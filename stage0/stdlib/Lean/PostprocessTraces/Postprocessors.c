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
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_PostprocessTraces_TraceTree_withChildren(lean_object*, lean_object*);
lean_object* l_Lean_PostprocessTraces_TraceTree_modifyData(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_PostprocessTraces_ofClass_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_PostprocessTraces_ofClass_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_PostprocessTraces_succeeded_spec__0___boxed(lean_object*, lean_object*);
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
lean_object* v_needle_19_; lean_object* v_table_20_; lean_object* v_stackPos_21_; lean_object* v_needlePos_22_; lean_object* v___x_24_; uint8_t v_isShared_25_; uint8_t v_isSharedCheck_75_; 
v_needle_19_ = lean_ctor_get(v_a_4_, 0);
v_table_20_ = lean_ctor_get(v_a_4_, 1);
v_stackPos_21_ = lean_ctor_get(v_a_4_, 2);
v_needlePos_22_ = lean_ctor_get(v_a_4_, 3);
v_isSharedCheck_75_ = !lean_is_exclusive(v_a_4_);
if (v_isSharedCheck_75_ == 0)
{
v___x_24_ = v_a_4_;
v_isShared_25_ = v_isSharedCheck_75_;
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
v_isShared_25_ = v_isSharedCheck_75_;
goto v_resetjp_23_;
}
v_resetjp_23_:
{
lean_object* v_str_26_; lean_object* v_startInclusive_27_; lean_object* v_endExclusive_28_; lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; 
v_str_26_ = lean_ctor_get(v_needle_19_, 0);
v_startInclusive_27_ = lean_ctor_get(v_needle_19_, 1);
v_endExclusive_28_ = lean_ctor_get(v_needle_19_, 2);
v___x_29_ = lean_nat_sub(v_stackPos_21_, v_needlePos_22_);
v___x_30_ = lean_nat_sub(v_endExclusive_28_, v_startInclusive_27_);
v___x_31_ = lean_nat_add(v___x_29_, v___x_30_);
v___x_32_ = lean_nat_dec_le(v___x_31_, v___x_3_);
lean_dec(v___x_31_);
if (v___x_32_ == 0)
{
lean_object* v___x_33_; lean_object* v___x_34_; uint8_t v___x_35_; 
lean_dec(v___x_30_);
lean_del_object(v___x_24_);
lean_dec(v_needlePos_22_);
lean_dec(v_stackPos_21_);
lean_dec_ref(v_table_20_);
lean_dec_ref(v_needle_19_);
v___x_33_ = lean_unsigned_to_nat(1u);
v___x_34_ = lean_nat_add(v___x_29_, v___x_33_);
lean_dec(v___x_29_);
v___x_35_ = lean_nat_dec_le(v___x_34_, v___x_3_);
lean_dec(v___x_34_);
if (v___x_35_ == 0)
{
lean_inc(v_b_5_);
return v_b_5_;
}
else
{
lean_object* v___x_36_; 
v___x_36_ = lean_box(3);
v_a_4_ = v___x_36_;
v_b_5_ = v___x_6_;
goto _start;
}
}
else
{
uint8_t v_stackByte_38_; lean_object* v___x_39_; uint8_t v_patByte_40_; uint8_t v___x_41_; 
lean_dec(v___x_29_);
lean_inc(v_stackPos_21_);
v_stackByte_38_ = lean_string_get_byte_fast(v_s_1_, v_stackPos_21_);
v___x_39_ = lean_nat_add(v_startInclusive_27_, v_needlePos_22_);
v_patByte_40_ = lean_string_get_byte_fast(v_str_26_, v___x_39_);
v___x_41_ = lean_uint8_dec_eq(v_stackByte_38_, v_patByte_40_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; uint8_t v_decide_43_; 
lean_dec(v___x_30_);
v___x_42_ = lean_unsigned_to_nat(0u);
v_decide_43_ = lean_nat_dec_eq(v_needlePos_22_, v___x_42_);
if (v_decide_43_ == 0)
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v_newNeedlePos_46_; uint8_t v___x_47_; 
v___x_44_ = lean_unsigned_to_nat(1u);
v___x_45_ = lean_nat_sub(v_needlePos_22_, v___x_44_);
lean_dec(v_needlePos_22_);
v_newNeedlePos_46_ = lean_array_fget_borrowed(v_table_20_, v___x_45_);
lean_dec(v___x_45_);
v___x_47_ = lean_nat_dec_eq(v_newNeedlePos_46_, v___x_42_);
if (v___x_47_ == 0)
{
lean_object* v___x_49_; 
lean_inc(v_newNeedlePos_46_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 3, v_newNeedlePos_46_);
v___x_49_ = v___x_24_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_51_; 
v_reuseFailAlloc_51_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_51_, 0, v_needle_19_);
lean_ctor_set(v_reuseFailAlloc_51_, 1, v_table_20_);
lean_ctor_set(v_reuseFailAlloc_51_, 2, v_stackPos_21_);
lean_ctor_set(v_reuseFailAlloc_51_, 3, v_newNeedlePos_46_);
v___x_49_ = v_reuseFailAlloc_51_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
v_a_4_ = v___x_49_;
v_b_5_ = v___x_6_;
goto _start;
}
}
else
{
lean_object* v_nextStackPos_52_; lean_object* v___x_54_; 
v_nextStackPos_52_ = l_String_Slice_posGE___redArg(v___x_2_, v_stackPos_21_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 3, v___x_42_);
lean_ctor_set(v___x_24_, 2, v_nextStackPos_52_);
v___x_54_ = v___x_24_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_56_; 
v_reuseFailAlloc_56_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_56_, 0, v_needle_19_);
lean_ctor_set(v_reuseFailAlloc_56_, 1, v_table_20_);
lean_ctor_set(v_reuseFailAlloc_56_, 2, v_nextStackPos_52_);
lean_ctor_set(v_reuseFailAlloc_56_, 3, v___x_42_);
v___x_54_ = v_reuseFailAlloc_56_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
v_a_4_ = v___x_54_;
v_b_5_ = v___x_6_;
goto _start;
}
}
}
else
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v_nextStackPos_59_; lean_object* v___x_61_; 
lean_dec(v_needlePos_22_);
v___x_57_ = lean_unsigned_to_nat(1u);
v___x_58_ = lean_nat_add(v_stackPos_21_, v___x_57_);
lean_dec(v_stackPos_21_);
v_nextStackPos_59_ = l_String_Slice_posGE___redArg(v___x_2_, v___x_58_);
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 3, v___x_42_);
lean_ctor_set(v___x_24_, 2, v_nextStackPos_59_);
v___x_61_ = v___x_24_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_needle_19_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v_table_20_);
lean_ctor_set(v_reuseFailAlloc_63_, 2, v_nextStackPos_59_);
lean_ctor_set(v_reuseFailAlloc_63_, 3, v___x_42_);
v___x_61_ = v_reuseFailAlloc_63_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
v_a_4_ = v___x_61_;
v_b_5_ = v___x_6_;
goto _start;
}
}
}
else
{
lean_object* v___x_64_; lean_object* v_nextStackPos_65_; lean_object* v_nextNeedlePos_66_; uint8_t v_decide_67_; 
v___x_64_ = lean_unsigned_to_nat(1u);
v_nextStackPos_65_ = lean_nat_add(v_stackPos_21_, v___x_64_);
lean_dec(v_stackPos_21_);
v_nextNeedlePos_66_ = lean_nat_add(v_needlePos_22_, v___x_64_);
lean_dec(v_needlePos_22_);
v_decide_67_ = lean_nat_dec_eq(v_nextNeedlePos_66_, v___x_30_);
lean_dec(v___x_30_);
if (v_decide_67_ == 0)
{
lean_object* v___x_69_; 
if (v_isShared_25_ == 0)
{
lean_ctor_set(v___x_24_, 3, v_nextNeedlePos_66_);
lean_ctor_set(v___x_24_, 2, v_nextStackPos_65_);
v___x_69_ = v___x_24_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_needle_19_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v_table_20_);
lean_ctor_set(v_reuseFailAlloc_71_, 2, v_nextStackPos_65_);
lean_ctor_set(v_reuseFailAlloc_71_, 3, v_nextNeedlePos_66_);
v___x_69_ = v_reuseFailAlloc_71_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
v_a_4_ = v___x_69_;
goto _start;
}
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
lean_del_object(v___x_24_);
lean_dec_ref(v_table_20_);
lean_dec_ref(v_needle_19_);
v___x_72_ = lean_nat_sub(v_nextStackPos_65_, v_nextNeedlePos_66_);
lean_dec(v_nextNeedlePos_66_);
lean_dec(v_nextStackPos_65_);
v___x_73_ = l_String_Slice_pos_x21(v___x_2_, v___x_72_);
lean_dec(v___x_72_);
v___x_74_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
return v___x_74_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_spec__0___redArg___boxed(lean_object* v_s_76_, lean_object* v___x_77_, lean_object* v___x_78_, lean_object* v_a_79_, lean_object* v_b_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_spec__0___redArg(v_s_76_, v___x_77_, v___x_78_, v_a_79_, v_b_80_);
lean_dec(v_b_80_);
lean_dec(v___x_78_);
lean_dec_ref(v___x_77_);
lean_dec_ref(v_s_76_);
return v_res_81_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr(lean_object* v_s_84_, lean_object* v_pat_85_){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___y_90_; lean_object* v___x_95_; uint8_t v___x_96_; 
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = lean_string_utf8_byte_size(v_s_84_);
lean_inc_ref(v_s_84_);
v___x_88_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_88_, 0, v_s_84_);
lean_ctor_set(v___x_88_, 1, v___x_86_);
lean_ctor_set(v___x_88_, 2, v___x_87_);
v___x_95_ = lean_string_utf8_byte_size(v_pat_85_);
v___x_96_ = lean_nat_dec_eq(v___x_95_, v___x_86_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_97_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_97_, 0, v_pat_85_);
lean_ctor_set(v___x_97_, 1, v___x_86_);
lean_ctor_set(v___x_97_, 2, v___x_95_);
v___x_98_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v___x_97_);
v___x_99_ = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(v___x_99_, 0, v___x_97_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
lean_ctor_set(v___x_99_, 2, v___x_86_);
lean_ctor_set(v___x_99_, 3, v___x_86_);
v___y_90_ = v___x_99_;
goto v___jp_89_;
}
else
{
lean_object* v___x_100_; 
lean_dec_ref(v_pat_85_);
v___x_100_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr___closed__0));
v___y_90_ = v___x_100_;
goto v___jp_89_;
}
v___jp_89_:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_box(0);
v___x_92_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_spec__0___redArg(v_s_84_, v___x_88_, v___x_87_, v___y_90_, v___x_91_);
lean_dec_ref_known(v___x_88_, 3);
lean_dec_ref(v_s_84_);
if (lean_obj_tag(v___x_92_) == 0)
{
uint8_t v___x_93_; 
v___x_93_ = 0;
return v___x_93_;
}
else
{
uint8_t v___x_94_; 
lean_dec_ref_known(v___x_92_, 1);
v___x_94_ = 1;
return v___x_94_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr___boxed(lean_object* v_s_101_, lean_object* v_pat_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr(v_s_101_, v_pat_102_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_spec__0(lean_object* v_s_105_, lean_object* v___x_106_, lean_object* v___x_107_, lean_object* v_inst_108_, lean_object* v_R_109_, lean_object* v_a_110_, lean_object* v_b_111_, lean_object* v_c_112_){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_spec__0___redArg(v_s_105_, v___x_106_, v___x_107_, v_a_110_, v_b_111_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_spec__0___boxed(lean_object* v_s_114_, lean_object* v___x_115_, lean_object* v___x_116_, lean_object* v_inst_117_, lean_object* v_R_118_, lean_object* v_a_119_, lean_object* v_b_120_, lean_object* v_c_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_spec__0(v_s_114_, v___x_115_, v___x_116_, v_inst_117_, v_R_118_, v_a_119_, v_b_120_, v_c_121_);
lean_dec(v_b_120_);
lean_dec(v___x_116_);
lean_dec_ref(v___x_115_);
lean_dec_ref(v_s_114_);
return v_res_122_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_PostprocessTraces_ofClass_spec__0(lean_object* v_x_123_, lean_object* v_x_124_){
_start:
{
if (lean_obj_tag(v_x_123_) == 0)
{
if (lean_obj_tag(v_x_124_) == 0)
{
uint8_t v___x_125_; 
v___x_125_ = 1;
return v___x_125_;
}
else
{
uint8_t v___x_126_; 
v___x_126_ = 0;
return v___x_126_;
}
}
else
{
if (lean_obj_tag(v_x_124_) == 0)
{
uint8_t v___x_127_; 
v___x_127_ = 0;
return v___x_127_;
}
else
{
lean_object* v_val_128_; lean_object* v_val_129_; uint8_t v___x_130_; 
v_val_128_ = lean_ctor_get(v_x_123_, 0);
v_val_129_ = lean_ctor_get(v_x_124_, 0);
v___x_130_ = lean_name_eq(v_val_128_, v_val_129_);
return v___x_130_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_PostprocessTraces_ofClass_spec__0___boxed(lean_object* v_x_131_, lean_object* v_x_132_){
_start:
{
uint8_t v_res_133_; lean_object* v_r_134_; 
v_res_133_ = l_instBEqOption_beq___at___00Lean_PostprocessTraces_ofClass_spec__0(v_x_131_, v_x_132_);
lean_dec(v_x_132_);
lean_dec(v_x_131_);
v_r_134_ = lean_box(v_res_133_);
return v_r_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass___redArg(lean_object* v_cls_135_, lean_object* v_t_136_){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; uint8_t v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_138_ = l_Lean_PostprocessTraces_TraceTree_cls_x3f(v_t_136_);
v___x_139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_139_, 0, v_cls_135_);
v___x_140_ = l_instBEqOption_beq___at___00Lean_PostprocessTraces_ofClass_spec__0(v___x_138_, v___x_139_);
lean_dec_ref_known(v___x_139_, 1);
lean_dec(v___x_138_);
v___x_141_ = lean_box(v___x_140_);
v___x_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass___redArg___boxed(lean_object* v_cls_143_, lean_object* v_t_144_, lean_object* v_a_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_PostprocessTraces_ofClass___redArg(v_cls_143_, v_t_144_);
lean_dec_ref(v_t_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass(lean_object* v_cls_147_, lean_object* v_t_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_PostprocessTraces_ofClass___redArg(v_cls_147_, v_t_148_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass___boxed(lean_object* v_cls_153_, lean_object* v_t_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_PostprocessTraces_ofClass(v_cls_153_, v_t_154_, v_a_155_, v_a_156_);
lean_dec(v_a_156_);
lean_dec_ref(v_a_155_);
lean_dec_ref(v_t_154_);
return v_res_158_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString___redArg(lean_object* v_pat_159_, lean_object* v_t_160_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_PostprocessTraces_TraceTree_cls_x3f(v_t_160_);
if (lean_obj_tag(v___x_167_) == 0)
{
goto v___jp_162_;
}
else
{
lean_object* v_val_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_179_; 
v_val_168_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_179_ == 0)
{
v___x_170_ = v___x_167_;
v_isShared_171_ = v_isSharedCheck_179_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_val_168_);
lean_dec(v___x_167_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_179_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
uint8_t v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_172_ = 1;
v___x_173_ = l_Lean_Name_toString(v_val_168_, v___x_172_);
lean_inc_ref(v_pat_159_);
v___x_174_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr(v___x_173_, v_pat_159_);
if (v___x_174_ == 0)
{
lean_del_object(v___x_170_);
goto v___jp_162_;
}
else
{
lean_object* v___x_175_; lean_object* v___x_177_; 
lean_dec_ref(v_t_160_);
lean_dec_ref(v_pat_159_);
v___x_175_ = lean_box(v___x_174_);
if (v_isShared_171_ == 0)
{
lean_ctor_set_tag(v___x_170_, 0);
lean_ctor_set(v___x_170_, 0, v___x_175_);
v___x_177_ = v___x_170_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
v___jp_162_:
{
lean_object* v___x_163_; uint8_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_163_ = l_Lean_PostprocessTraces_TraceTree_headText(v_t_160_);
v___x_164_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr(v___x_163_, v_pat_159_);
v___x_165_ = lean_box(v___x_164_);
v___x_166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString___redArg___boxed(lean_object* v_pat_180_, lean_object* v_t_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_PostprocessTraces_containsString___redArg(v_pat_180_, v_t_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString(lean_object* v_pat_184_, lean_object* v_t_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Lean_PostprocessTraces_containsString___redArg(v_pat_184_, v_t_185_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString___boxed(lean_object* v_pat_190_, lean_object* v_t_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Lean_PostprocessTraces_containsString(v_pat_190_, v_t_191_, v_a_192_, v_a_193_);
lean_dec(v_a_193_);
lean_dec_ref(v_a_192_);
return v_res_195_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(lean_object* v_x_196_, lean_object* v_x_197_){
_start:
{
if (lean_obj_tag(v_x_196_) == 0)
{
if (lean_obj_tag(v_x_197_) == 0)
{
uint8_t v___x_198_; 
v___x_198_ = 1;
return v___x_198_;
}
else
{
uint8_t v___x_199_; 
v___x_199_ = 0;
return v___x_199_;
}
}
else
{
if (lean_obj_tag(v_x_197_) == 0)
{
uint8_t v___x_200_; 
v___x_200_ = 0;
return v___x_200_;
}
else
{
lean_object* v_val_201_; lean_object* v_val_202_; uint8_t v___x_203_; uint8_t v___x_204_; uint8_t v___x_205_; 
v_val_201_ = lean_ctor_get(v_x_196_, 0);
v_val_202_ = lean_ctor_get(v_x_197_, 0);
v___x_203_ = lean_unbox(v_val_201_);
v___x_204_ = lean_unbox(v_val_202_);
v___x_205_ = l_Lean_instBEqTraceResult_beq(v___x_203_, v___x_204_);
return v___x_205_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_PostprocessTraces_succeeded_spec__0___boxed(lean_object* v_x_206_, lean_object* v_x_207_){
_start:
{
uint8_t v_res_208_; lean_object* v_r_209_; 
v_res_208_ = l_instBEqOption_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v_x_206_, v_x_207_);
lean_dec(v_x_207_);
lean_dec(v_x_206_);
v_r_209_ = lean_box(v_res_208_);
return v_r_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_succeeded___redArg(lean_object* v_t_213_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_215_ = l_Lean_PostprocessTraces_TraceTree_result_x3f(v_t_213_);
v___x_216_ = ((lean_object*)(l_Lean_PostprocessTraces_succeeded___redArg___closed__0));
v___x_217_ = l_instBEqOption_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v___x_215_, v___x_216_);
lean_dec(v___x_215_);
v___x_218_ = lean_box(v___x_217_);
v___x_219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_succeeded___redArg___boxed(lean_object* v_t_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_PostprocessTraces_succeeded___redArg(v_t_220_);
lean_dec_ref(v_t_220_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_succeeded(lean_object* v_t_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_PostprocessTraces_succeeded___redArg(v_t_223_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_succeeded___boxed(lean_object* v_t_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_PostprocessTraces_succeeded(v_t_228_, v_a_229_, v_a_230_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec_ref(v_t_228_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_failed___redArg(lean_object* v_t_236_){
_start:
{
lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_238_ = l_Lean_PostprocessTraces_TraceTree_result_x3f(v_t_236_);
v___x_239_ = ((lean_object*)(l_Lean_PostprocessTraces_failed___redArg___closed__0));
v___x_240_ = l_instBEqOption_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v___x_238_, v___x_239_);
lean_dec(v___x_238_);
v___x_241_ = lean_box(v___x_240_);
v___x_242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_failed___redArg___boxed(lean_object* v_t_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_PostprocessTraces_failed___redArg(v_t_243_);
lean_dec_ref(v_t_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_failed(lean_object* v_t_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_PostprocessTraces_failed___redArg(v_t_246_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_failed___boxed(lean_object* v_t_251_, lean_object* v_a_252_, lean_object* v_a_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_PostprocessTraces_failed(v_t_251_, v_a_252_, v_a_253_);
lean_dec(v_a_253_);
lean_dec_ref(v_a_252_);
lean_dec_ref(v_t_251_);
return v_res_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_errored___redArg(lean_object* v_t_259_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_261_ = l_Lean_PostprocessTraces_TraceTree_result_x3f(v_t_259_);
v___x_262_ = ((lean_object*)(l_Lean_PostprocessTraces_errored___redArg___closed__0));
v___x_263_ = l_instBEqOption_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v___x_261_, v___x_262_);
lean_dec(v___x_261_);
v___x_264_ = lean_box(v___x_263_);
v___x_265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_errored___redArg___boxed(lean_object* v_t_266_, lean_object* v_a_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_PostprocessTraces_errored___redArg(v_t_266_);
lean_dec_ref(v_t_266_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_errored(lean_object* v_t_269_, lean_object* v_a_270_, lean_object* v_a_271_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Lean_PostprocessTraces_errored___redArg(v_t_269_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_errored___boxed(lean_object* v_t_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_PostprocessTraces_errored(v_t_274_, v_a_275_, v_a_276_);
lean_dec(v_a_276_);
lean_dec_ref(v_a_275_);
lean_dec_ref(v_t_274_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_unsuccessful___redArg(lean_object* v_t_279_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_281_ = l_Lean_PostprocessTraces_TraceTree_result_x3f(v_t_279_);
v___x_282_ = ((lean_object*)(l_Lean_PostprocessTraces_failed___redArg___closed__0));
v___x_283_ = l_instBEqOption_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v___x_281_, v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_284_ = ((lean_object*)(l_Lean_PostprocessTraces_errored___redArg___closed__0));
v___x_285_ = l_instBEqOption_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v___x_281_, v___x_284_);
lean_dec(v___x_281_);
v___x_286_ = lean_box(v___x_285_);
v___x_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
return v___x_287_;
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; 
lean_dec(v___x_281_);
v___x_288_ = lean_box(v___x_283_);
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_unsuccessful___redArg___boxed(lean_object* v_t_290_, lean_object* v_a_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_PostprocessTraces_unsuccessful___redArg(v_t_290_);
lean_dec_ref(v_t_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_unsuccessful(lean_object* v_t_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_PostprocessTraces_unsuccessful___redArg(v_t_293_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_unsuccessful___boxed(lean_object* v_t_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_PostprocessTraces_unsuccessful(v_t_298_, v_a_299_, v_a_300_);
lean_dec(v_a_300_);
lean_dec_ref(v_a_299_);
lean_dec_ref(v_t_298_);
return v_res_302_;
}
}
static double _init_l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0(void){
_start:
{
lean_object* v___x_303_; double v___x_304_; 
v___x_303_ = lean_unsigned_to_nat(1000u);
v___x_304_ = lean_float_of_nat(v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minTimeMs___redArg(double v_ms_305_, lean_object* v_t_306_){
_start:
{
double v___x_308_; double v___x_309_; double v___x_310_; uint8_t v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_308_ = l_Lean_PostprocessTraces_TraceTree_elapsed(v_t_306_);
v___x_309_ = lean_float_once(&l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0, &l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0_once, _init_l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0);
v___x_310_ = lean_float_mul(v___x_308_, v___x_309_);
v___x_311_ = lean_float_decLe(v_ms_305_, v___x_310_);
v___x_312_ = lean_box(v___x_311_);
v___x_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minTimeMs___redArg___boxed(lean_object* v_ms_314_, lean_object* v_t_315_, lean_object* v_a_316_){
_start:
{
double v_ms_boxed_317_; lean_object* v_res_318_; 
v_ms_boxed_317_ = lean_unbox_float(v_ms_314_);
lean_dec_ref(v_ms_314_);
v_res_318_ = l_Lean_PostprocessTraces_minTimeMs___redArg(v_ms_boxed_317_, v_t_315_);
lean_dec_ref(v_t_315_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minTimeMs(double v_ms_319_, lean_object* v_t_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_PostprocessTraces_minTimeMs___redArg(v_ms_319_, v_t_320_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minTimeMs___boxed(lean_object* v_ms_325_, lean_object* v_t_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
double v_ms_boxed_330_; lean_object* v_res_331_; 
v_ms_boxed_330_ = lean_unbox_float(v_ms_325_);
lean_dec_ref(v_ms_325_);
v_res_331_ = l_Lean_PostprocessTraces_minTimeMs(v_ms_boxed_330_, v_t_326_, v_a_327_, v_a_328_);
lean_dec(v_a_328_);
lean_dec_ref(v_a_327_);
lean_dec_ref(v_t_326_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minSelfTimeMs___redArg(double v_ms_332_, lean_object* v_t_333_){
_start:
{
double v___x_335_; double v___x_336_; double v___x_337_; uint8_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_335_ = l_Lean_PostprocessTraces_TraceTree_selfElapsed(v_t_333_);
v___x_336_ = lean_float_once(&l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0, &l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0_once, _init_l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0);
v___x_337_ = lean_float_mul(v___x_335_, v___x_336_);
v___x_338_ = lean_float_decLe(v_ms_332_, v___x_337_);
v___x_339_ = lean_box(v___x_338_);
v___x_340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minSelfTimeMs___redArg___boxed(lean_object* v_ms_341_, lean_object* v_t_342_, lean_object* v_a_343_){
_start:
{
double v_ms_boxed_344_; lean_object* v_res_345_; 
v_ms_boxed_344_ = lean_unbox_float(v_ms_341_);
lean_dec_ref(v_ms_341_);
v_res_345_ = l_Lean_PostprocessTraces_minSelfTimeMs___redArg(v_ms_boxed_344_, v_t_342_);
lean_dec_ref(v_t_342_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minSelfTimeMs(double v_ms_346_, lean_object* v_t_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_PostprocessTraces_minSelfTimeMs___redArg(v_ms_346_, v_t_347_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minSelfTimeMs___boxed(lean_object* v_ms_352_, lean_object* v_t_353_, lean_object* v_a_354_, lean_object* v_a_355_, lean_object* v_a_356_){
_start:
{
double v_ms_boxed_357_; lean_object* v_res_358_; 
v_ms_boxed_357_ = lean_unbox_float(v_ms_352_);
lean_dec_ref(v_ms_352_);
v_res_358_ = l_Lean_PostprocessTraces_minSelfTimeMs(v_ms_boxed_357_, v_t_353_, v_a_354_, v_a_355_);
lean_dec(v_a_355_);
lean_dec_ref(v_a_354_);
lean_dec_ref(v_t_353_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0_spec__0(lean_object* v_p_359_, lean_object* v_as_360_, size_t v_i_361_, size_t v_stop_362_, lean_object* v_b_363_, lean_object* v___y_364_, lean_object* v___y_365_){
_start:
{
lean_object* v_a_368_; uint8_t v___x_372_; 
v___x_372_ = lean_usize_dec_eq(v_i_361_, v_stop_362_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = lean_array_uget_borrowed(v_as_360_, v_i_361_);
lean_inc(v___x_373_);
lean_inc_ref(v_p_359_);
v___x_374_ = l_Lean_PostprocessTraces_TraceTree_filterSubtrees(v_p_359_, v___x_373_, v___y_364_, v___y_365_);
if (lean_obj_tag(v___x_374_) == 0)
{
lean_object* v_a_375_; 
v_a_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_a_375_);
lean_dec_ref_known(v___x_374_, 1);
if (lean_obj_tag(v_a_375_) == 0)
{
v_a_368_ = v_b_363_;
goto v___jp_367_;
}
else
{
lean_object* v_val_376_; lean_object* v___x_377_; 
v_val_376_ = lean_ctor_get(v_a_375_, 0);
lean_inc(v_val_376_);
lean_dec_ref_known(v_a_375_, 1);
v___x_377_ = lean_array_push(v_b_363_, v_val_376_);
v_a_368_ = v___x_377_;
goto v___jp_367_;
}
}
else
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_385_; 
lean_dec_ref(v_b_363_);
lean_dec_ref(v_p_359_);
v_a_378_ = lean_ctor_get(v___x_374_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_374_);
if (v_isSharedCheck_385_ == 0)
{
v___x_380_ = v___x_374_;
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_374_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_385_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v___x_383_; 
if (v_isShared_381_ == 0)
{
v___x_383_ = v___x_380_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_a_378_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
else
{
lean_object* v___x_386_; 
lean_dec_ref(v_p_359_);
v___x_386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_386_, 0, v_b_363_);
return v___x_386_;
}
v___jp_367_:
{
size_t v___x_369_; size_t v___x_370_; 
v___x_369_ = ((size_t)1ULL);
v___x_370_ = lean_usize_add(v_i_361_, v___x_369_);
v_i_361_ = v___x_370_;
v_b_363_ = v_a_368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0_spec__0___boxed(lean_object* v_p_387_, lean_object* v_as_388_, lean_object* v_i_389_, lean_object* v_stop_390_, lean_object* v_b_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
size_t v_i_boxed_395_; size_t v_stop_boxed_396_; lean_object* v_res_397_; 
v_i_boxed_395_ = lean_unbox_usize(v_i_389_);
lean_dec(v_i_389_);
v_stop_boxed_396_ = lean_unbox_usize(v_stop_390_);
lean_dec(v_stop_390_);
v_res_397_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0_spec__0(v_p_387_, v_as_388_, v_i_boxed_395_, v_stop_boxed_396_, v_b_391_, v___y_392_, v___y_393_);
lean_dec(v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec_ref(v_as_388_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0(lean_object* v_p_400_, lean_object* v_as_401_, lean_object* v_start_402_, lean_object* v_stop_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0___closed__0));
v___x_408_ = lean_nat_dec_lt(v_start_402_, v_stop_403_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; 
lean_dec_ref(v_p_400_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_407_);
return v___x_409_;
}
else
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_array_get_size(v_as_401_);
v___x_411_ = lean_nat_dec_le(v_stop_403_, v___x_410_);
if (v___x_411_ == 0)
{
uint8_t v___x_412_; 
v___x_412_ = lean_nat_dec_lt(v_start_402_, v___x_410_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; 
lean_dec_ref(v_p_400_);
v___x_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_413_, 0, v___x_407_);
return v___x_413_;
}
else
{
size_t v___x_414_; size_t v___x_415_; lean_object* v___x_416_; 
v___x_414_ = lean_usize_of_nat(v_start_402_);
v___x_415_ = lean_usize_of_nat(v___x_410_);
v___x_416_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0_spec__0(v_p_400_, v_as_401_, v___x_414_, v___x_415_, v___x_407_, v___y_404_, v___y_405_);
return v___x_416_;
}
}
else
{
size_t v___x_417_; size_t v___x_418_; lean_object* v___x_419_; 
v___x_417_ = lean_usize_of_nat(v_start_402_);
v___x_418_ = lean_usize_of_nat(v_stop_403_);
v___x_419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0_spec__0(v_p_400_, v_as_401_, v___x_417_, v___x_418_, v___x_407_, v___y_404_, v___y_405_);
return v___x_419_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0___boxed(lean_object* v_p_420_, lean_object* v_as_421_, lean_object* v_start_422_, lean_object* v_stop_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0(v_p_420_, v_as_421_, v_start_422_, v_stop_423_, v___y_424_, v___y_425_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v_stop_423_);
lean_dec(v_start_422_);
lean_dec_ref(v_as_421_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_filterSubtrees(lean_object* v_p_428_, lean_object* v_roots_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_433_ = lean_unsigned_to_nat(0u);
v___x_434_ = lean_array_get_size(v_roots_429_);
v___x_435_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0(v_p_428_, v_roots_429_, v___x_433_, v___x_434_, v_a_430_, v_a_431_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_filterSubtrees___boxed(lean_object* v_p_436_, lean_object* v_roots_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_PostprocessTraces_filterSubtrees(v_p_436_, v_roots_437_, v_a_438_, v_a_439_);
lean_dec(v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec_ref(v_roots_437_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_hoist_spec__0(lean_object* v_p_442_, lean_object* v_as_443_, size_t v_i_444_, size_t v_stop_445_, lean_object* v_b_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
uint8_t v___x_450_; 
v___x_450_ = lean_usize_dec_eq(v_i_444_, v_stop_445_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_451_ = lean_array_uget_borrowed(v_as_443_, v_i_444_);
lean_inc(v___x_451_);
lean_inc_ref(v_p_442_);
v___x_452_ = l_Lean_PostprocessTraces_TraceTree_collectSubtrees(v_p_442_, v___x_451_, v_b_446_, v___y_447_, v___y_448_);
if (lean_obj_tag(v___x_452_) == 0)
{
lean_object* v_a_453_; size_t v___x_454_; size_t v___x_455_; 
v_a_453_ = lean_ctor_get(v___x_452_, 0);
lean_inc(v_a_453_);
lean_dec_ref_known(v___x_452_, 1);
v___x_454_ = ((size_t)1ULL);
v___x_455_ = lean_usize_add(v_i_444_, v___x_454_);
v_i_444_ = v___x_455_;
v_b_446_ = v_a_453_;
goto _start;
}
else
{
lean_dec_ref(v_p_442_);
return v___x_452_;
}
}
else
{
lean_object* v___x_457_; 
lean_dec_ref(v_p_442_);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v_b_446_);
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_hoist_spec__0___boxed(lean_object* v_p_458_, lean_object* v_as_459_, lean_object* v_i_460_, lean_object* v_stop_461_, lean_object* v_b_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
size_t v_i_boxed_466_; size_t v_stop_boxed_467_; lean_object* v_res_468_; 
v_i_boxed_466_ = lean_unbox_usize(v_i_460_);
lean_dec(v_i_460_);
v_stop_boxed_467_ = lean_unbox_usize(v_stop_461_);
lean_dec(v_stop_461_);
v_res_468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_hoist_spec__0(v_p_458_, v_as_459_, v_i_boxed_466_, v_stop_boxed_467_, v_b_462_, v___y_463_, v___y_464_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec_ref(v_as_459_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_hoist(lean_object* v_p_469_, lean_object* v_roots_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0___closed__0));
v___x_476_ = lean_array_get_size(v_roots_470_);
v___x_477_ = lean_nat_dec_lt(v___x_474_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; 
lean_dec_ref(v_p_469_);
v___x_478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_478_, 0, v___x_475_);
return v___x_478_;
}
else
{
size_t v___x_479_; size_t v___x_480_; lean_object* v___x_481_; 
v___x_479_ = ((size_t)0ULL);
v___x_480_ = lean_usize_of_nat(v___x_476_);
v___x_481_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_hoist_spec__0(v_p_469_, v_roots_470_, v___x_479_, v___x_480_, v___x_475_, v_a_471_, v_a_472_);
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_hoist___boxed(lean_object* v_p_482_, lean_object* v_roots_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_PostprocessTraces_hoist(v_p_482_, v_roots_483_, v_a_484_, v_a_485_);
lean_dec(v_a_485_);
lean_dec_ref(v_a_484_);
lean_dec_ref(v_roots_483_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go___lam__0(uint8_t v_a_488_, lean_object* v_x_489_){
_start:
{
lean_object* v_cls_490_; lean_object* v_result_x3f_491_; double v_startTime_492_; double v_stopTime_493_; lean_object* v_tag_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_501_; 
v_cls_490_ = lean_ctor_get(v_x_489_, 0);
v_result_x3f_491_ = lean_ctor_get(v_x_489_, 1);
v_startTime_492_ = lean_ctor_get_float(v_x_489_, sizeof(void*)*3);
v_stopTime_493_ = lean_ctor_get_float(v_x_489_, sizeof(void*)*3 + 8);
v_tag_494_ = lean_ctor_get(v_x_489_, 2);
v_isSharedCheck_501_ = !lean_is_exclusive(v_x_489_);
if (v_isSharedCheck_501_ == 0)
{
v___x_496_ = v_x_489_;
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_tag_494_);
lean_inc(v_result_x3f_491_);
lean_inc(v_cls_490_);
lean_dec(v_x_489_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_501_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_499_; 
if (v_isShared_497_ == 0)
{
v___x_499_ = v___x_496_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_cls_490_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_result_x3f_491_);
lean_ctor_set(v_reuseFailAlloc_500_, 2, v_tag_494_);
lean_ctor_set_float(v_reuseFailAlloc_500_, sizeof(void*)*3, v_startTime_492_);
lean_ctor_set_float(v_reuseFailAlloc_500_, sizeof(void*)*3 + 8, v_stopTime_493_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_ctor_set_uint8(v___x_499_, sizeof(void*)*3 + 16, v_a_488_);
return v___x_499_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go___lam__0___boxed(lean_object* v_a_502_, lean_object* v_x_503_){
_start:
{
uint8_t v_a_905__boxed_504_; lean_object* v_res_505_; 
v_a_905__boxed_504_ = lean_unbox(v_a_502_);
v_res_505_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go___lam__0(v_a_905__boxed_504_, v_x_503_);
return v_res_505_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__2(lean_object* v_as_506_, size_t v_i_507_, size_t v_stop_508_){
_start:
{
uint8_t v___x_509_; 
v___x_509_ = lean_usize_dec_eq(v_i_507_, v_stop_508_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; lean_object* v_snd_511_; uint8_t v___x_512_; 
v___x_510_ = lean_array_uget_borrowed(v_as_506_, v_i_507_);
v_snd_511_ = lean_ctor_get(v___x_510_, 1);
v___x_512_ = lean_unbox(v_snd_511_);
if (v___x_512_ == 0)
{
size_t v___x_513_; size_t v___x_514_; 
v___x_513_ = ((size_t)1ULL);
v___x_514_ = lean_usize_add(v_i_507_, v___x_513_);
v_i_507_ = v___x_514_;
goto _start;
}
else
{
uint8_t v___x_516_; 
v___x_516_ = 1;
return v___x_516_;
}
}
else
{
uint8_t v___x_517_; 
v___x_517_ = 0;
return v___x_517_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__2___boxed(lean_object* v_as_518_, lean_object* v_i_519_, lean_object* v_stop_520_){
_start:
{
size_t v_i_boxed_521_; size_t v_stop_boxed_522_; uint8_t v_res_523_; lean_object* v_r_524_; 
v_i_boxed_521_ = lean_unbox_usize(v_i_519_);
lean_dec(v_i_519_);
v_stop_boxed_522_ = lean_unbox_usize(v_stop_520_);
lean_dec(v_stop_520_);
v_res_523_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__2(v_as_518_, v_i_boxed_521_, v_stop_boxed_522_);
lean_dec_ref(v_as_518_);
v_r_524_ = lean_box(v_res_523_);
return v_r_524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__1(size_t v_sz_525_, size_t v_i_526_, lean_object* v_bs_527_){
_start:
{
uint8_t v___x_528_; 
v___x_528_ = lean_usize_dec_lt(v_i_526_, v_sz_525_);
if (v___x_528_ == 0)
{
return v_bs_527_;
}
else
{
lean_object* v_v_529_; lean_object* v_fst_530_; lean_object* v___x_531_; lean_object* v_bs_x27_532_; size_t v___x_533_; size_t v___x_534_; lean_object* v___x_535_; 
v_v_529_ = lean_array_uget_borrowed(v_bs_527_, v_i_526_);
v_fst_530_ = lean_ctor_get(v_v_529_, 0);
lean_inc(v_fst_530_);
v___x_531_ = lean_unsigned_to_nat(0u);
v_bs_x27_532_ = lean_array_uset(v_bs_527_, v_i_526_, v___x_531_);
v___x_533_ = ((size_t)1ULL);
v___x_534_ = lean_usize_add(v_i_526_, v___x_533_);
v___x_535_ = lean_array_uset(v_bs_x27_532_, v_i_526_, v_fst_530_);
v_i_526_ = v___x_534_;
v_bs_527_ = v___x_535_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__1___boxed(lean_object* v_sz_537_, lean_object* v_i_538_, lean_object* v_bs_539_){
_start:
{
size_t v_sz_boxed_540_; size_t v_i_boxed_541_; lean_object* v_res_542_; 
v_sz_boxed_540_ = lean_unbox_usize(v_sz_537_);
lean_dec(v_sz_537_);
v_i_boxed_541_ = lean_unbox_usize(v_i_538_);
lean_dec(v_i_538_);
v_res_542_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__1(v_sz_boxed_540_, v_i_boxed_541_, v_bs_539_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go(lean_object* v_p_543_, lean_object* v_t_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v___x_548_; 
lean_inc_ref(v_p_543_);
lean_inc(v_a_546_);
lean_inc_ref(v_a_545_);
lean_inc_ref(v_t_544_);
v___x_548_ = lean_apply_4(v_p_543_, v_t_544_, v_a_545_, v_a_546_, lean_box(0));
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_595_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_595_ == 0)
{
v___x_551_ = v___x_548_;
v_isShared_552_ = v_isSharedCheck_595_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_548_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_595_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
uint8_t v___x_553_; 
v___x_553_ = lean_unbox(v_a_549_);
if (v___x_553_ == 0)
{
lean_object* v___f_554_; lean_object* v___x_555_; size_t v_sz_556_; size_t v___x_557_; lean_object* v___x_558_; 
lean_del_object(v___x_551_);
v___f_554_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go___lam__0___boxed), 2, 1);
lean_closure_set(v___f_554_, 0, v_a_549_);
v___x_555_ = l_Lean_PostprocessTraces_TraceTree_children(v_t_544_);
v_sz_556_ = lean_array_size(v___x_555_);
v___x_557_ = ((size_t)0ULL);
v___x_558_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__0(v_p_543_, v_sz_556_, v___x_557_, v___x_555_, v_a_545_, v_a_546_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_582_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_582_ == 0)
{
v___x_561_ = v___x_558_;
v_isShared_562_ = v_isSharedCheck_582_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_558_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_582_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
uint8_t v___y_564_; lean_object* v___y_565_; uint8_t v___y_572_; lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = lean_array_get_size(v_a_559_);
v___x_579_ = lean_nat_dec_lt(v___x_577_, v___x_578_);
if (v___x_579_ == 0)
{
v___y_572_ = v___x_579_;
goto v___jp_571_;
}
else
{
if (v___x_579_ == 0)
{
v___y_572_ = v___x_579_;
goto v___jp_571_;
}
else
{
size_t v___x_580_; uint8_t v___x_581_; 
v___x_580_ = lean_usize_of_nat(v___x_578_);
v___x_581_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__2(v_a_559_, v___x_557_, v___x_580_);
v___y_572_ = v___x_581_;
goto v___jp_571_;
}
}
v___jp_563_:
{
lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_566_ = lean_box(v___y_564_);
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v___y_565_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_567_);
v___x_569_ = v___x_561_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
v___jp_571_:
{
size_t v_sz_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_sz_573_ = lean_array_size(v_a_559_);
v___x_574_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__1(v_sz_573_, v___x_557_, v_a_559_);
v___x_575_ = l_Lean_PostprocessTraces_TraceTree_withChildren(v_t_544_, v___x_574_);
if (v___y_572_ == 0)
{
lean_dec_ref(v___f_554_);
v___y_564_ = v___y_572_;
v___y_565_ = v___x_575_;
goto v___jp_563_;
}
else
{
lean_object* v___x_576_; 
v___x_576_ = l_Lean_PostprocessTraces_TraceTree_modifyData(v___x_575_, v___f_554_);
v___y_564_ = v___y_572_;
v___y_565_ = v___x_576_;
goto v___jp_563_;
}
}
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_dec_ref(v___f_554_);
lean_dec_ref(v_t_544_);
v_a_583_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_558_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_558_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
else
{
lean_object* v___x_591_; lean_object* v___x_593_; 
lean_dec_ref(v_p_543_);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v_t_544_);
lean_ctor_set(v___x_591_, 1, v_a_549_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_591_);
v___x_593_ = v___x_551_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
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
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec_ref(v_t_544_);
lean_dec_ref(v_p_543_);
v_a_596_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_548_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_548_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__0(lean_object* v_p_604_, size_t v_sz_605_, size_t v_i_606_, lean_object* v_bs_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
uint8_t v___x_611_; 
v___x_611_ = lean_usize_dec_lt(v_i_606_, v_sz_605_);
if (v___x_611_ == 0)
{
lean_object* v___x_612_; 
lean_dec_ref(v_p_604_);
v___x_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_612_, 0, v_bs_607_);
return v___x_612_;
}
else
{
lean_object* v_v_613_; lean_object* v___x_614_; lean_object* v_bs_x27_615_; lean_object* v___x_616_; 
v_v_613_ = lean_array_uget(v_bs_607_, v_i_606_);
v___x_614_ = lean_unsigned_to_nat(0u);
v_bs_x27_615_ = lean_array_uset(v_bs_607_, v_i_606_, v___x_614_);
lean_inc_ref(v_p_604_);
v___x_616_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go(v_p_604_, v_v_613_, v___y_608_, v___y_609_);
if (lean_obj_tag(v___x_616_) == 0)
{
lean_object* v_a_617_; size_t v___x_618_; size_t v___x_619_; lean_object* v___x_620_; 
v_a_617_ = lean_ctor_get(v___x_616_, 0);
lean_inc(v_a_617_);
lean_dec_ref_known(v___x_616_, 1);
v___x_618_ = ((size_t)1ULL);
v___x_619_ = lean_usize_add(v_i_606_, v___x_618_);
v___x_620_ = lean_array_uset(v_bs_x27_615_, v_i_606_, v_a_617_);
v_i_606_ = v___x_619_;
v_bs_607_ = v___x_620_;
goto _start;
}
else
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_629_; 
lean_dec_ref(v_bs_x27_615_);
lean_dec_ref(v_p_604_);
v_a_622_ = lean_ctor_get(v___x_616_, 0);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_616_);
if (v_isSharedCheck_629_ == 0)
{
v___x_624_ = v___x_616_;
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_616_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_629_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_627_; 
if (v_isShared_625_ == 0)
{
v___x_627_ = v___x_624_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_a_622_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__0___boxed(lean_object* v_p_630_, lean_object* v_sz_631_, lean_object* v_i_632_, lean_object* v_bs_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
size_t v_sz_boxed_637_; size_t v_i_boxed_638_; lean_object* v_res_639_; 
v_sz_boxed_637_ = lean_unbox_usize(v_sz_631_);
lean_dec(v_sz_631_);
v_i_boxed_638_ = lean_unbox_usize(v_i_632_);
lean_dec(v_i_632_);
v_res_639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__0(v_p_630_, v_sz_boxed_637_, v_i_boxed_638_, v_bs_633_, v___y_634_, v___y_635_);
lean_dec(v___y_635_);
lean_dec_ref(v___y_634_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go___boxed(lean_object* v_p_640_, lean_object* v_t_641_, lean_object* v_a_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go(v_p_640_, v_t_641_, v_a_642_, v_a_643_);
lean_dec(v_a_643_);
lean_dec_ref(v_a_642_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_exposeSubtrees_spec__0(lean_object* v_p_646_, size_t v_sz_647_, size_t v_i_648_, lean_object* v_bs_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
uint8_t v___x_653_; 
v___x_653_ = lean_usize_dec_lt(v_i_648_, v_sz_647_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; 
lean_dec_ref(v_p_646_);
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v_bs_649_);
return v___x_654_;
}
else
{
lean_object* v_v_655_; lean_object* v___x_656_; lean_object* v_bs_x27_657_; lean_object* v___x_658_; 
v_v_655_ = lean_array_uget(v_bs_649_, v_i_648_);
v___x_656_ = lean_unsigned_to_nat(0u);
v_bs_x27_657_ = lean_array_uset(v_bs_649_, v_i_648_, v___x_656_);
lean_inc_ref(v_p_646_);
v___x_658_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go(v_p_646_, v_v_655_, v___y_650_, v___y_651_);
if (lean_obj_tag(v___x_658_) == 0)
{
lean_object* v_a_659_; lean_object* v_fst_660_; size_t v___x_661_; size_t v___x_662_; lean_object* v___x_663_; 
v_a_659_ = lean_ctor_get(v___x_658_, 0);
lean_inc(v_a_659_);
lean_dec_ref_known(v___x_658_, 1);
v_fst_660_ = lean_ctor_get(v_a_659_, 0);
lean_inc(v_fst_660_);
lean_dec(v_a_659_);
v___x_661_ = ((size_t)1ULL);
v___x_662_ = lean_usize_add(v_i_648_, v___x_661_);
v___x_663_ = lean_array_uset(v_bs_x27_657_, v_i_648_, v_fst_660_);
v_i_648_ = v___x_662_;
v_bs_649_ = v___x_663_;
goto _start;
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
lean_dec_ref(v_bs_x27_657_);
lean_dec_ref(v_p_646_);
v_a_665_ = lean_ctor_get(v___x_658_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_658_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_658_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_658_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_exposeSubtrees_spec__0___boxed(lean_object* v_p_673_, lean_object* v_sz_674_, lean_object* v_i_675_, lean_object* v_bs_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
size_t v_sz_boxed_680_; size_t v_i_boxed_681_; lean_object* v_res_682_; 
v_sz_boxed_680_ = lean_unbox_usize(v_sz_674_);
lean_dec(v_sz_674_);
v_i_boxed_681_ = lean_unbox_usize(v_i_675_);
lean_dec(v_i_675_);
v_res_682_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_exposeSubtrees_spec__0(v_p_673_, v_sz_boxed_680_, v_i_boxed_681_, v_bs_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_exposeSubtrees(lean_object* v_p_683_, lean_object* v_roots_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
size_t v_sz_688_; size_t v___x_689_; lean_object* v___x_690_; 
v_sz_688_ = lean_array_size(v_roots_684_);
v___x_689_ = ((size_t)0ULL);
v___x_690_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_exposeSubtrees_spec__0(v_p_683_, v_sz_688_, v___x_689_, v_roots_684_, v_a_685_, v_a_686_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_exposeSubtrees___boxed(lean_object* v_p_691_, lean_object* v_roots_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Lean_PostprocessTraces_exposeSubtrees(v_p_691_, v_roots_692_, v_a_693_, v_a_694_);
lean_dec(v_a_694_);
lean_dec_ref(v_a_693_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__2(lean_object* v_as_697_, size_t v_i_698_, size_t v_stop_699_, lean_object* v_b_700_){
_start:
{
uint8_t v___x_701_; 
v___x_701_ = lean_usize_dec_eq(v_i_698_, v_stop_699_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; lean_object* v_snd_703_; lean_object* v___x_704_; size_t v___x_705_; size_t v___x_706_; 
v___x_702_ = lean_array_uget_borrowed(v_as_697_, v_i_698_);
v_snd_703_ = lean_ctor_get(v___x_702_, 1);
v___x_704_ = lean_nat_add(v_b_700_, v_snd_703_);
lean_dec(v_b_700_);
v___x_705_ = ((size_t)1ULL);
v___x_706_ = lean_usize_add(v_i_698_, v___x_705_);
v_i_698_ = v___x_706_;
v_b_700_ = v___x_704_;
goto _start;
}
else
{
return v_b_700_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__2___boxed(lean_object* v_as_708_, lean_object* v_i_709_, lean_object* v_stop_710_, lean_object* v_b_711_){
_start:
{
size_t v_i_boxed_712_; size_t v_stop_boxed_713_; lean_object* v_res_714_; 
v_i_boxed_712_ = lean_unbox_usize(v_i_709_);
lean_dec(v_i_709_);
v_stop_boxed_713_ = lean_unbox_usize(v_stop_710_);
lean_dec(v_stop_710_);
v_res_714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__2(v_as_708_, v_i_boxed_712_, v_stop_boxed_713_, v_b_711_);
lean_dec_ref(v_as_708_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__1(size_t v_sz_715_, size_t v_i_716_, lean_object* v_bs_717_){
_start:
{
uint8_t v___x_718_; 
v___x_718_ = lean_usize_dec_lt(v_i_716_, v_sz_715_);
if (v___x_718_ == 0)
{
return v_bs_717_;
}
else
{
lean_object* v_v_719_; lean_object* v_fst_720_; lean_object* v___x_721_; lean_object* v_bs_x27_722_; size_t v___x_723_; size_t v___x_724_; lean_object* v___x_725_; 
v_v_719_ = lean_array_uget_borrowed(v_bs_717_, v_i_716_);
v_fst_720_ = lean_ctor_get(v_v_719_, 0);
lean_inc(v_fst_720_);
v___x_721_ = lean_unsigned_to_nat(0u);
v_bs_x27_722_ = lean_array_uset(v_bs_717_, v_i_716_, v___x_721_);
v___x_723_ = ((size_t)1ULL);
v___x_724_ = lean_usize_add(v_i_716_, v___x_723_);
v___x_725_ = lean_array_uset(v_bs_x27_722_, v_i_716_, v_fst_720_);
v_i_716_ = v___x_724_;
v_bs_717_ = v___x_725_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__1___boxed(lean_object* v_sz_727_, lean_object* v_i_728_, lean_object* v_bs_729_){
_start:
{
size_t v_sz_boxed_730_; size_t v_i_boxed_731_; lean_object* v_res_732_; 
v_sz_boxed_730_ = lean_unbox_usize(v_sz_727_);
lean_dec(v_sz_727_);
v_i_boxed_731_ = lean_unbox_usize(v_i_728_);
lean_dec(v_i_728_);
v_res_732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__1(v_sz_boxed_730_, v_i_boxed_731_, v_bs_729_);
return v_res_732_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__1(void){
_start:
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__0));
v___x_735_ = l_Lean_stringToMessageData(v___x_734_);
return v___x_735_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__3(void){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__2));
v___x_738_ = l_Lean_stringToMessageData(v___x_737_);
return v___x_738_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__5(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__4));
v___x_741_ = l_Lean_stringToMessageData(v___x_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go(lean_object* v_a_744_){
_start:
{
if (lean_obj_tag(v_a_744_) == 0)
{
lean_object* v_data_745_; lean_object* v_msg_746_; lean_object* v_children_747_; lean_object* v_wrap_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_787_; 
v_data_745_ = lean_ctor_get(v_a_744_, 0);
v_msg_746_ = lean_ctor_get(v_a_744_, 1);
v_children_747_ = lean_ctor_get(v_a_744_, 2);
v_wrap_748_ = lean_ctor_get(v_a_744_, 3);
v_isSharedCheck_787_ = !lean_is_exclusive(v_a_744_);
if (v_isSharedCheck_787_ == 0)
{
v___x_750_ = v_a_744_;
v_isShared_751_ = v_isSharedCheck_787_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_wrap_748_);
lean_inc(v_children_747_);
lean_inc(v_msg_746_);
lean_inc(v_data_745_);
lean_dec(v_a_744_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_787_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
size_t v_sz_752_; size_t v___x_753_; lean_object* v_results_754_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___x_776_; lean_object* v___y_778_; lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v_sz_752_ = lean_array_size(v_children_747_);
v___x_753_ = ((size_t)0ULL);
v_results_754_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__0(v_sz_752_, v___x_753_, v_children_747_);
v___x_776_ = lean_unsigned_to_nat(1u);
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = lean_array_get_size(v_results_754_);
v___x_784_ = lean_nat_dec_lt(v___x_782_, v___x_783_);
if (v___x_784_ == 0)
{
v___y_778_ = v___x_776_;
goto v___jp_777_;
}
else
{
size_t v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_usize_of_nat(v___x_783_);
v___x_786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__2(v_results_754_, v___x_753_, v___x_785_, v___x_776_);
v___y_778_ = v___x_786_;
goto v___jp_777_;
}
v___jp_755_:
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; size_t v_sz_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
v___x_758_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__1, &l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__1_once, _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__1);
v___x_759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_759_, 0, v_msg_746_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
lean_inc(v___y_756_);
v___x_760_ = l_Nat_reprFast(v___y_756_);
v___x_761_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
v___x_762_ = l_Lean_MessageData_ofFormat(v___x_761_);
v___x_763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_759_);
lean_ctor_set(v___x_763_, 1, v___x_762_);
v___x_764_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__3, &l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__3_once, _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__3);
v___x_765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_763_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
lean_inc_ref(v___y_757_);
v___x_766_ = l_Lean_stringToMessageData(v___y_757_);
v___x_767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_767_, 0, v___x_765_);
lean_ctor_set(v___x_767_, 1, v___x_766_);
v___x_768_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__5, &l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__5_once, _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__5);
v___x_769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_767_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v_sz_770_ = lean_array_size(v_results_754_);
v___x_771_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__1(v_sz_770_, v___x_753_, v_results_754_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 2, v___x_771_);
lean_ctor_set(v___x_750_, 1, v___x_769_);
v___x_773_ = v___x_750_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_data_745_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v___x_769_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v___x_771_);
lean_ctor_set(v_reuseFailAlloc_775_, 3, v_wrap_748_);
v___x_773_ = v_reuseFailAlloc_775_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_774_; 
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
lean_ctor_set(v___x_774_, 1, v___y_756_);
return v___x_774_;
}
}
v___jp_777_:
{
uint8_t v___x_779_; 
v___x_779_ = lean_nat_dec_eq(v___y_778_, v___x_776_);
if (v___x_779_ == 0)
{
lean_object* v___x_780_; 
v___x_780_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__6));
v___y_756_ = v___y_778_;
v___y_757_ = v___x_780_;
goto v___jp_755_;
}
else
{
lean_object* v___x_781_; 
v___x_781_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__7));
v___y_756_ = v___y_778_;
v___y_757_ = v___x_781_;
goto v___jp_755_;
}
}
}
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_unsigned_to_nat(1u);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v_a_744_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
return v___x_789_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__0(size_t v_sz_790_, size_t v_i_791_, lean_object* v_bs_792_){
_start:
{
uint8_t v___x_793_; 
v___x_793_ = lean_usize_dec_lt(v_i_791_, v_sz_790_);
if (v___x_793_ == 0)
{
return v_bs_792_;
}
else
{
lean_object* v_v_794_; lean_object* v___x_795_; lean_object* v_bs_x27_796_; lean_object* v___x_797_; size_t v___x_798_; size_t v___x_799_; lean_object* v___x_800_; 
v_v_794_ = lean_array_uget(v_bs_792_, v_i_791_);
v___x_795_ = lean_unsigned_to_nat(0u);
v_bs_x27_796_ = lean_array_uset(v_bs_792_, v_i_791_, v___x_795_);
v___x_797_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go(v_v_794_);
v___x_798_ = ((size_t)1ULL);
v___x_799_ = lean_usize_add(v_i_791_, v___x_798_);
v___x_800_ = lean_array_uset(v_bs_x27_796_, v_i_791_, v___x_797_);
v_i_791_ = v___x_799_;
v_bs_792_ = v___x_800_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__0___boxed(lean_object* v_sz_802_, lean_object* v_i_803_, lean_object* v_bs_804_){
_start:
{
size_t v_sz_boxed_805_; size_t v_i_boxed_806_; lean_object* v_res_807_; 
v_sz_boxed_805_ = lean_unbox_usize(v_sz_802_);
lean_dec(v_sz_802_);
v_i_boxed_806_ = lean_unbox_usize(v_i_803_);
lean_dec(v_i_803_);
v_res_807_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__0(v_sz_boxed_805_, v_i_boxed_806_, v_bs_804_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_countNodes_spec__0(size_t v_sz_808_, size_t v_i_809_, lean_object* v_bs_810_){
_start:
{
uint8_t v___x_811_; 
v___x_811_ = lean_usize_dec_lt(v_i_809_, v_sz_808_);
if (v___x_811_ == 0)
{
return v_bs_810_;
}
else
{
lean_object* v_v_812_; lean_object* v___x_813_; lean_object* v_fst_814_; lean_object* v___x_815_; lean_object* v_bs_x27_816_; size_t v___x_817_; size_t v___x_818_; lean_object* v___x_819_; 
v_v_812_ = lean_array_uget_borrowed(v_bs_810_, v_i_809_);
lean_inc(v_v_812_);
v___x_813_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go(v_v_812_);
v_fst_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_fst_814_);
lean_dec_ref(v___x_813_);
v___x_815_ = lean_unsigned_to_nat(0u);
v_bs_x27_816_ = lean_array_uset(v_bs_810_, v_i_809_, v___x_815_);
v___x_817_ = ((size_t)1ULL);
v___x_818_ = lean_usize_add(v_i_809_, v___x_817_);
v___x_819_ = lean_array_uset(v_bs_x27_816_, v_i_809_, v_fst_814_);
v_i_809_ = v___x_818_;
v_bs_810_ = v___x_819_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_countNodes_spec__0___boxed(lean_object* v_sz_821_, lean_object* v_i_822_, lean_object* v_bs_823_){
_start:
{
size_t v_sz_boxed_824_; size_t v_i_boxed_825_; lean_object* v_res_826_; 
v_sz_boxed_824_ = lean_unbox_usize(v_sz_821_);
lean_dec(v_sz_821_);
v_i_boxed_825_ = lean_unbox_usize(v_i_822_);
lean_dec(v_i_822_);
v_res_826_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_countNodes_spec__0(v_sz_boxed_824_, v_i_boxed_825_, v_bs_823_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_countNodes___redArg(lean_object* v_roots_827_){
_start:
{
size_t v_sz_829_; size_t v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v_sz_829_ = lean_array_size(v_roots_827_);
v___x_830_ = ((size_t)0ULL);
v___x_831_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_countNodes_spec__0(v_sz_829_, v___x_830_, v_roots_827_);
v___x_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_832_, 0, v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_countNodes___redArg___boxed(lean_object* v_roots_833_, lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_PostprocessTraces_countNodes___redArg(v_roots_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_countNodes(lean_object* v_roots_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = l_Lean_PostprocessTraces_countNodes___redArg(v_roots_836_);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_countNodes___boxed(lean_object* v_roots_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_PostprocessTraces_countNodes(v_roots_841_, v_a_842_, v_a_843_);
lean_dec(v_a_843_);
lean_dec_ref(v_a_842_);
return v_res_845_;
}
}
static double _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__0(void){
_start:
{
lean_object* v___x_846_; double v___x_847_; 
v___x_846_ = lean_unsigned_to_nat(10u);
v___x_847_ = lean_float_of_nat(v___x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs(double v_ms_850_){
_start:
{
lean_object* v___x_851_; double v___x_852_; double v___x_853_; double v___x_854_; uint64_t v___x_855_; lean_object* v_tenths_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_851_ = lean_unsigned_to_nat(10u);
v___x_852_ = lean_float_once(&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__0, &l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__0_once, _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__0);
v___x_853_ = lean_float_mul(v_ms_850_, v___x_852_);
v___x_854_ = round(v___x_853_);
v___x_855_ = lean_float_to_uint64(v___x_854_);
v_tenths_856_ = lean_uint64_to_nat(v___x_855_);
v___x_857_ = lean_nat_div(v_tenths_856_, v___x_851_);
v___x_858_ = l_Nat_reprFast(v___x_857_);
v___x_859_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__1));
v___x_860_ = lean_string_append(v___x_858_, v___x_859_);
v___x_861_ = lean_nat_mod(v_tenths_856_, v___x_851_);
lean_dec(v_tenths_856_);
v___x_862_ = l_Nat_reprFast(v___x_861_);
v___x_863_ = lean_string_append(v___x_860_, v___x_862_);
lean_dec_ref(v___x_862_);
v___x_864_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__2));
v___x_865_ = lean_string_append(v___x_863_, v___x_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___boxed(lean_object* v_ms_866_){
_start:
{
double v_ms_boxed_867_; lean_object* v_res_868_; 
v_ms_boxed_867_ = lean_unbox_float(v_ms_866_);
lean_dec_ref(v_ms_866_);
v_res_868_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs(v_ms_boxed_867_);
return v_res_868_;
}
}
static double _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__0(void){
_start:
{
lean_object* v___x_869_; double v___x_870_; 
v___x_869_ = lean_unsigned_to_nat(0u);
v___x_870_ = lean_float_of_nat(v___x_869_);
return v___x_870_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__2(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__1));
v___x_873_ = l_Lean_stringToMessageData(v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go(lean_object* v_a_874_){
_start:
{
if (lean_obj_tag(v_a_874_) == 0)
{
lean_object* v_data_875_; lean_object* v_msg_876_; lean_object* v_children_877_; lean_object* v_wrap_878_; lean_object* v___y_880_; double v_startTime_885_; double v___x_886_; uint8_t v___x_887_; 
v_data_875_ = lean_ctor_get(v_a_874_, 0);
lean_inc_ref(v_data_875_);
v_msg_876_ = lean_ctor_get(v_a_874_, 1);
v_children_877_ = lean_ctor_get(v_a_874_, 2);
lean_inc_ref(v_children_877_);
v_wrap_878_ = lean_ctor_get(v_a_874_, 3);
lean_inc_ref(v_wrap_878_);
v_startTime_885_ = lean_ctor_get_float(v_data_875_, sizeof(void*)*3);
v___x_886_ = lean_float_once(&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__0, &l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__0_once, _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__0);
v___x_887_ = lean_float_beq(v_startTime_885_, v___x_886_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; lean_object* v___x_889_; double v___x_890_; double v___x_891_; double v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_888_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__2, &l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__2_once, _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__2);
lean_inc_ref(v_msg_876_);
v___x_889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_889_, 0, v_msg_876_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = l_Lean_PostprocessTraces_TraceTree_selfElapsed(v_a_874_);
lean_dec_ref_known(v_a_874_, 4);
v___x_891_ = lean_float_once(&l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0, &l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0_once, _init_l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0);
v___x_892_ = lean_float_mul(v___x_890_, v___x_891_);
v___x_893_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs(v___x_892_);
v___x_894_ = l_Lean_stringToMessageData(v___x_893_);
v___x_895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_889_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__5, &l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__5_once, _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__5);
v___x_897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_897_, 0, v___x_895_);
lean_ctor_set(v___x_897_, 1, v___x_896_);
v___y_880_ = v___x_897_;
goto v___jp_879_;
}
else
{
lean_inc_ref(v_msg_876_);
lean_dec_ref_known(v_a_874_, 4);
v___y_880_ = v_msg_876_;
goto v___jp_879_;
}
v___jp_879_:
{
size_t v_sz_881_; size_t v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_sz_881_ = lean_array_size(v_children_877_);
v___x_882_ = ((size_t)0ULL);
v___x_883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go_spec__0(v_sz_881_, v___x_882_, v_children_877_);
v___x_884_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_884_, 0, v_data_875_);
lean_ctor_set(v___x_884_, 1, v___y_880_);
lean_ctor_set(v___x_884_, 2, v___x_883_);
lean_ctor_set(v___x_884_, 3, v_wrap_878_);
return v___x_884_;
}
}
else
{
return v_a_874_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go_spec__0(size_t v_sz_898_, size_t v_i_899_, lean_object* v_bs_900_){
_start:
{
uint8_t v___x_901_; 
v___x_901_ = lean_usize_dec_lt(v_i_899_, v_sz_898_);
if (v___x_901_ == 0)
{
return v_bs_900_;
}
else
{
lean_object* v_v_902_; lean_object* v___x_903_; lean_object* v_bs_x27_904_; lean_object* v___x_905_; size_t v___x_906_; size_t v___x_907_; lean_object* v___x_908_; 
v_v_902_ = lean_array_uget(v_bs_900_, v_i_899_);
v___x_903_ = lean_unsigned_to_nat(0u);
v_bs_x27_904_ = lean_array_uset(v_bs_900_, v_i_899_, v___x_903_);
v___x_905_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go(v_v_902_);
v___x_906_ = ((size_t)1ULL);
v___x_907_ = lean_usize_add(v_i_899_, v___x_906_);
v___x_908_ = lean_array_uset(v_bs_x27_904_, v_i_899_, v___x_905_);
v_i_899_ = v___x_907_;
v_bs_900_ = v___x_908_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go_spec__0___boxed(lean_object* v_sz_910_, lean_object* v_i_911_, lean_object* v_bs_912_){
_start:
{
size_t v_sz_boxed_913_; size_t v_i_boxed_914_; lean_object* v_res_915_; 
v_sz_boxed_913_ = lean_unbox_usize(v_sz_910_);
lean_dec(v_sz_910_);
v_i_boxed_914_ = lean_unbox_usize(v_i_911_);
lean_dec(v_i_911_);
v_res_915_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go_spec__0(v_sz_boxed_913_, v_i_boxed_914_, v_bs_912_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_selfTime___redArg(lean_object* v_roots_916_){
_start:
{
size_t v_sz_918_; size_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v_sz_918_ = lean_array_size(v_roots_916_);
v___x_919_ = ((size_t)0ULL);
v___x_920_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go_spec__0(v_sz_918_, v___x_919_, v_roots_916_);
v___x_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_selfTime___redArg___boxed(lean_object* v_roots_922_, lean_object* v_a_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_PostprocessTraces_selfTime___redArg(v_roots_922_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_selfTime(lean_object* v_roots_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = l_Lean_PostprocessTraces_selfTime___redArg(v_roots_925_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_selfTime___boxed(lean_object* v_roots_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_PostprocessTraces_selfTime(v_roots_930_, v_a_931_, v_a_932_);
lean_dec(v_a_932_);
lean_dec_ref(v_a_931_);
return v_res_934_;
}
}
lean_object* runtime_initialize_Lean_PostprocessTraces_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_PostprocessTraces_Postprocessors(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
