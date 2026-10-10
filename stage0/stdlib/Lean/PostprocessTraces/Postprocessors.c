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
uint8_t l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr(lean_object* v_s_84_, lean_object* v_pat_85_){
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
LEAN_EXPORT void l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_84_ = stack[0].m_obj;
lean_object* v_pat_85_ = stack[1].m_obj;
uint8_t v_res_101_;
v_res_101_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr(v_s_84_, v_pat_85_);
stack->m_num = v_res_101_;
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr___boxed(lean_object* v_s_102_, lean_object* v_pat_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr(v_s_102_, v_pat_103_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_spec__0(lean_object* v_s_106_, lean_object* v___x_107_, lean_object* v___x_108_, lean_object* v_inst_109_, lean_object* v_R_110_, lean_object* v_a_111_, lean_object* v_b_112_, lean_object* v_c_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_spec__0___redArg(v_s_106_, v___x_107_, v___x_108_, v_a_111_, v_b_112_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_spec__0___boxed(lean_object* v_s_115_, lean_object* v___x_116_, lean_object* v___x_117_, lean_object* v_inst_118_, lean_object* v_R_119_, lean_object* v_a_120_, lean_object* v_b_121_, lean_object* v_c_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr_spec__0(v_s_115_, v___x_116_, v___x_117_, v_inst_118_, v_R_119_, v_a_120_, v_b_121_, v_c_122_);
lean_dec(v_b_121_);
lean_dec(v___x_117_);
lean_dec_ref(v___x_116_);
lean_dec_ref(v_s_115_);
return v_res_123_;
}
}
uint8_t l_instBEqOption_beq___at___00Lean_PostprocessTraces_ofClass_spec__0(lean_object* v_x_124_, lean_object* v_x_125_){
_start:
{
if (lean_obj_tag(v_x_124_) == 0)
{
if (lean_obj_tag(v_x_125_) == 0)
{
uint8_t v___x_126_; 
v___x_126_ = 1;
return v___x_126_;
}
else
{
uint8_t v___x_127_; 
v___x_127_ = 0;
return v___x_127_;
}
}
else
{
if (lean_obj_tag(v_x_125_) == 0)
{
uint8_t v___x_128_; 
v___x_128_ = 0;
return v___x_128_;
}
else
{
lean_object* v_val_129_; lean_object* v_val_130_; uint8_t v___x_131_; 
v_val_129_ = lean_ctor_get(v_x_124_, 0);
v_val_130_ = lean_ctor_get(v_x_125_, 0);
v___x_131_ = lean_name_eq(v_val_129_, v_val_130_);
return v___x_131_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_PostprocessTraces_ofClass_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_124_ = stack[0].m_obj;
lean_object* v_x_125_ = stack[1].m_obj;
uint8_t v_res_132_;
v_res_132_ = l_instBEqOption_beq___at___00Lean_PostprocessTraces_ofClass_spec__0(v_x_124_, v_x_125_);
stack->m_num = v_res_132_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_PostprocessTraces_ofClass_spec__0___boxed(lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = l_instBEqOption_beq___at___00Lean_PostprocessTraces_ofClass_spec__0(v_x_133_, v_x_134_);
lean_dec(v_x_134_);
lean_dec(v_x_133_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
lean_object* l_Lean_PostprocessTraces_ofClass___redArg(lean_object* v_cls_137_, lean_object* v_t_138_){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_140_ = l_Lean_PostprocessTraces_TraceTree_cls_x3f(v_t_138_);
v___x_141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_141_, 0, v_cls_137_);
v___x_142_ = l_instBEqOption_beq___at___00Lean_PostprocessTraces_ofClass_spec__0(v___x_140_, v___x_141_);
lean_dec_ref_known(v___x_141_, 1);
lean_dec(v___x_140_);
v___x_143_ = lean_box(v___x_142_);
v___x_144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_ofClass___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_137_ = stack[0].m_obj;
lean_object* v_t_138_ = stack[1].m_obj;
lean_object* v_res_145_;
v_res_145_ = l_Lean_PostprocessTraces_ofClass___redArg(v_cls_137_, v_t_138_);
stack->m_obj
 = v_res_145_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass___redArg___boxed(lean_object* v_cls_146_, lean_object* v_t_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_PostprocessTraces_ofClass___redArg(v_cls_146_, v_t_147_);
lean_dec_ref(v_t_147_);
return v_res_149_;
}
}
lean_object* l_Lean_PostprocessTraces_ofClass(lean_object* v_cls_150_, lean_object* v_t_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_PostprocessTraces_ofClass___redArg(v_cls_150_, v_t_151_);
return v___x_155_;
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_ofClass_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_150_ = stack[0].m_obj;
lean_object* v_t_151_ = stack[1].m_obj;
lean_object* v_a_152_ = stack[2].m_obj;
lean_object* v_a_153_ = stack[3].m_obj;
lean_object* v_res_156_;
v_res_156_ = l_Lean_PostprocessTraces_ofClass(v_cls_150_, v_t_151_, v_a_152_, v_a_153_);
stack->m_obj
 = v_res_156_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_ofClass___boxed(lean_object* v_cls_157_, lean_object* v_t_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Lean_PostprocessTraces_ofClass(v_cls_157_, v_t_158_, v_a_159_, v_a_160_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec_ref(v_t_158_);
return v_res_162_;
}
}
lean_object* l_Lean_PostprocessTraces_containsString___redArg(lean_object* v_pat_163_, lean_object* v_t_164_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_Lean_PostprocessTraces_TraceTree_cls_x3f(v_t_164_);
if (lean_obj_tag(v___x_171_) == 0)
{
goto v___jp_166_;
}
else
{
lean_object* v_val_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_183_; 
v_val_172_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_183_ == 0)
{
v___x_174_ = v___x_171_;
v_isShared_175_ = v_isSharedCheck_183_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_val_172_);
lean_dec(v___x_171_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_183_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
uint8_t v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_176_ = 1;
v___x_177_ = l_Lean_Name_toString(v_val_172_, v___x_176_);
lean_inc_ref(v_pat_163_);
v___x_178_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr(v___x_177_, v_pat_163_);
if (v___x_178_ == 0)
{
lean_del_object(v___x_174_);
goto v___jp_166_;
}
else
{
lean_object* v___x_179_; lean_object* v___x_181_; 
lean_dec_ref(v_t_164_);
lean_dec_ref(v_pat_163_);
v___x_179_ = lean_box(v___x_178_);
if (v_isShared_175_ == 0)
{
lean_ctor_set_tag(v___x_174_, 0);
lean_ctor_set(v___x_174_, 0, v___x_179_);
v___x_181_ = v___x_174_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_179_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
v___jp_166_:
{
lean_object* v___x_167_; uint8_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_167_ = l_Lean_PostprocessTraces_TraceTree_headText(v_t_164_);
v___x_168_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_containsSubstr(v___x_167_, v_pat_163_);
v___x_169_ = lean_box(v___x_168_);
v___x_170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
return v___x_170_;
}
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_containsString___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_pat_163_ = stack[0].m_obj;
lean_object* v_t_164_ = stack[1].m_obj;
lean_object* v_res_184_;
v_res_184_ = l_Lean_PostprocessTraces_containsString___redArg(v_pat_163_, v_t_164_);
stack->m_obj
 = v_res_184_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString___redArg___boxed(lean_object* v_pat_185_, lean_object* v_t_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_PostprocessTraces_containsString___redArg(v_pat_185_, v_t_186_);
return v_res_188_;
}
}
lean_object* l_Lean_PostprocessTraces_containsString(lean_object* v_pat_189_, lean_object* v_t_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_PostprocessTraces_containsString___redArg(v_pat_189_, v_t_190_);
return v___x_194_;
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_containsString_0interp(lean_interpreter_value* stack)
{
lean_object* v_pat_189_ = stack[0].m_obj;
lean_object* v_t_190_ = stack[1].m_obj;
lean_object* v_a_191_ = stack[2].m_obj;
lean_object* v_a_192_ = stack[3].m_obj;
lean_object* v_res_195_;
v_res_195_ = l_Lean_PostprocessTraces_containsString(v_pat_189_, v_t_190_, v_a_191_, v_a_192_);
stack->m_obj
 = v_res_195_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_containsString___boxed(lean_object* v_pat_196_, lean_object* v_t_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_Lean_PostprocessTraces_containsString(v_pat_196_, v_t_197_, v_a_198_, v_a_199_);
lean_dec(v_a_199_);
lean_dec_ref(v_a_198_);
return v_res_201_;
}
}
uint8_t l_instBEqOption_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(lean_object* v_x_202_, lean_object* v_x_203_){
_start:
{
if (lean_obj_tag(v_x_202_) == 0)
{
if (lean_obj_tag(v_x_203_) == 0)
{
uint8_t v___x_204_; 
v___x_204_ = 1;
return v___x_204_;
}
else
{
uint8_t v___x_205_; 
v___x_205_ = 0;
return v___x_205_;
}
}
else
{
if (lean_obj_tag(v_x_203_) == 0)
{
uint8_t v___x_206_; 
v___x_206_ = 0;
return v___x_206_;
}
else
{
lean_object* v_val_207_; lean_object* v_val_208_; uint8_t v___x_209_; uint8_t v___x_210_; uint8_t v___x_211_; 
v_val_207_ = lean_ctor_get(v_x_202_, 0);
v_val_208_ = lean_ctor_get(v_x_203_, 0);
v___x_209_ = lean_unbox(v_val_207_);
v___x_210_ = lean_unbox(v_val_208_);
v___x_211_ = l_Lean_instBEqTraceResult_beq(v___x_209_, v___x_210_);
return v___x_211_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_PostprocessTraces_succeeded_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_202_ = stack[0].m_obj;
lean_object* v_x_203_ = stack[1].m_obj;
uint8_t v_res_212_;
v_res_212_ = l_instBEqOption_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v_x_202_, v_x_203_);
stack->m_num = v_res_212_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_PostprocessTraces_succeeded_spec__0___boxed(lean_object* v_x_213_, lean_object* v_x_214_){
_start:
{
uint8_t v_res_215_; lean_object* v_r_216_; 
v_res_215_ = l_instBEqOption_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v_x_213_, v_x_214_);
lean_dec(v_x_214_);
lean_dec(v_x_213_);
v_r_216_ = lean_box(v_res_215_);
return v_r_216_;
}
}
lean_object* l_Lean_PostprocessTraces_succeeded___redArg(lean_object* v_t_220_){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_222_ = l_Lean_PostprocessTraces_TraceTree_result_x3f(v_t_220_);
v___x_223_ = ((lean_object*)(l_Lean_PostprocessTraces_succeeded___redArg___closed__0));
v___x_224_ = l_instBEqOption_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v___x_222_, v___x_223_);
lean_dec(v___x_222_);
v___x_225_ = lean_box(v___x_224_);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_succeeded___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_220_ = stack[0].m_obj;
lean_object* v_res_227_;
v_res_227_ = l_Lean_PostprocessTraces_succeeded___redArg(v_t_220_);
stack->m_obj
 = v_res_227_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_succeeded___redArg___boxed(lean_object* v_t_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_PostprocessTraces_succeeded___redArg(v_t_228_);
lean_dec_ref(v_t_228_);
return v_res_230_;
}
}
lean_object* l_Lean_PostprocessTraces_succeeded(lean_object* v_t_231_, lean_object* v_a_232_, lean_object* v_a_233_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_PostprocessTraces_succeeded___redArg(v_t_231_);
return v___x_235_;
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_succeeded_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_231_ = stack[0].m_obj;
lean_object* v_a_232_ = stack[1].m_obj;
lean_object* v_a_233_ = stack[2].m_obj;
lean_object* v_res_236_;
v_res_236_ = l_Lean_PostprocessTraces_succeeded(v_t_231_, v_a_232_, v_a_233_);
stack->m_obj
 = v_res_236_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_succeeded___boxed(lean_object* v_t_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_PostprocessTraces_succeeded(v_t_237_, v_a_238_, v_a_239_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
lean_dec_ref(v_t_237_);
return v_res_241_;
}
}
lean_object* l_Lean_PostprocessTraces_failed___redArg(lean_object* v_t_245_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_247_ = l_Lean_PostprocessTraces_TraceTree_result_x3f(v_t_245_);
v___x_248_ = ((lean_object*)(l_Lean_PostprocessTraces_failed___redArg___closed__0));
v___x_249_ = l_instBEqOption_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v___x_247_, v___x_248_);
lean_dec(v___x_247_);
v___x_250_ = lean_box(v___x_249_);
v___x_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_251_, 0, v___x_250_);
return v___x_251_;
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_failed___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_245_ = stack[0].m_obj;
lean_object* v_res_252_;
v_res_252_ = l_Lean_PostprocessTraces_failed___redArg(v_t_245_);
stack->m_obj
 = v_res_252_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_failed___redArg___boxed(lean_object* v_t_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Lean_PostprocessTraces_failed___redArg(v_t_253_);
lean_dec_ref(v_t_253_);
return v_res_255_;
}
}
lean_object* l_Lean_PostprocessTraces_failed(lean_object* v_t_256_, lean_object* v_a_257_, lean_object* v_a_258_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_PostprocessTraces_failed___redArg(v_t_256_);
return v___x_260_;
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_failed_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_256_ = stack[0].m_obj;
lean_object* v_a_257_ = stack[1].m_obj;
lean_object* v_a_258_ = stack[2].m_obj;
lean_object* v_res_261_;
v_res_261_ = l_Lean_PostprocessTraces_failed(v_t_256_, v_a_257_, v_a_258_);
stack->m_obj
 = v_res_261_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_failed___boxed(lean_object* v_t_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_PostprocessTraces_failed(v_t_262_, v_a_263_, v_a_264_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
lean_dec_ref(v_t_262_);
return v_res_266_;
}
}
lean_object* l_Lean_PostprocessTraces_errored___redArg(lean_object* v_t_270_){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; uint8_t v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_272_ = l_Lean_PostprocessTraces_TraceTree_result_x3f(v_t_270_);
v___x_273_ = ((lean_object*)(l_Lean_PostprocessTraces_errored___redArg___closed__0));
v___x_274_ = l_instBEqOption_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v___x_272_, v___x_273_);
lean_dec(v___x_272_);
v___x_275_ = lean_box(v___x_274_);
v___x_276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_errored___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_270_ = stack[0].m_obj;
lean_object* v_res_277_;
v_res_277_ = l_Lean_PostprocessTraces_errored___redArg(v_t_270_);
stack->m_obj
 = v_res_277_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_errored___redArg___boxed(lean_object* v_t_278_, lean_object* v_a_279_){
_start:
{
lean_object* v_res_280_; 
v_res_280_ = l_Lean_PostprocessTraces_errored___redArg(v_t_278_);
lean_dec_ref(v_t_278_);
return v_res_280_;
}
}
lean_object* l_Lean_PostprocessTraces_errored(lean_object* v_t_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Lean_PostprocessTraces_errored___redArg(v_t_281_);
return v___x_285_;
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_errored_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_281_ = stack[0].m_obj;
lean_object* v_a_282_ = stack[1].m_obj;
lean_object* v_a_283_ = stack[2].m_obj;
lean_object* v_res_286_;
v_res_286_ = l_Lean_PostprocessTraces_errored(v_t_281_, v_a_282_, v_a_283_);
stack->m_obj
 = v_res_286_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_errored___boxed(lean_object* v_t_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_PostprocessTraces_errored(v_t_287_, v_a_288_, v_a_289_);
lean_dec(v_a_289_);
lean_dec_ref(v_a_288_);
lean_dec_ref(v_t_287_);
return v_res_291_;
}
}
lean_object* l_Lean_PostprocessTraces_unsuccessful___redArg(lean_object* v_t_292_){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_294_ = l_Lean_PostprocessTraces_TraceTree_result_x3f(v_t_292_);
v___x_295_ = ((lean_object*)(l_Lean_PostprocessTraces_failed___redArg___closed__0));
v___x_296_ = l_instBEqOption_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v___x_294_, v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; uint8_t v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_297_ = ((lean_object*)(l_Lean_PostprocessTraces_errored___redArg___closed__0));
v___x_298_ = l_instBEqOption_beq___at___00Lean_PostprocessTraces_succeeded_spec__0(v___x_294_, v___x_297_);
lean_dec(v___x_294_);
v___x_299_ = lean_box(v___x_298_);
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
return v___x_300_;
}
else
{
lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec(v___x_294_);
v___x_301_ = lean_box(v___x_296_);
v___x_302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
return v___x_302_;
}
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_unsuccessful___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_292_ = stack[0].m_obj;
lean_object* v_res_303_;
v_res_303_ = l_Lean_PostprocessTraces_unsuccessful___redArg(v_t_292_);
stack->m_obj
 = v_res_303_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_unsuccessful___redArg___boxed(lean_object* v_t_304_, lean_object* v_a_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lean_PostprocessTraces_unsuccessful___redArg(v_t_304_);
lean_dec_ref(v_t_304_);
return v_res_306_;
}
}
lean_object* l_Lean_PostprocessTraces_unsuccessful(lean_object* v_t_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_PostprocessTraces_unsuccessful___redArg(v_t_307_);
return v___x_311_;
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_unsuccessful_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_307_ = stack[0].m_obj;
lean_object* v_a_308_ = stack[1].m_obj;
lean_object* v_a_309_ = stack[2].m_obj;
lean_object* v_res_312_;
v_res_312_ = l_Lean_PostprocessTraces_unsuccessful(v_t_307_, v_a_308_, v_a_309_);
stack->m_obj
 = v_res_312_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_unsuccessful___boxed(lean_object* v_t_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_PostprocessTraces_unsuccessful(v_t_313_, v_a_314_, v_a_315_);
lean_dec(v_a_315_);
lean_dec_ref(v_a_314_);
lean_dec_ref(v_t_313_);
return v_res_317_;
}
}
static double _init_l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0(void){
_start:
{
lean_object* v___x_318_; double v___x_319_; 
v___x_318_ = lean_unsigned_to_nat(1000u);
v___x_319_ = lean_float_of_nat(v___x_318_);
return v___x_319_;
}
}
lean_object* l_Lean_PostprocessTraces_minTimeMs___redArg(double v_ms_320_, lean_object* v_t_321_){
_start:
{
double v___x_323_; double v___x_324_; double v___x_325_; uint8_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_323_ = l_Lean_PostprocessTraces_TraceTree_elapsed(v_t_321_);
v___x_324_ = lean_float_once(&l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0, &l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0_once, _init_l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0);
v___x_325_ = lean_float_mul(v___x_323_, v___x_324_);
v___x_326_ = lean_float_decLe(v_ms_320_, v___x_325_);
v___x_327_ = lean_box(v___x_326_);
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_minTimeMs___redArg_0interp(lean_interpreter_value* stack)
{
double v_ms_320_ = stack[0].m_float;
lean_object* v_t_321_ = stack[1].m_obj;
lean_object* v_res_329_;
v_res_329_ = l_Lean_PostprocessTraces_minTimeMs___redArg(v_ms_320_, v_t_321_);
stack->m_obj
 = v_res_329_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minTimeMs___redArg___boxed(lean_object* v_ms_330_, lean_object* v_t_331_, lean_object* v_a_332_){
_start:
{
double v_ms_boxed_333_; lean_object* v_res_334_; 
v_ms_boxed_333_ = lean_unbox_float(v_ms_330_);
lean_dec_ref(v_ms_330_);
v_res_334_ = l_Lean_PostprocessTraces_minTimeMs___redArg(v_ms_boxed_333_, v_t_331_);
lean_dec_ref(v_t_331_);
return v_res_334_;
}
}
lean_object* l_Lean_PostprocessTraces_minTimeMs(double v_ms_335_, lean_object* v_t_336_, lean_object* v_a_337_, lean_object* v_a_338_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l_Lean_PostprocessTraces_minTimeMs___redArg(v_ms_335_, v_t_336_);
return v___x_340_;
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_minTimeMs_0interp(lean_interpreter_value* stack)
{
double v_ms_335_ = stack[0].m_float;
lean_object* v_t_336_ = stack[1].m_obj;
lean_object* v_a_337_ = stack[2].m_obj;
lean_object* v_a_338_ = stack[3].m_obj;
lean_object* v_res_341_;
v_res_341_ = l_Lean_PostprocessTraces_minTimeMs(v_ms_335_, v_t_336_, v_a_337_, v_a_338_);
stack->m_obj
 = v_res_341_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minTimeMs___boxed(lean_object* v_ms_342_, lean_object* v_t_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
double v_ms_boxed_347_; lean_object* v_res_348_; 
v_ms_boxed_347_ = lean_unbox_float(v_ms_342_);
lean_dec_ref(v_ms_342_);
v_res_348_ = l_Lean_PostprocessTraces_minTimeMs(v_ms_boxed_347_, v_t_343_, v_a_344_, v_a_345_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec_ref(v_t_343_);
return v_res_348_;
}
}
lean_object* l_Lean_PostprocessTraces_minSelfTimeMs___redArg(double v_ms_349_, lean_object* v_t_350_){
_start:
{
double v___x_352_; double v___x_353_; double v___x_354_; uint8_t v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_352_ = l_Lean_PostprocessTraces_TraceTree_selfElapsed(v_t_350_);
v___x_353_ = lean_float_once(&l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0, &l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0_once, _init_l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0);
v___x_354_ = lean_float_mul(v___x_352_, v___x_353_);
v___x_355_ = lean_float_decLe(v_ms_349_, v___x_354_);
v___x_356_ = lean_box(v___x_355_);
v___x_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
return v___x_357_;
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_minSelfTimeMs___redArg_0interp(lean_interpreter_value* stack)
{
double v_ms_349_ = stack[0].m_float;
lean_object* v_t_350_ = stack[1].m_obj;
lean_object* v_res_358_;
v_res_358_ = l_Lean_PostprocessTraces_minSelfTimeMs___redArg(v_ms_349_, v_t_350_);
stack->m_obj
 = v_res_358_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minSelfTimeMs___redArg___boxed(lean_object* v_ms_359_, lean_object* v_t_360_, lean_object* v_a_361_){
_start:
{
double v_ms_boxed_362_; lean_object* v_res_363_; 
v_ms_boxed_362_ = lean_unbox_float(v_ms_359_);
lean_dec_ref(v_ms_359_);
v_res_363_ = l_Lean_PostprocessTraces_minSelfTimeMs___redArg(v_ms_boxed_362_, v_t_360_);
lean_dec_ref(v_t_360_);
return v_res_363_;
}
}
lean_object* l_Lean_PostprocessTraces_minSelfTimeMs(double v_ms_364_, lean_object* v_t_365_, lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Lean_PostprocessTraces_minSelfTimeMs___redArg(v_ms_364_, v_t_365_);
return v___x_369_;
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_minSelfTimeMs_0interp(lean_interpreter_value* stack)
{
double v_ms_364_ = stack[0].m_float;
lean_object* v_t_365_ = stack[1].m_obj;
lean_object* v_a_366_ = stack[2].m_obj;
lean_object* v_a_367_ = stack[3].m_obj;
lean_object* v_res_370_;
v_res_370_ = l_Lean_PostprocessTraces_minSelfTimeMs(v_ms_364_, v_t_365_, v_a_366_, v_a_367_);
stack->m_obj
 = v_res_370_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_minSelfTimeMs___boxed(lean_object* v_ms_371_, lean_object* v_t_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_){
_start:
{
double v_ms_boxed_376_; lean_object* v_res_377_; 
v_ms_boxed_376_ = lean_unbox_float(v_ms_371_);
lean_dec_ref(v_ms_371_);
v_res_377_ = l_Lean_PostprocessTraces_minSelfTimeMs(v_ms_boxed_376_, v_t_372_, v_a_373_, v_a_374_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec_ref(v_t_372_);
return v_res_377_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0_spec__0(lean_object* v_p_378_, lean_object* v_as_379_, size_t v_i_380_, size_t v_stop_381_, lean_object* v_b_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v_a_387_; uint8_t v___x_391_; 
v___x_391_ = lean_usize_dec_eq(v_i_380_, v_stop_381_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_array_uget_borrowed(v_as_379_, v_i_380_);
lean_inc(v___x_392_);
lean_inc_ref(v_p_378_);
v___x_393_ = l_Lean_PostprocessTraces_TraceTree_filterSubtrees(v_p_378_, v___x_392_, v___y_383_, v___y_384_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_a_394_; 
v_a_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_a_394_);
lean_dec_ref_known(v___x_393_, 1);
if (lean_obj_tag(v_a_394_) == 0)
{
v_a_387_ = v_b_382_;
goto v___jp_386_;
}
else
{
lean_object* v_val_395_; lean_object* v___x_396_; 
v_val_395_ = lean_ctor_get(v_a_394_, 0);
lean_inc(v_val_395_);
lean_dec_ref_known(v_a_394_, 1);
v___x_396_ = lean_array_push(v_b_382_, v_val_395_);
v_a_387_ = v___x_396_;
goto v___jp_386_;
}
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
lean_dec_ref(v_b_382_);
lean_dec_ref(v_p_378_);
v_a_397_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_393_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_393_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
else
{
lean_object* v___x_405_; 
lean_dec_ref(v_p_378_);
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v_b_382_);
return v___x_405_;
}
v___jp_386_:
{
size_t v___x_388_; size_t v___x_389_; 
v___x_388_ = ((size_t)1ULL);
v___x_389_ = lean_usize_add(v_i_380_, v___x_388_);
v_i_380_ = v___x_389_;
v_b_382_ = v_a_387_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_378_ = stack[0].m_obj;
lean_object* v_as_379_ = stack[1].m_obj;
size_t v_i_380_ = stack[2].m_num;
size_t v_stop_381_ = stack[3].m_num;
lean_object* v_b_382_ = stack[4].m_obj;
lean_object* v___y_383_ = stack[5].m_obj;
lean_object* v___y_384_ = stack[6].m_obj;
lean_object* v_res_406_;
v_res_406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0_spec__0(v_p_378_, v_as_379_, v_i_380_, v_stop_381_, v_b_382_, v___y_383_, v___y_384_);
stack->m_obj
 = v_res_406_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0_spec__0___boxed(lean_object* v_p_407_, lean_object* v_as_408_, lean_object* v_i_409_, lean_object* v_stop_410_, lean_object* v_b_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
size_t v_i_boxed_415_; size_t v_stop_boxed_416_; lean_object* v_res_417_; 
v_i_boxed_415_ = lean_unbox_usize(v_i_409_);
lean_dec(v_i_409_);
v_stop_boxed_416_ = lean_unbox_usize(v_stop_410_);
lean_dec(v_stop_410_);
v_res_417_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0_spec__0(v_p_407_, v_as_408_, v_i_boxed_415_, v_stop_boxed_416_, v_b_411_, v___y_412_, v___y_413_);
lean_dec(v___y_413_);
lean_dec_ref(v___y_412_);
lean_dec_ref(v_as_408_);
return v_res_417_;
}
}
lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0(lean_object* v_p_420_, lean_object* v_as_421_, lean_object* v_start_422_, lean_object* v_stop_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0___closed__0));
v___x_428_ = lean_nat_dec_lt(v_start_422_, v_stop_423_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; 
lean_dec_ref(v_p_420_);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_427_);
return v___x_429_;
}
else
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = lean_array_get_size(v_as_421_);
v___x_431_ = lean_nat_dec_le(v_stop_423_, v___x_430_);
if (v___x_431_ == 0)
{
uint8_t v___x_432_; 
v___x_432_ = lean_nat_dec_lt(v_start_422_, v___x_430_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; 
lean_dec_ref(v_p_420_);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_427_);
return v___x_433_;
}
else
{
size_t v___x_434_; size_t v___x_435_; lean_object* v___x_436_; 
v___x_434_ = lean_usize_of_nat(v_start_422_);
v___x_435_ = lean_usize_of_nat(v___x_430_);
v___x_436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0_spec__0(v_p_420_, v_as_421_, v___x_434_, v___x_435_, v___x_427_, v___y_424_, v___y_425_);
return v___x_436_;
}
}
else
{
size_t v___x_437_; size_t v___x_438_; lean_object* v___x_439_; 
v___x_437_ = lean_usize_of_nat(v_start_422_);
v___x_438_ = lean_usize_of_nat(v_stop_423_);
v___x_439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0_spec__0(v_p_420_, v_as_421_, v___x_437_, v___x_438_, v___x_427_, v___y_424_, v___y_425_);
return v___x_439_;
}
}
}
}
LEAN_EXPORT void l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_420_ = stack[0].m_obj;
lean_object* v_as_421_ = stack[1].m_obj;
lean_object* v_start_422_ = stack[2].m_obj;
lean_object* v_stop_423_ = stack[3].m_obj;
lean_object* v___y_424_ = stack[4].m_obj;
lean_object* v___y_425_ = stack[5].m_obj;
lean_object* v_res_440_;
v_res_440_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0(v_p_420_, v_as_421_, v_start_422_, v_stop_423_, v___y_424_, v___y_425_);
stack->m_obj
 = v_res_440_;
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0___boxed(lean_object* v_p_441_, lean_object* v_as_442_, lean_object* v_start_443_, lean_object* v_stop_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0(v_p_441_, v_as_442_, v_start_443_, v_stop_444_, v___y_445_, v___y_446_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v_stop_444_);
lean_dec(v_start_443_);
lean_dec_ref(v_as_442_);
return v_res_448_;
}
}
lean_object* l_Lean_PostprocessTraces_filterSubtrees(lean_object* v_p_449_, lean_object* v_roots_450_, lean_object* v_a_451_, lean_object* v_a_452_){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_454_ = lean_unsigned_to_nat(0u);
v___x_455_ = lean_array_get_size(v_roots_450_);
v___x_456_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0(v_p_449_, v_roots_450_, v___x_454_, v___x_455_, v_a_451_, v_a_452_);
return v___x_456_;
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_filterSubtrees_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_449_ = stack[0].m_obj;
lean_object* v_roots_450_ = stack[1].m_obj;
lean_object* v_a_451_ = stack[2].m_obj;
lean_object* v_a_452_ = stack[3].m_obj;
lean_object* v_res_457_;
v_res_457_ = l_Lean_PostprocessTraces_filterSubtrees(v_p_449_, v_roots_450_, v_a_451_, v_a_452_);
stack->m_obj
 = v_res_457_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_filterSubtrees___boxed(lean_object* v_p_458_, lean_object* v_roots_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_PostprocessTraces_filterSubtrees(v_p_458_, v_roots_459_, v_a_460_, v_a_461_);
lean_dec(v_a_461_);
lean_dec_ref(v_a_460_);
lean_dec_ref(v_roots_459_);
return v_res_463_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_hoist_spec__0(lean_object* v_p_464_, lean_object* v_as_465_, size_t v_i_466_, size_t v_stop_467_, lean_object* v_b_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
uint8_t v___x_472_; 
v___x_472_ = lean_usize_dec_eq(v_i_466_, v_stop_467_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_array_uget_borrowed(v_as_465_, v_i_466_);
lean_inc(v___x_473_);
lean_inc_ref(v_p_464_);
v___x_474_ = l_Lean_PostprocessTraces_TraceTree_collectSubtrees(v_p_464_, v___x_473_, v_b_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; size_t v___x_476_; size_t v___x_477_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_a_475_);
lean_dec_ref_known(v___x_474_, 1);
v___x_476_ = ((size_t)1ULL);
v___x_477_ = lean_usize_add(v_i_466_, v___x_476_);
v_i_466_ = v___x_477_;
v_b_468_ = v_a_475_;
goto _start;
}
else
{
lean_dec_ref(v_p_464_);
return v___x_474_;
}
}
else
{
lean_object* v___x_479_; 
lean_dec_ref(v_p_464_);
v___x_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_479_, 0, v_b_468_);
return v___x_479_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_hoist_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_464_ = stack[0].m_obj;
lean_object* v_as_465_ = stack[1].m_obj;
size_t v_i_466_ = stack[2].m_num;
size_t v_stop_467_ = stack[3].m_num;
lean_object* v_b_468_ = stack[4].m_obj;
lean_object* v___y_469_ = stack[5].m_obj;
lean_object* v___y_470_ = stack[6].m_obj;
lean_object* v_res_480_;
v_res_480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_hoist_spec__0(v_p_464_, v_as_465_, v_i_466_, v_stop_467_, v_b_468_, v___y_469_, v___y_470_);
stack->m_obj
 = v_res_480_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_hoist_spec__0___boxed(lean_object* v_p_481_, lean_object* v_as_482_, lean_object* v_i_483_, lean_object* v_stop_484_, lean_object* v_b_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
size_t v_i_boxed_489_; size_t v_stop_boxed_490_; lean_object* v_res_491_; 
v_i_boxed_489_ = lean_unbox_usize(v_i_483_);
lean_dec(v_i_483_);
v_stop_boxed_490_ = lean_unbox_usize(v_stop_484_);
lean_dec(v_stop_484_);
v_res_491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_hoist_spec__0(v_p_481_, v_as_482_, v_i_boxed_489_, v_stop_boxed_490_, v_b_485_, v___y_486_, v___y_487_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec_ref(v_as_482_);
return v_res_491_;
}
}
lean_object* l_Lean_PostprocessTraces_hoist(lean_object* v_p_492_, lean_object* v_roots_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_PostprocessTraces_filterSubtrees_spec__0___closed__0));
v___x_499_ = lean_array_get_size(v_roots_493_);
v___x_500_ = lean_nat_dec_lt(v___x_497_, v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; 
lean_dec_ref(v_p_492_);
v___x_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_498_);
return v___x_501_;
}
else
{
uint8_t v___x_502_; 
v___x_502_ = lean_nat_dec_le(v___x_499_, v___x_499_);
if (v___x_502_ == 0)
{
if (v___x_500_ == 0)
{
lean_object* v___x_503_; 
lean_dec_ref(v_p_492_);
v___x_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_498_);
return v___x_503_;
}
else
{
size_t v___x_504_; size_t v___x_505_; lean_object* v___x_506_; 
v___x_504_ = ((size_t)0ULL);
v___x_505_ = lean_usize_of_nat(v___x_499_);
v___x_506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_hoist_spec__0(v_p_492_, v_roots_493_, v___x_504_, v___x_505_, v___x_498_, v_a_494_, v_a_495_);
return v___x_506_;
}
}
else
{
size_t v___x_507_; size_t v___x_508_; lean_object* v___x_509_; 
v___x_507_ = ((size_t)0ULL);
v___x_508_ = lean_usize_of_nat(v___x_499_);
v___x_509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_hoist_spec__0(v_p_492_, v_roots_493_, v___x_507_, v___x_508_, v___x_498_, v_a_494_, v_a_495_);
return v___x_509_;
}
}
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_hoist_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_492_ = stack[0].m_obj;
lean_object* v_roots_493_ = stack[1].m_obj;
lean_object* v_a_494_ = stack[2].m_obj;
lean_object* v_a_495_ = stack[3].m_obj;
lean_object* v_res_510_;
v_res_510_ = l_Lean_PostprocessTraces_hoist(v_p_492_, v_roots_493_, v_a_494_, v_a_495_);
stack->m_obj
 = v_res_510_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_hoist___boxed(lean_object* v_p_511_, lean_object* v_roots_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Lean_PostprocessTraces_hoist(v_p_511_, v_roots_512_, v_a_513_, v_a_514_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec_ref(v_roots_512_);
return v_res_516_;
}
}
lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go___lam__0(uint8_t v_a_517_, lean_object* v_x_518_){
_start:
{
lean_object* v_cls_519_; lean_object* v_result_x3f_520_; double v_startTime_521_; double v_stopTime_522_; lean_object* v_tag_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
v_cls_519_ = lean_ctor_get(v_x_518_, 0);
v_result_x3f_520_ = lean_ctor_get(v_x_518_, 1);
v_startTime_521_ = lean_ctor_get_float(v_x_518_, sizeof(void*)*3);
v_stopTime_522_ = lean_ctor_get_float(v_x_518_, sizeof(void*)*3 + 8);
v_tag_523_ = lean_ctor_get(v_x_518_, 2);
v_isSharedCheck_530_ = !lean_is_exclusive(v_x_518_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v_x_518_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_tag_523_);
lean_inc(v_result_x3f_520_);
lean_inc(v_cls_519_);
lean_dec(v_x_518_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_cls_519_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v_result_x3f_520_);
lean_ctor_set(v_reuseFailAlloc_529_, 2, v_tag_523_);
lean_ctor_set_float(v_reuseFailAlloc_529_, sizeof(void*)*3, v_startTime_521_);
lean_ctor_set_float(v_reuseFailAlloc_529_, sizeof(void*)*3 + 8, v_stopTime_522_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_ctor_set_uint8(v___x_528_, sizeof(void*)*3 + 16, v_a_517_);
return v___x_528_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_517_ = stack[0].m_num;
lean_object* v_x_518_ = stack[1].m_obj;
lean_object* v_res_531_;
v_res_531_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go___lam__0(v_a_517_, v_x_518_);
stack->m_obj
 = v_res_531_;
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go___lam__0___boxed(lean_object* v_a_532_, lean_object* v_x_533_){
_start:
{
uint8_t v_a_905__boxed_534_; lean_object* v_res_535_; 
v_a_905__boxed_534_ = lean_unbox(v_a_532_);
v_res_535_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go___lam__0(v_a_905__boxed_534_, v_x_533_);
return v_res_535_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__2(lean_object* v_as_536_, size_t v_i_537_, size_t v_stop_538_){
_start:
{
uint8_t v___x_539_; 
v___x_539_ = lean_usize_dec_eq(v_i_537_, v_stop_538_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; lean_object* v_snd_541_; uint8_t v___x_542_; 
v___x_540_ = lean_array_uget_borrowed(v_as_536_, v_i_537_);
v_snd_541_ = lean_ctor_get(v___x_540_, 1);
v___x_542_ = lean_unbox(v_snd_541_);
if (v___x_542_ == 0)
{
size_t v___x_543_; size_t v___x_544_; 
v___x_543_ = ((size_t)1ULL);
v___x_544_ = lean_usize_add(v_i_537_, v___x_543_);
v_i_537_ = v___x_544_;
goto _start;
}
else
{
uint8_t v___x_546_; 
v___x_546_ = 1;
return v___x_546_;
}
}
else
{
uint8_t v___x_547_; 
v___x_547_ = 0;
return v___x_547_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_536_ = stack[0].m_obj;
size_t v_i_537_ = stack[1].m_num;
size_t v_stop_538_ = stack[2].m_num;
uint8_t v_res_548_;
v_res_548_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__2(v_as_536_, v_i_537_, v_stop_538_);
stack->m_num = v_res_548_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__2___boxed(lean_object* v_as_549_, lean_object* v_i_550_, lean_object* v_stop_551_){
_start:
{
size_t v_i_boxed_552_; size_t v_stop_boxed_553_; uint8_t v_res_554_; lean_object* v_r_555_; 
v_i_boxed_552_ = lean_unbox_usize(v_i_550_);
lean_dec(v_i_550_);
v_stop_boxed_553_ = lean_unbox_usize(v_stop_551_);
lean_dec(v_stop_551_);
v_res_554_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__2(v_as_549_, v_i_boxed_552_, v_stop_boxed_553_);
lean_dec_ref(v_as_549_);
v_r_555_ = lean_box(v_res_554_);
return v_r_555_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__1(size_t v_sz_556_, size_t v_i_557_, lean_object* v_bs_558_){
_start:
{
uint8_t v___x_559_; 
v___x_559_ = lean_usize_dec_lt(v_i_557_, v_sz_556_);
if (v___x_559_ == 0)
{
return v_bs_558_;
}
else
{
lean_object* v_v_560_; lean_object* v_fst_561_; lean_object* v___x_562_; lean_object* v_bs_x27_563_; size_t v___x_564_; size_t v___x_565_; lean_object* v___x_566_; 
v_v_560_ = lean_array_uget_borrowed(v_bs_558_, v_i_557_);
v_fst_561_ = lean_ctor_get(v_v_560_, 0);
lean_inc(v_fst_561_);
v___x_562_ = lean_unsigned_to_nat(0u);
v_bs_x27_563_ = lean_array_uset(v_bs_558_, v_i_557_, v___x_562_);
v___x_564_ = ((size_t)1ULL);
v___x_565_ = lean_usize_add(v_i_557_, v___x_564_);
v___x_566_ = lean_array_uset(v_bs_x27_563_, v_i_557_, v_fst_561_);
v_i_557_ = v___x_565_;
v_bs_558_ = v___x_566_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_556_ = stack[0].m_num;
size_t v_i_557_ = stack[1].m_num;
lean_object* v_bs_558_ = stack[2].m_obj;
lean_object* v_res_568_;
v_res_568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__1(v_sz_556_, v_i_557_, v_bs_558_);
stack->m_obj
 = v_res_568_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__1___boxed(lean_object* v_sz_569_, lean_object* v_i_570_, lean_object* v_bs_571_){
_start:
{
size_t v_sz_boxed_572_; size_t v_i_boxed_573_; lean_object* v_res_574_; 
v_sz_boxed_572_ = lean_unbox_usize(v_sz_569_);
lean_dec(v_sz_569_);
v_i_boxed_573_ = lean_unbox_usize(v_i_570_);
lean_dec(v_i_570_);
v_res_574_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__1(v_sz_boxed_572_, v_i_boxed_573_, v_bs_571_);
return v_res_574_;
}
}
lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go(lean_object* v_p_575_, lean_object* v_t_576_, lean_object* v_a_577_, lean_object* v_a_578_){
_start:
{
lean_object* v___x_580_; 
lean_inc_ref(v_p_575_);
lean_inc(v_a_578_);
lean_inc_ref(v_a_577_);
lean_inc_ref(v_t_576_);
v___x_580_ = lean_apply_4(v_p_575_, v_t_576_, v_a_577_, v_a_578_, lean_box(0));
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_627_; 
v_a_581_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_627_ == 0)
{
v___x_583_ = v___x_580_;
v_isShared_584_ = v_isSharedCheck_627_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_580_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_627_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
uint8_t v___x_585_; 
v___x_585_ = lean_unbox(v_a_581_);
if (v___x_585_ == 0)
{
lean_object* v___f_586_; lean_object* v___x_587_; size_t v_sz_588_; size_t v___x_589_; lean_object* v___x_590_; 
lean_del_object(v___x_583_);
v___f_586_ = lean_alloc_closure((void*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go___lam__0___boxed), 2, 1);
lean_closure_set(v___f_586_, 0, v_a_581_);
v___x_587_ = l_Lean_PostprocessTraces_TraceTree_children(v_t_576_);
v_sz_588_ = lean_array_size(v___x_587_);
v___x_589_ = ((size_t)0ULL);
v___x_590_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__0(v_p_575_, v_sz_588_, v___x_589_, v___x_587_, v_a_577_, v_a_578_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_614_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_614_ == 0)
{
v___x_593_ = v___x_590_;
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_590_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_614_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
uint8_t v___y_596_; lean_object* v___y_597_; uint8_t v___y_604_; lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v___x_609_ = lean_unsigned_to_nat(0u);
v___x_610_ = lean_array_get_size(v_a_591_);
v___x_611_ = lean_nat_dec_lt(v___x_609_, v___x_610_);
if (v___x_611_ == 0)
{
v___y_604_ = v___x_611_;
goto v___jp_603_;
}
else
{
if (v___x_611_ == 0)
{
v___y_604_ = v___x_611_;
goto v___jp_603_;
}
else
{
size_t v___x_612_; uint8_t v___x_613_; 
v___x_612_ = lean_usize_of_nat(v___x_610_);
v___x_613_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__2(v_a_591_, v___x_589_, v___x_612_);
v___y_604_ = v___x_613_;
goto v___jp_603_;
}
}
v___jp_595_:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_598_ = lean_box(v___y_596_);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v___y_597_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_599_);
v___x_601_ = v___x_593_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_599_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
v___jp_603_:
{
size_t v_sz_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v_sz_605_ = lean_array_size(v_a_591_);
v___x_606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__1(v_sz_605_, v___x_589_, v_a_591_);
v___x_607_ = l_Lean_PostprocessTraces_TraceTree_withChildren(v_t_576_, v___x_606_);
if (v___y_604_ == 0)
{
lean_dec_ref(v___f_586_);
v___y_596_ = v___y_604_;
v___y_597_ = v___x_607_;
goto v___jp_595_;
}
else
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_PostprocessTraces_TraceTree_modifyData(v___x_607_, v___f_586_);
v___y_596_ = v___y_604_;
v___y_597_ = v___x_608_;
goto v___jp_595_;
}
}
}
}
else
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_622_; 
lean_dec_ref(v___f_586_);
lean_dec_ref(v_t_576_);
v_a_615_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_622_ == 0)
{
v___x_617_ = v___x_590_;
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_590_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_622_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_620_; 
if (v_isShared_618_ == 0)
{
v___x_620_ = v___x_617_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
else
{
lean_object* v___x_623_; lean_object* v___x_625_; 
lean_dec_ref(v_p_575_);
v___x_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_623_, 0, v_t_576_);
lean_ctor_set(v___x_623_, 1, v_a_581_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_623_);
v___x_625_ = v___x_583_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
}
else
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_635_; 
lean_dec_ref(v_t_576_);
lean_dec_ref(v_p_575_);
v_a_628_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_635_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_635_ == 0)
{
v___x_630_ = v___x_580_;
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_580_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_635_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v___x_633_; 
if (v_isShared_631_ == 0)
{
v___x_633_ = v___x_630_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_575_ = stack[0].m_obj;
lean_object* v_t_576_ = stack[1].m_obj;
lean_object* v_a_577_ = stack[2].m_obj;
lean_object* v_a_578_ = stack[3].m_obj;
lean_object* v_res_636_;
v_res_636_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go(v_p_575_, v_t_576_, v_a_577_, v_a_578_);
stack->m_obj
 = v_res_636_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__0(lean_object* v_p_637_, size_t v_sz_638_, size_t v_i_639_, lean_object* v_bs_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
uint8_t v___x_644_; 
v___x_644_ = lean_usize_dec_lt(v_i_639_, v_sz_638_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; 
lean_dec_ref(v_p_637_);
v___x_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_645_, 0, v_bs_640_);
return v___x_645_;
}
else
{
lean_object* v_v_646_; lean_object* v___x_647_; lean_object* v_bs_x27_648_; lean_object* v___x_649_; 
v_v_646_ = lean_array_uget(v_bs_640_, v_i_639_);
v___x_647_ = lean_unsigned_to_nat(0u);
v_bs_x27_648_ = lean_array_uset(v_bs_640_, v_i_639_, v___x_647_);
lean_inc_ref(v_p_637_);
v___x_649_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go(v_p_637_, v_v_646_, v___y_641_, v___y_642_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_a_650_; size_t v___x_651_; size_t v___x_652_; lean_object* v___x_653_; 
v_a_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_a_650_);
lean_dec_ref_known(v___x_649_, 1);
v___x_651_ = ((size_t)1ULL);
v___x_652_ = lean_usize_add(v_i_639_, v___x_651_);
v___x_653_ = lean_array_uset(v_bs_x27_648_, v_i_639_, v_a_650_);
v_i_639_ = v___x_652_;
v_bs_640_ = v___x_653_;
goto _start;
}
else
{
lean_object* v_a_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_662_; 
lean_dec_ref(v_bs_x27_648_);
lean_dec_ref(v_p_637_);
v_a_655_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_662_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_662_ == 0)
{
v___x_657_ = v___x_649_;
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_a_655_);
lean_dec(v___x_649_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_662_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_660_; 
if (v_isShared_658_ == 0)
{
v___x_660_ = v___x_657_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_a_655_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_637_ = stack[0].m_obj;
size_t v_sz_638_ = stack[1].m_num;
size_t v_i_639_ = stack[2].m_num;
lean_object* v_bs_640_ = stack[3].m_obj;
lean_object* v___y_641_ = stack[4].m_obj;
lean_object* v___y_642_ = stack[5].m_obj;
lean_object* v_res_663_;
v_res_663_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__0(v_p_637_, v_sz_638_, v_i_639_, v_bs_640_, v___y_641_, v___y_642_);
stack->m_obj
 = v_res_663_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__0___boxed(lean_object* v_p_664_, lean_object* v_sz_665_, lean_object* v_i_666_, lean_object* v_bs_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
size_t v_sz_boxed_671_; size_t v_i_boxed_672_; lean_object* v_res_673_; 
v_sz_boxed_671_ = lean_unbox_usize(v_sz_665_);
lean_dec(v_sz_665_);
v_i_boxed_672_ = lean_unbox_usize(v_i_666_);
lean_dec(v_i_666_);
v_res_673_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go_spec__0(v_p_664_, v_sz_boxed_671_, v_i_boxed_672_, v_bs_667_, v___y_668_, v___y_669_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go___boxed(lean_object* v_p_674_, lean_object* v_t_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go(v_p_674_, v_t_675_, v_a_676_, v_a_677_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
return v_res_679_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_exposeSubtrees_spec__0(lean_object* v_p_680_, size_t v_sz_681_, size_t v_i_682_, lean_object* v_bs_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
uint8_t v___x_687_; 
v___x_687_ = lean_usize_dec_lt(v_i_682_, v_sz_681_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; 
lean_dec_ref(v_p_680_);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v_bs_683_);
return v___x_688_;
}
else
{
lean_object* v_v_689_; lean_object* v___x_690_; lean_object* v_bs_x27_691_; lean_object* v___x_692_; 
v_v_689_ = lean_array_uget(v_bs_683_, v_i_682_);
v___x_690_ = lean_unsigned_to_nat(0u);
v_bs_x27_691_ = lean_array_uset(v_bs_683_, v_i_682_, v___x_690_);
lean_inc_ref(v_p_680_);
v___x_692_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_exposeSubtrees_go(v_p_680_, v_v_689_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v_fst_694_; size_t v___x_695_; size_t v___x_696_; lean_object* v___x_697_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_692_, 1);
v_fst_694_ = lean_ctor_get(v_a_693_, 0);
lean_inc(v_fst_694_);
lean_dec(v_a_693_);
v___x_695_ = ((size_t)1ULL);
v___x_696_ = lean_usize_add(v_i_682_, v___x_695_);
v___x_697_ = lean_array_uset(v_bs_x27_691_, v_i_682_, v_fst_694_);
v_i_682_ = v___x_696_;
v_bs_683_ = v___x_697_;
goto _start;
}
else
{
lean_object* v_a_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_706_; 
lean_dec_ref(v_bs_x27_691_);
lean_dec_ref(v_p_680_);
v_a_699_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_706_ == 0)
{
v___x_701_ = v___x_692_;
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_a_699_);
lean_dec(v___x_692_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_706_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v___x_704_; 
if (v_isShared_702_ == 0)
{
v___x_704_ = v___x_701_;
goto v_reusejp_703_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v_a_699_);
v___x_704_ = v_reuseFailAlloc_705_;
goto v_reusejp_703_;
}
v_reusejp_703_:
{
return v___x_704_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_exposeSubtrees_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_680_ = stack[0].m_obj;
size_t v_sz_681_ = stack[1].m_num;
size_t v_i_682_ = stack[2].m_num;
lean_object* v_bs_683_ = stack[3].m_obj;
lean_object* v___y_684_ = stack[4].m_obj;
lean_object* v___y_685_ = stack[5].m_obj;
lean_object* v_res_707_;
v_res_707_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_exposeSubtrees_spec__0(v_p_680_, v_sz_681_, v_i_682_, v_bs_683_, v___y_684_, v___y_685_);
stack->m_obj
 = v_res_707_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_exposeSubtrees_spec__0___boxed(lean_object* v_p_708_, lean_object* v_sz_709_, lean_object* v_i_710_, lean_object* v_bs_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
size_t v_sz_boxed_715_; size_t v_i_boxed_716_; lean_object* v_res_717_; 
v_sz_boxed_715_ = lean_unbox_usize(v_sz_709_);
lean_dec(v_sz_709_);
v_i_boxed_716_ = lean_unbox_usize(v_i_710_);
lean_dec(v_i_710_);
v_res_717_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_exposeSubtrees_spec__0(v_p_708_, v_sz_boxed_715_, v_i_boxed_716_, v_bs_711_, v___y_712_, v___y_713_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
return v_res_717_;
}
}
lean_object* l_Lean_PostprocessTraces_exposeSubtrees(lean_object* v_p_718_, lean_object* v_roots_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
size_t v_sz_723_; size_t v___x_724_; lean_object* v___x_725_; 
v_sz_723_ = lean_array_size(v_roots_719_);
v___x_724_ = ((size_t)0ULL);
v___x_725_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_exposeSubtrees_spec__0(v_p_718_, v_sz_723_, v___x_724_, v_roots_719_, v_a_720_, v_a_721_);
return v___x_725_;
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_exposeSubtrees_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_718_ = stack[0].m_obj;
lean_object* v_roots_719_ = stack[1].m_obj;
lean_object* v_a_720_ = stack[2].m_obj;
lean_object* v_a_721_ = stack[3].m_obj;
lean_object* v_res_726_;
v_res_726_ = l_Lean_PostprocessTraces_exposeSubtrees(v_p_718_, v_roots_719_, v_a_720_, v_a_721_);
stack->m_obj
 = v_res_726_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_exposeSubtrees___boxed(lean_object* v_p_727_, lean_object* v_roots_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_Lean_PostprocessTraces_exposeSubtrees(v_p_727_, v_roots_728_, v_a_729_, v_a_730_);
lean_dec(v_a_730_);
lean_dec_ref(v_a_729_);
return v_res_732_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__2(lean_object* v_as_733_, size_t v_i_734_, size_t v_stop_735_, lean_object* v_b_736_){
_start:
{
uint8_t v___x_737_; 
v___x_737_ = lean_usize_dec_eq(v_i_734_, v_stop_735_);
if (v___x_737_ == 0)
{
lean_object* v___x_738_; lean_object* v_snd_739_; lean_object* v___x_740_; size_t v___x_741_; size_t v___x_742_; 
v___x_738_ = lean_array_uget_borrowed(v_as_733_, v_i_734_);
v_snd_739_ = lean_ctor_get(v___x_738_, 1);
v___x_740_ = lean_nat_add(v_b_736_, v_snd_739_);
lean_dec(v_b_736_);
v___x_741_ = ((size_t)1ULL);
v___x_742_ = lean_usize_add(v_i_734_, v___x_741_);
v_i_734_ = v___x_742_;
v_b_736_ = v___x_740_;
goto _start;
}
else
{
return v_b_736_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_733_ = stack[0].m_obj;
size_t v_i_734_ = stack[1].m_num;
size_t v_stop_735_ = stack[2].m_num;
lean_object* v_b_736_ = stack[3].m_obj;
lean_object* v_res_744_;
v_res_744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__2(v_as_733_, v_i_734_, v_stop_735_, v_b_736_);
stack->m_obj
 = v_res_744_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__2___boxed(lean_object* v_as_745_, lean_object* v_i_746_, lean_object* v_stop_747_, lean_object* v_b_748_){
_start:
{
size_t v_i_boxed_749_; size_t v_stop_boxed_750_; lean_object* v_res_751_; 
v_i_boxed_749_ = lean_unbox_usize(v_i_746_);
lean_dec(v_i_746_);
v_stop_boxed_750_ = lean_unbox_usize(v_stop_747_);
lean_dec(v_stop_747_);
v_res_751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__2(v_as_745_, v_i_boxed_749_, v_stop_boxed_750_, v_b_748_);
lean_dec_ref(v_as_745_);
return v_res_751_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__1(size_t v_sz_752_, size_t v_i_753_, lean_object* v_bs_754_){
_start:
{
uint8_t v___x_755_; 
v___x_755_ = lean_usize_dec_lt(v_i_753_, v_sz_752_);
if (v___x_755_ == 0)
{
return v_bs_754_;
}
else
{
lean_object* v_v_756_; lean_object* v_fst_757_; lean_object* v___x_758_; lean_object* v_bs_x27_759_; size_t v___x_760_; size_t v___x_761_; lean_object* v___x_762_; 
v_v_756_ = lean_array_uget_borrowed(v_bs_754_, v_i_753_);
v_fst_757_ = lean_ctor_get(v_v_756_, 0);
lean_inc(v_fst_757_);
v___x_758_ = lean_unsigned_to_nat(0u);
v_bs_x27_759_ = lean_array_uset(v_bs_754_, v_i_753_, v___x_758_);
v___x_760_ = ((size_t)1ULL);
v___x_761_ = lean_usize_add(v_i_753_, v___x_760_);
v___x_762_ = lean_array_uset(v_bs_x27_759_, v_i_753_, v_fst_757_);
v_i_753_ = v___x_761_;
v_bs_754_ = v___x_762_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_752_ = stack[0].m_num;
size_t v_i_753_ = stack[1].m_num;
lean_object* v_bs_754_ = stack[2].m_obj;
lean_object* v_res_764_;
v_res_764_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__1(v_sz_752_, v_i_753_, v_bs_754_);
stack->m_obj
 = v_res_764_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__1___boxed(lean_object* v_sz_765_, lean_object* v_i_766_, lean_object* v_bs_767_){
_start:
{
size_t v_sz_boxed_768_; size_t v_i_boxed_769_; lean_object* v_res_770_; 
v_sz_boxed_768_ = lean_unbox_usize(v_sz_765_);
lean_dec(v_sz_765_);
v_i_boxed_769_ = lean_unbox_usize(v_i_766_);
lean_dec(v_i_766_);
v_res_770_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__1(v_sz_boxed_768_, v_i_boxed_769_, v_bs_767_);
return v_res_770_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__1(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__0));
v___x_773_ = l_Lean_stringToMessageData(v___x_772_);
return v___x_773_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__3(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__2));
v___x_776_ = l_Lean_stringToMessageData(v___x_775_);
return v___x_776_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__5(void){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__4));
v___x_779_ = l_Lean_stringToMessageData(v___x_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go(lean_object* v_a_782_){
_start:
{
if (lean_obj_tag(v_a_782_) == 0)
{
lean_object* v_data_783_; lean_object* v_msg_784_; lean_object* v_children_785_; lean_object* v_wrap_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_828_; 
v_data_783_ = lean_ctor_get(v_a_782_, 0);
v_msg_784_ = lean_ctor_get(v_a_782_, 1);
v_children_785_ = lean_ctor_get(v_a_782_, 2);
v_wrap_786_ = lean_ctor_get(v_a_782_, 3);
v_isSharedCheck_828_ = !lean_is_exclusive(v_a_782_);
if (v_isSharedCheck_828_ == 0)
{
v___x_788_ = v_a_782_;
v_isShared_789_ = v_isSharedCheck_828_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_wrap_786_);
lean_inc(v_children_785_);
lean_inc(v_msg_784_);
lean_inc(v_data_783_);
lean_dec(v_a_782_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_828_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
size_t v_sz_790_; size_t v___x_791_; lean_object* v_results_792_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___x_814_; lean_object* v___y_816_; lean_object* v___x_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v_sz_790_ = lean_array_size(v_children_785_);
v___x_791_ = ((size_t)0ULL);
v_results_792_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__0(v_sz_790_, v___x_791_, v_children_785_);
v___x_814_ = lean_unsigned_to_nat(1u);
v___x_820_ = lean_unsigned_to_nat(0u);
v___x_821_ = lean_array_get_size(v_results_792_);
v___x_822_ = lean_nat_dec_lt(v___x_820_, v___x_821_);
if (v___x_822_ == 0)
{
v___y_816_ = v___x_814_;
goto v___jp_815_;
}
else
{
uint8_t v___x_823_; 
v___x_823_ = lean_nat_dec_le(v___x_821_, v___x_821_);
if (v___x_823_ == 0)
{
if (v___x_822_ == 0)
{
v___y_816_ = v___x_814_;
goto v___jp_815_;
}
else
{
size_t v___x_824_; lean_object* v___x_825_; 
v___x_824_ = lean_usize_of_nat(v___x_821_);
v___x_825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__2(v_results_792_, v___x_791_, v___x_824_, v___x_814_);
v___y_816_ = v___x_825_;
goto v___jp_815_;
}
}
else
{
size_t v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_usize_of_nat(v___x_821_);
v___x_827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__2(v_results_792_, v___x_791_, v___x_826_, v___x_814_);
v___y_816_ = v___x_827_;
goto v___jp_815_;
}
}
v___jp_793_:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; size_t v_sz_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_796_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__1, &l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__1_once, _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__1);
v___x_797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_797_, 0, v_msg_784_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
lean_inc(v___y_794_);
v___x_798_ = l_Nat_reprFast(v___y_794_);
v___x_799_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_799_, 0, v___x_798_);
v___x_800_ = l_Lean_MessageData_ofFormat(v___x_799_);
v___x_801_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_801_, 0, v___x_797_);
lean_ctor_set(v___x_801_, 1, v___x_800_);
v___x_802_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__3, &l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__3_once, _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__3);
v___x_803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_801_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
lean_inc_ref(v___y_795_);
v___x_804_ = l_Lean_stringToMessageData(v___y_795_);
v___x_805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_803_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v___x_806_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__5, &l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__5_once, _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__5);
v___x_807_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_805_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v_sz_808_ = lean_array_size(v_results_792_);
v___x_809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__1(v_sz_808_, v___x_791_, v_results_792_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 2, v___x_809_);
lean_ctor_set(v___x_788_, 1, v___x_807_);
v___x_811_ = v___x_788_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_data_783_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_813_, 3, v_wrap_786_);
v___x_811_ = v_reuseFailAlloc_813_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_812_; 
v___x_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
lean_ctor_set(v___x_812_, 1, v___y_794_);
return v___x_812_;
}
}
v___jp_815_:
{
uint8_t v___x_817_; 
v___x_817_ = lean_nat_dec_eq(v___y_816_, v___x_814_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; 
v___x_818_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__6));
v___y_794_ = v___y_816_;
v___y_795_ = v___x_818_;
goto v___jp_793_;
}
else
{
lean_object* v___x_819_; 
v___x_819_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__7));
v___y_794_ = v___y_816_;
v___y_795_ = v___x_819_;
goto v___jp_793_;
}
}
}
}
else
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = lean_unsigned_to_nat(1u);
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v_a_782_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
return v___x_830_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__0(size_t v_sz_831_, size_t v_i_832_, lean_object* v_bs_833_){
_start:
{
uint8_t v___x_834_; 
v___x_834_ = lean_usize_dec_lt(v_i_832_, v_sz_831_);
if (v___x_834_ == 0)
{
return v_bs_833_;
}
else
{
lean_object* v_v_835_; lean_object* v___x_836_; lean_object* v_bs_x27_837_; lean_object* v___x_838_; size_t v___x_839_; size_t v___x_840_; lean_object* v___x_841_; 
v_v_835_ = lean_array_uget(v_bs_833_, v_i_832_);
v___x_836_ = lean_unsigned_to_nat(0u);
v_bs_x27_837_ = lean_array_uset(v_bs_833_, v_i_832_, v___x_836_);
v___x_838_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go(v_v_835_);
v___x_839_ = ((size_t)1ULL);
v___x_840_ = lean_usize_add(v_i_832_, v___x_839_);
v___x_841_ = lean_array_uset(v_bs_x27_837_, v_i_832_, v___x_838_);
v_i_832_ = v___x_840_;
v_bs_833_ = v___x_841_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_831_ = stack[0].m_num;
size_t v_i_832_ = stack[1].m_num;
lean_object* v_bs_833_ = stack[2].m_obj;
lean_object* v_res_843_;
v_res_843_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__0(v_sz_831_, v_i_832_, v_bs_833_);
stack->m_obj
 = v_res_843_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__0___boxed(lean_object* v_sz_844_, lean_object* v_i_845_, lean_object* v_bs_846_){
_start:
{
size_t v_sz_boxed_847_; size_t v_i_boxed_848_; lean_object* v_res_849_; 
v_sz_boxed_847_ = lean_unbox_usize(v_sz_844_);
lean_dec(v_sz_844_);
v_i_boxed_848_ = lean_unbox_usize(v_i_845_);
lean_dec(v_i_845_);
v_res_849_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go_spec__0(v_sz_boxed_847_, v_i_boxed_848_, v_bs_846_);
return v_res_849_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_countNodes_spec__0(size_t v_sz_850_, size_t v_i_851_, lean_object* v_bs_852_){
_start:
{
uint8_t v___x_853_; 
v___x_853_ = lean_usize_dec_lt(v_i_851_, v_sz_850_);
if (v___x_853_ == 0)
{
return v_bs_852_;
}
else
{
lean_object* v_v_854_; lean_object* v___x_855_; lean_object* v_fst_856_; lean_object* v___x_857_; lean_object* v_bs_x27_858_; size_t v___x_859_; size_t v___x_860_; lean_object* v___x_861_; 
v_v_854_ = lean_array_uget_borrowed(v_bs_852_, v_i_851_);
lean_inc(v_v_854_);
v___x_855_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go(v_v_854_);
v_fst_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_fst_856_);
lean_dec_ref(v___x_855_);
v___x_857_ = lean_unsigned_to_nat(0u);
v_bs_x27_858_ = lean_array_uset(v_bs_852_, v_i_851_, v___x_857_);
v___x_859_ = ((size_t)1ULL);
v___x_860_ = lean_usize_add(v_i_851_, v___x_859_);
v___x_861_ = lean_array_uset(v_bs_x27_858_, v_i_851_, v_fst_856_);
v_i_851_ = v___x_860_;
v_bs_852_ = v___x_861_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_countNodes_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_850_ = stack[0].m_num;
size_t v_i_851_ = stack[1].m_num;
lean_object* v_bs_852_ = stack[2].m_obj;
lean_object* v_res_863_;
v_res_863_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_countNodes_spec__0(v_sz_850_, v_i_851_, v_bs_852_);
stack->m_obj
 = v_res_863_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_countNodes_spec__0___boxed(lean_object* v_sz_864_, lean_object* v_i_865_, lean_object* v_bs_866_){
_start:
{
size_t v_sz_boxed_867_; size_t v_i_boxed_868_; lean_object* v_res_869_; 
v_sz_boxed_867_ = lean_unbox_usize(v_sz_864_);
lean_dec(v_sz_864_);
v_i_boxed_868_ = lean_unbox_usize(v_i_865_);
lean_dec(v_i_865_);
v_res_869_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_countNodes_spec__0(v_sz_boxed_867_, v_i_boxed_868_, v_bs_866_);
return v_res_869_;
}
}
lean_object* l_Lean_PostprocessTraces_countNodes___redArg(lean_object* v_roots_870_){
_start:
{
size_t v_sz_872_; size_t v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v_sz_872_ = lean_array_size(v_roots_870_);
v___x_873_ = ((size_t)0ULL);
v___x_874_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_countNodes_spec__0(v_sz_872_, v___x_873_, v_roots_870_);
v___x_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_875_, 0, v___x_874_);
return v___x_875_;
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_countNodes___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_roots_870_ = stack[0].m_obj;
lean_object* v_res_876_;
v_res_876_ = l_Lean_PostprocessTraces_countNodes___redArg(v_roots_870_);
stack->m_obj
 = v_res_876_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_countNodes___redArg___boxed(lean_object* v_roots_877_, lean_object* v_a_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Lean_PostprocessTraces_countNodes___redArg(v_roots_877_);
return v_res_879_;
}
}
lean_object* l_Lean_PostprocessTraces_countNodes(lean_object* v_roots_880_, lean_object* v_a_881_, lean_object* v_a_882_){
_start:
{
lean_object* v___x_884_; 
v___x_884_ = l_Lean_PostprocessTraces_countNodes___redArg(v_roots_880_);
return v___x_884_;
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_countNodes_0interp(lean_interpreter_value* stack)
{
lean_object* v_roots_880_ = stack[0].m_obj;
lean_object* v_a_881_ = stack[1].m_obj;
lean_object* v_a_882_ = stack[2].m_obj;
lean_object* v_res_885_;
v_res_885_ = l_Lean_PostprocessTraces_countNodes(v_roots_880_, v_a_881_, v_a_882_);
stack->m_obj
 = v_res_885_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_countNodes___boxed(lean_object* v_roots_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_PostprocessTraces_countNodes(v_roots_886_, v_a_887_, v_a_888_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
return v_res_890_;
}
}
static double _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__0(void){
_start:
{
lean_object* v___x_891_; double v___x_892_; 
v___x_891_ = lean_unsigned_to_nat(10u);
v___x_892_ = lean_float_of_nat(v___x_891_);
return v___x_892_;
}
}
lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs(double v_ms_895_){
_start:
{
lean_object* v___x_896_; double v___x_897_; double v___x_898_; double v___x_899_; uint64_t v___x_900_; lean_object* v_tenths_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_896_ = lean_unsigned_to_nat(10u);
v___x_897_ = lean_float_once(&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__0, &l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__0_once, _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__0);
v___x_898_ = lean_float_mul(v_ms_895_, v___x_897_);
v___x_899_ = round(v___x_898_);
v___x_900_ = lean_float_to_uint64(v___x_899_);
v_tenths_901_ = lean_uint64_to_nat(v___x_900_);
v___x_902_ = lean_nat_div(v_tenths_901_, v___x_896_);
v___x_903_ = l_Nat_reprFast(v___x_902_);
v___x_904_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__1));
v___x_905_ = lean_string_append(v___x_903_, v___x_904_);
v___x_906_ = lean_nat_mod(v_tenths_901_, v___x_896_);
lean_dec(v_tenths_901_);
v___x_907_ = l_Nat_reprFast(v___x_906_);
v___x_908_ = lean_string_append(v___x_905_, v___x_907_);
lean_dec_ref(v___x_907_);
v___x_909_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___closed__2));
v___x_910_ = lean_string_append(v___x_908_, v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT void l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs_0interp(lean_interpreter_value* stack)
{
double v_ms_895_ = stack[0].m_float;
lean_object* v_res_911_;
v_res_911_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs(v_ms_895_);
stack->m_obj
 = v_res_911_;
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs___boxed(lean_object* v_ms_912_){
_start:
{
double v_ms_boxed_913_; lean_object* v_res_914_; 
v_ms_boxed_913_ = lean_unbox_float(v_ms_912_);
lean_dec_ref(v_ms_912_);
v_res_914_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs(v_ms_boxed_913_);
return v_res_914_;
}
}
static double _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__0(void){
_start:
{
lean_object* v___x_915_; double v___x_916_; 
v___x_915_ = lean_unsigned_to_nat(0u);
v___x_916_ = lean_float_of_nat(v___x_915_);
return v___x_916_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__2(void){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = ((lean_object*)(l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__1));
v___x_919_ = l_Lean_stringToMessageData(v___x_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go(lean_object* v_a_920_){
_start:
{
if (lean_obj_tag(v_a_920_) == 0)
{
lean_object* v_data_921_; lean_object* v_msg_922_; lean_object* v_children_923_; lean_object* v_wrap_924_; lean_object* v___y_926_; double v_startTime_931_; double v___x_932_; uint8_t v___x_933_; 
v_data_921_ = lean_ctor_get(v_a_920_, 0);
lean_inc_ref(v_data_921_);
v_msg_922_ = lean_ctor_get(v_a_920_, 1);
v_children_923_ = lean_ctor_get(v_a_920_, 2);
lean_inc_ref(v_children_923_);
v_wrap_924_ = lean_ctor_get(v_a_920_, 3);
lean_inc_ref(v_wrap_924_);
v_startTime_931_ = lean_ctor_get_float(v_data_921_, sizeof(void*)*3);
v___x_932_ = lean_float_once(&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__0, &l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__0_once, _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__0);
v___x_933_ = lean_float_beq(v_startTime_931_, v___x_932_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; double v___x_936_; double v___x_937_; double v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_934_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__2, &l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__2_once, _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go___closed__2);
lean_inc_ref(v_msg_922_);
v___x_935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_935_, 0, v_msg_922_);
lean_ctor_set(v___x_935_, 1, v___x_934_);
v___x_936_ = l_Lean_PostprocessTraces_TraceTree_selfElapsed(v_a_920_);
lean_dec_ref_known(v_a_920_, 4);
v___x_937_ = lean_float_once(&l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0, &l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0_once, _init_l_Lean_PostprocessTraces_minTimeMs___redArg___closed__0);
v___x_938_ = lean_float_mul(v___x_936_, v___x_937_);
v___x_939_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_formatMs(v___x_938_);
v___x_940_ = l_Lean_stringToMessageData(v___x_939_);
v___x_941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_935_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = lean_obj_once(&l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__5, &l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__5_once, _init_l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_countNodes_go___closed__5);
v___x_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_943_, 0, v___x_941_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
v___y_926_ = v___x_943_;
goto v___jp_925_;
}
else
{
lean_inc_ref(v_msg_922_);
lean_dec_ref_known(v_a_920_, 4);
v___y_926_ = v_msg_922_;
goto v___jp_925_;
}
v___jp_925_:
{
size_t v_sz_927_; size_t v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v_sz_927_ = lean_array_size(v_children_923_);
v___x_928_ = ((size_t)0ULL);
v___x_929_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go_spec__0(v_sz_927_, v___x_928_, v_children_923_);
v___x_930_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_930_, 0, v_data_921_);
lean_ctor_set(v___x_930_, 1, v___y_926_);
lean_ctor_set(v___x_930_, 2, v___x_929_);
lean_ctor_set(v___x_930_, 3, v_wrap_924_);
return v___x_930_;
}
}
else
{
return v_a_920_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go_spec__0(size_t v_sz_944_, size_t v_i_945_, lean_object* v_bs_946_){
_start:
{
uint8_t v___x_947_; 
v___x_947_ = lean_usize_dec_lt(v_i_945_, v_sz_944_);
if (v___x_947_ == 0)
{
return v_bs_946_;
}
else
{
lean_object* v_v_948_; lean_object* v___x_949_; lean_object* v_bs_x27_950_; lean_object* v___x_951_; size_t v___x_952_; size_t v___x_953_; lean_object* v___x_954_; 
v_v_948_ = lean_array_uget(v_bs_946_, v_i_945_);
v___x_949_ = lean_unsigned_to_nat(0u);
v_bs_x27_950_ = lean_array_uset(v_bs_946_, v_i_945_, v___x_949_);
v___x_951_ = l___private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go(v_v_948_);
v___x_952_ = ((size_t)1ULL);
v___x_953_ = lean_usize_add(v_i_945_, v___x_952_);
v___x_954_ = lean_array_uset(v_bs_x27_950_, v_i_945_, v___x_951_);
v_i_945_ = v___x_953_;
v_bs_946_ = v___x_954_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_944_ = stack[0].m_num;
size_t v_i_945_ = stack[1].m_num;
lean_object* v_bs_946_ = stack[2].m_obj;
lean_object* v_res_956_;
v_res_956_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go_spec__0(v_sz_944_, v_i_945_, v_bs_946_);
stack->m_obj
 = v_res_956_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go_spec__0___boxed(lean_object* v_sz_957_, lean_object* v_i_958_, lean_object* v_bs_959_){
_start:
{
size_t v_sz_boxed_960_; size_t v_i_boxed_961_; lean_object* v_res_962_; 
v_sz_boxed_960_ = lean_unbox_usize(v_sz_957_);
lean_dec(v_sz_957_);
v_i_boxed_961_ = lean_unbox_usize(v_i_958_);
lean_dec(v_i_958_);
v_res_962_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go_spec__0(v_sz_boxed_960_, v_i_boxed_961_, v_bs_959_);
return v_res_962_;
}
}
lean_object* l_Lean_PostprocessTraces_selfTime___redArg(lean_object* v_roots_963_){
_start:
{
size_t v_sz_965_; size_t v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_sz_965_ = lean_array_size(v_roots_963_);
v___x_966_ = ((size_t)0ULL);
v___x_967_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_PostprocessTraces_Postprocessors_0__Lean_PostprocessTraces_selfTime_go_spec__0(v_sz_965_, v___x_966_, v_roots_963_);
v___x_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
return v___x_968_;
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_selfTime___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_roots_963_ = stack[0].m_obj;
lean_object* v_res_969_;
v_res_969_ = l_Lean_PostprocessTraces_selfTime___redArg(v_roots_963_);
stack->m_obj
 = v_res_969_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_selfTime___redArg___boxed(lean_object* v_roots_970_, lean_object* v_a_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_PostprocessTraces_selfTime___redArg(v_roots_970_);
return v_res_972_;
}
}
lean_object* l_Lean_PostprocessTraces_selfTime(lean_object* v_roots_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Lean_PostprocessTraces_selfTime___redArg(v_roots_973_);
return v___x_977_;
}
}
LEAN_EXPORT void l_Lean_PostprocessTraces_selfTime_0interp(lean_interpreter_value* stack)
{
lean_object* v_roots_973_ = stack[0].m_obj;
lean_object* v_a_974_ = stack[1].m_obj;
lean_object* v_a_975_ = stack[2].m_obj;
lean_object* v_res_978_;
v_res_978_ = l_Lean_PostprocessTraces_selfTime(v_roots_973_, v_a_974_, v_a_975_);
stack->m_obj
 = v_res_978_;
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_selfTime___boxed(lean_object* v_roots_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_PostprocessTraces_selfTime(v_roots_979_, v_a_980_, v_a_981_);
lean_dec(v_a_981_);
lean_dec_ref(v_a_980_);
return v_res_983_;
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
