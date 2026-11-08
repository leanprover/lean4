// Lean compiler output
// Module: Lean.Data.Markdown.Parser.Emphasis
// Imports: import Init.While import Init.Data.Vector.Basic public import Lean.Data.Markdown.Inline public import Lean.Data.Markdown.InlineCursor
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
lean_object* l_Lean_Markdown_instInhabitedInline_default(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_InlineSource_linesBetween(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* l_Fin_mul(lean_object*, lean_object*, lean_object*);
lean_object* l_Fin_add(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Markdown_subsliceClamped___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_delimiterSubslice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_delimiterSubslice___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Markdown_instInhabitedDelimSequence_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(65, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Markdown_instInhabitedDelimSequence_default___redArg___closed__0 = (const lean_object*)&l_Lean_Markdown_instInhabitedDelimSequence_default___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedDelimSequence_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedDelimSequence_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Markdown_instInhabitedDelimSequence_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_instInhabitedDelimSequence_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedDelimSequence_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedDelimSequence_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedDelimSequence___redArg();
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedDelimSequence___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedDelimSequence(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedDelimSequence___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_ctorIdx___impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_ctorIdx___impl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_inline_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_inline_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_inline_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_delim_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_delim_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_delim_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineTok_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineTok_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineTok(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineTok___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_pushTokText___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_pushTokText(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_pushTokText___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Markdown_instInhabitedOpenerFrame_default___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(65, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Markdown_instInhabitedOpenerFrame_default___redArg___closed__0 = (const lean_object*)&l_Lean_Markdown_instInhabitedOpenerFrame_default___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenerFrame_default___redArg();
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenerFrame_default___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_Markdown_instInhabitedOpenerFrame_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Markdown_instInhabitedOpenerFrame_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenerFrame_default(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenerFrame_default___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_instInhabitedOpenerFrame___redArg();
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_instInhabitedOpenerFrame___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_instInhabitedOpenerFrame(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_instInhabitedOpenerFrame___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_bottomKey___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_bottomKey___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_bottomKey(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_bottomKey___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg___closed__0 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg___closed__1;
static lean_once_cell_t l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg();
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_coalesceText_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_coalesceText_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_coalesceText(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_coalesceText___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_coalesceText_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_coalesceText_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_emit___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_emit(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_emit___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_openDelimiter_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_openDelimiter_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_openDelimiter___redArg(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_openDelimiter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_openDelimiter(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_openDelimiter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_abandonOpener___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_abandonOpener(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_abandonOpener___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_closeMatched_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_closeMatched_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_closeMatched___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_closeMatched___redArg___closed__0 = (const lean_object*)&l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_closeMatched___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_closeMatched___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_closeMatched___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_closeMatched(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_closeMatched___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_finalizeEmphasis___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_finalizeEmphasis___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_finalizeEmphasis(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_finalizeEmphasis___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processMathSequence_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processMathSequence_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processMathSequence_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processMathSequence_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processMathSequence(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processMathSequence___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Markdown_processEmphasis_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Markdown_processEmphasis_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_processEmphasis(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Markdown_processEmphasis___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_delimiterSubslice(lean_object* v_s_1_, lean_object* v_p_2_, lean_object* v_n_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; 
lean_inc(v_p_2_);
v___x_4_ = l_String_Slice_Pos_nextn(v_s_1_, v_p_2_, v_n_3_);
v___x_5_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5_, 0, v_p_2_);
lean_ctor_set(v___x_5_, 1, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_delimiterSubslice___boxed(lean_object* v_s_6_, lean_object* v_p_7_, lean_object* v_n_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_delimiterSubslice(v_s_6_, v_p_7_, v_n_8_);
lean_dec_ref(v_s_6_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedDelimSequence_default___redArg(){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = ((lean_object*)(l_Lean_Markdown_instInhabitedDelimSequence_default___redArg___closed__0));
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedDelimSequence_default___redArg___boxed(lean_object* v___dummy_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l_Lean_Markdown_instInhabitedDelimSequence_default___redArg();
return v_res_17_;
}
}
static lean_object* _init_l_Lean_Markdown_instInhabitedDelimSequence_default___closed__0(void){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Markdown_instInhabitedDelimSequence_default___redArg();
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedDelimSequence_default(lean_object* v_s_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_obj_once(&l_Lean_Markdown_instInhabitedDelimSequence_default___closed__0, &l_Lean_Markdown_instInhabitedDelimSequence_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedDelimSequence_default___closed__0);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedDelimSequence_default___boxed(lean_object* v_s_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Lean_Markdown_instInhabitedDelimSequence_default(v_s_21_);
lean_dec_ref(v_s_21_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedDelimSequence___redArg(){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_obj_once(&l_Lean_Markdown_instInhabitedDelimSequence_default___closed__0, &l_Lean_Markdown_instInhabitedDelimSequence_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedDelimSequence_default___closed__0);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedDelimSequence___redArg___boxed(lean_object* v___dummy_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Markdown_instInhabitedDelimSequence___redArg();
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedDelimSequence(lean_object* v_a_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lean_obj_once(&l_Lean_Markdown_instInhabitedDelimSequence_default___closed__0, &l_Lean_Markdown_instInhabitedDelimSequence_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedDelimSequence_default___closed__0);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedDelimSequence___boxed(lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_Markdown_instInhabitedDelimSequence(v_a_29_);
lean_dec_ref(v_a_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_ctorIdx___impl___redArg(lean_object* v_x_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = lean_obj_tag_nat(v_x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_ctorIdx___impl___redArg___boxed(lean_object* v_x_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Markdown_InlineTok_ctorIdx___impl___redArg(v_x_33_);
lean_dec_ref(v_x_33_);
return v_res_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_ctorIdx___impl(lean_object* v_s_35_, lean_object* v_x_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_obj_tag_nat(v_x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_ctorIdx___impl___boxed(lean_object* v_s_38_, lean_object* v_x_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Markdown_InlineTok_ctorIdx___impl(v_s_38_, v_x_39_);
lean_dec_ref(v_x_39_);
lean_dec_ref(v_s_38_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_ctorElim___redArg(lean_object* v_t_41_, lean_object* v_k_42_){
_start:
{
lean_object* v_i_43_; lean_object* v___x_44_; 
v_i_43_ = lean_ctor_get(v_t_41_, 0);
lean_inc_ref(v_i_43_);
lean_dec_ref(v_t_41_);
v___x_44_ = lean_apply_1(v_k_42_, v_i_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_ctorElim(lean_object* v_s_45_, lean_object* v_motive_46_, lean_object* v_ctorIdx_47_, lean_object* v_t_48_, lean_object* v_h_49_, lean_object* v_k_50_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_Markdown_InlineTok_ctorElim___redArg(v_t_48_, v_k_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_ctorElim___boxed(lean_object* v_s_52_, lean_object* v_motive_53_, lean_object* v_ctorIdx_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_k_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Lean_Markdown_InlineTok_ctorElim(v_s_52_, v_motive_53_, v_ctorIdx_54_, v_t_55_, v_h_56_, v_k_57_);
lean_dec(v_ctorIdx_54_);
lean_dec_ref(v_s_52_);
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_inline_elim___redArg(lean_object* v_t_59_, lean_object* v_inline_60_){
_start:
{
lean_object* v___x_61_; 
v___x_61_ = l_Lean_Markdown_InlineTok_ctorElim___redArg(v_t_59_, v_inline_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_inline_elim(lean_object* v_s_62_, lean_object* v_motive_63_, lean_object* v_t_64_, lean_object* v_h_65_, lean_object* v_inline_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Markdown_InlineTok_ctorElim___redArg(v_t_64_, v_inline_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_inline_elim___boxed(lean_object* v_s_68_, lean_object* v_motive_69_, lean_object* v_t_70_, lean_object* v_h_71_, lean_object* v_inline_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_Markdown_InlineTok_inline_elim(v_s_68_, v_motive_69_, v_t_70_, v_h_71_, v_inline_72_);
lean_dec_ref(v_s_68_);
return v_res_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_delim_elim___redArg(lean_object* v_t_74_, lean_object* v_delim_75_){
_start:
{
lean_object* v___x_76_; 
v___x_76_ = l_Lean_Markdown_InlineTok_ctorElim___redArg(v_t_74_, v_delim_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_delim_elim(lean_object* v_s_77_, lean_object* v_motive_78_, lean_object* v_t_79_, lean_object* v_h_80_, lean_object* v_delim_81_){
_start:
{
lean_object* v___x_82_; 
v___x_82_ = l_Lean_Markdown_InlineTok_ctorElim___redArg(v_t_79_, v_delim_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_InlineTok_delim_elim___boxed(lean_object* v_s_83_, lean_object* v_motive_84_, lean_object* v_t_85_, lean_object* v_h_86_, lean_object* v_delim_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Markdown_InlineTok_delim_elim(v_s_83_, v_motive_84_, v_t_85_, v_h_86_, v_delim_87_);
lean_dec_ref(v_s_83_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineTok_default(lean_object* v_s_89_){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_90_ = l_Lean_Markdown_instInhabitedInline_default(v_s_89_);
v___x_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineTok_default___boxed(lean_object* v_s_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_Markdown_instInhabitedInlineTok_default(v_s_92_);
lean_dec_ref(v_s_92_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineTok(lean_object* v_a_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_Markdown_instInhabitedInlineTok_default(v_a_94_);
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedInlineTok___boxed(lean_object* v_a_96_){
_start:
{
lean_object* v_res_97_; 
v_res_97_ = l_Lean_Markdown_instInhabitedInlineTok(v_a_96_);
lean_dec_ref(v_a_96_);
return v_res_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_pushTokText___redArg(lean_object* v_out_98_, lean_object* v_textStart_99_, lean_object* v_pos_100_){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_101_ = lean_unsigned_to_nat(1u);
v___x_102_ = lean_nat_add(v_textStart_99_, v___x_101_);
v___x_103_ = lean_nat_dec_le(v___x_102_, v_pos_100_);
lean_dec(v___x_102_);
if (v___x_103_ == 0)
{
lean_dec(v_pos_100_);
lean_dec(v_textStart_99_);
return v_out_98_;
}
else
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_104_ = l_Lean_Markdown_subsliceClamped___redArg(v_textStart_99_, v_pos_100_);
v___x_105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
v___x_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
v___x_107_ = lean_array_push(v_out_98_, v___x_106_);
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_pushTokText(lean_object* v_s_108_, lean_object* v_out_109_, lean_object* v_textStart_110_, lean_object* v_pos_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_Markdown_pushTokText___redArg(v_out_109_, v_textStart_110_, v_pos_111_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_pushTokText___boxed(lean_object* v_s_113_, lean_object* v_out_114_, lean_object* v_textStart_115_, lean_object* v_pos_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Markdown_pushTokText(v_s_113_, v_out_114_, v_textStart_115_, v_pos_116_);
lean_dec_ref(v_s_113_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenerFrame_default___redArg(){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = ((lean_object*)(l_Lean_Markdown_instInhabitedOpenerFrame_default___redArg___closed__0));
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenerFrame_default___redArg___boxed(lean_object* v___dummy_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Markdown_instInhabitedOpenerFrame_default___redArg();
return v_res_125_;
}
}
static lean_object* _init_l_Lean_Markdown_instInhabitedOpenerFrame_default___closed__0(void){
_start:
{
lean_object* v___x_126_; 
v___x_126_ = l_Lean_Markdown_instInhabitedOpenerFrame_default___redArg();
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenerFrame_default(lean_object* v_s_127_){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = lean_obj_once(&l_Lean_Markdown_instInhabitedOpenerFrame_default___closed__0, &l_Lean_Markdown_instInhabitedOpenerFrame_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedOpenerFrame_default___closed__0);
return v___x_128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_instInhabitedOpenerFrame_default___boxed(lean_object* v_s_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Markdown_instInhabitedOpenerFrame_default(v_s_129_);
lean_dec_ref(v_s_129_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_instInhabitedOpenerFrame___redArg(){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lean_obj_once(&l_Lean_Markdown_instInhabitedOpenerFrame_default___closed__0, &l_Lean_Markdown_instInhabitedOpenerFrame_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedOpenerFrame_default___closed__0);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_instInhabitedOpenerFrame___redArg___boxed(lean_object* v___dummy_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_instInhabitedOpenerFrame___redArg();
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_instInhabitedOpenerFrame(lean_object* v_a_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = lean_obj_once(&l_Lean_Markdown_instInhabitedOpenerFrame_default___closed__0, &l_Lean_Markdown_instInhabitedOpenerFrame_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedOpenerFrame_default___closed__0);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_instInhabitedOpenerFrame___boxed(lean_object* v_a_137_){
_start:
{
lean_object* v_res_138_; 
v_res_138_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_instInhabitedOpenerFrame(v_a_137_);
lean_dec_ref(v_a_137_);
return v_res_138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_bottomKey___redArg(lean_object* v_seq_139_){
_start:
{
uint32_t v_ch_140_; lean_object* v_origLen_141_; uint8_t v_canOpen_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v_lenMod3_145_; lean_object* v___y_147_; uint32_t v___x_155_; uint8_t v___x_156_; 
v_ch_140_ = lean_ctor_get_uint32(v_seq_139_, sizeof(void*)*2);
v_origLen_141_ = lean_ctor_get(v_seq_139_, 1);
v_canOpen_142_ = lean_ctor_get_uint8(v_seq_139_, sizeof(void*)*2 + 4);
v___x_143_ = lean_unsigned_to_nat(12u);
v___x_144_ = lean_unsigned_to_nat(3u);
v_lenMod3_145_ = lean_nat_mod(v_origLen_141_, v___x_144_);
v___x_155_ = 42;
v___x_156_ = lean_uint32_dec_eq(v_ch_140_, v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; 
v___x_157_ = lean_unsigned_to_nat(6u);
v___y_147_ = v___x_157_;
goto v___jp_146_;
}
else
{
lean_object* v___x_158_; 
v___x_158_ = lean_unsigned_to_nat(0u);
v___y_147_ = v___x_158_;
goto v___jp_146_;
}
v___jp_146_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_unsigned_to_nat(2u);
v___x_149_ = l_Fin_mul(v___x_143_, v_lenMod3_145_, v___x_148_);
lean_dec(v_lenMod3_145_);
v___x_150_ = l_Fin_add(v___x_143_, v___y_147_, v___x_149_);
lean_dec(v___x_149_);
if (v_canOpen_142_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = l_Fin_add(v___x_143_, v___x_150_, v___x_151_);
lean_dec(v___x_150_);
return v___x_152_;
}
else
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(1u);
v___x_154_ = l_Fin_add(v___x_143_, v___x_150_, v___x_153_);
lean_dec(v___x_150_);
return v___x_154_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_bottomKey___redArg___boxed(lean_object* v_seq_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_bottomKey___redArg(v_seq_159_);
lean_dec_ref(v_seq_159_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_bottomKey(lean_object* v_s_161_, lean_object* v_seq_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_bottomKey___redArg(v_seq_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_bottomKey___boxed(lean_object* v_s_164_, lean_object* v_seq_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_bottomKey(v_s_164_, v_seq_165_);
lean_dec_ref(v_seq_165_);
lean_dec_ref(v_s_164_);
return v_res_166_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg___closed__1(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = lean_unsigned_to_nat(12u);
v___x_171_ = lean_mk_array(v___x_170_, v___x_169_);
return v___x_171_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg___closed__2(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg___closed__1, &l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg___closed__1_once, _init_l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg___closed__1);
v___x_173_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg___closed__0));
v___x_174_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
lean_ctor_set(v___x_174_, 2, v___x_173_);
lean_ctor_set(v___x_174_, 3, v___x_172_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg(){
_start:
{
lean_object* v___x_176_; 
v___x_176_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg___closed__2, &l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg___closed__2_once, _init_l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg___closed__2);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg___boxed(lean_object* v___dummy_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg();
return v_res_178_;
}
}
static lean_object* _init_l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___closed__0(void){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg();
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty(lean_object* v_s_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___closed__0, &l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___closed__0);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___boxed(lean_object* v_s_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty(v_s_182_);
lean_dec_ref(v_s_182_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_coalesceText_spec__0___redArg(lean_object* v_as_184_, size_t v_i_185_, size_t v_stop_186_, lean_object* v_b_187_){
_start:
{
lean_object* v___y_189_; uint8_t v___x_193_; 
v___x_193_ = lean_usize_dec_eq(v_i_185_, v_stop_186_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; 
v___x_194_ = lean_array_uget_borrowed(v_as_184_, v_i_185_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_range_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v_range_195_ = lean_ctor_get(v___x_194_, 0);
v___x_196_ = lean_array_get_size(v_b_187_);
v___x_197_ = lean_unsigned_to_nat(1u);
v___x_198_ = lean_nat_sub(v___x_196_, v___x_197_);
v___x_199_ = lean_nat_dec_lt(v___x_198_, v___x_196_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; 
lean_dec(v___x_198_);
lean_inc_ref(v___x_194_);
v___x_200_ = lean_array_push(v_b_187_, v___x_194_);
v___y_189_ = v___x_200_;
goto v___jp_188_;
}
else
{
lean_object* v___x_201_; 
v___x_201_ = lean_array_fget(v_b_187_, v___x_198_);
lean_dec(v___x_198_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_object* v_range_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_218_; 
v_range_202_ = lean_ctor_get(v___x_201_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_201_);
if (v_isSharedCheck_218_ == 0)
{
v___x_204_ = v___x_201_;
v_isShared_205_ = v_isSharedCheck_218_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_range_202_);
lean_dec(v___x_201_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_218_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v_startInclusive_206_; lean_object* v_endExclusive_207_; lean_object* v_startInclusive_208_; lean_object* v_endExclusive_209_; uint8_t v_decide_210_; 
v_startInclusive_206_ = lean_ctor_get(v_range_202_, 0);
lean_inc(v_startInclusive_206_);
v_endExclusive_207_ = lean_ctor_get(v_range_202_, 1);
lean_inc(v_endExclusive_207_);
lean_dec_ref(v_range_202_);
v_startInclusive_208_ = lean_ctor_get(v_range_195_, 0);
v_endExclusive_209_ = lean_ctor_get(v_range_195_, 1);
v_decide_210_ = lean_nat_dec_eq(v_endExclusive_207_, v_startInclusive_208_);
lean_dec(v_endExclusive_207_);
if (v_decide_210_ == 0)
{
lean_object* v___x_211_; 
lean_dec(v_startInclusive_206_);
lean_del_object(v___x_204_);
lean_inc_ref(v___x_194_);
v___x_211_ = lean_array_push(v_b_187_, v___x_194_);
v___y_189_ = v___x_211_;
goto v___jp_188_;
}
else
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_215_; 
v___x_212_ = lean_array_pop(v_b_187_);
lean_inc(v_endExclusive_209_);
v___x_213_ = l_Lean_Markdown_subsliceClamped___redArg(v_startInclusive_206_, v_endExclusive_209_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 0, v___x_213_);
v___x_215_ = v___x_204_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v___x_213_);
v___x_215_ = v_reuseFailAlloc_217_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v___x_216_; 
v___x_216_ = lean_array_push(v___x_212_, v___x_215_);
v___y_189_ = v___x_216_;
goto v___jp_188_;
}
}
}
}
else
{
lean_object* v___x_219_; 
lean_dec(v___x_201_);
lean_inc_ref(v___x_194_);
v___x_219_ = lean_array_push(v_b_187_, v___x_194_);
v___y_189_ = v___x_219_;
goto v___jp_188_;
}
}
}
else
{
lean_object* v___x_220_; 
lean_inc(v___x_194_);
v___x_220_ = lean_array_push(v_b_187_, v___x_194_);
v___y_189_ = v___x_220_;
goto v___jp_188_;
}
}
else
{
return v_b_187_;
}
v___jp_188_:
{
size_t v___x_190_; size_t v___x_191_; 
v___x_190_ = ((size_t)1ULL);
v___x_191_ = lean_usize_add(v_i_185_, v___x_190_);
v_i_185_ = v___x_191_;
v_b_187_ = v___y_189_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_coalesceText_spec__0___redArg___boxed(lean_object* v_as_221_, lean_object* v_i_222_, lean_object* v_stop_223_, lean_object* v_b_224_){
_start:
{
size_t v_i_boxed_225_; size_t v_stop_boxed_226_; lean_object* v_res_227_; 
v_i_boxed_225_ = lean_unbox_usize(v_i_222_);
lean_dec(v_i_222_);
v_stop_boxed_226_ = lean_unbox_usize(v_stop_223_);
lean_dec(v_stop_223_);
v_res_227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_coalesceText_spec__0___redArg(v_as_221_, v_i_boxed_225_, v_stop_boxed_226_, v_b_224_);
lean_dec_ref(v_as_221_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_coalesceText(lean_object* v_s_228_, lean_object* v_inlines_229_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_230_ = lean_array_get_size(v_inlines_229_);
v___x_231_ = lean_mk_empty_array_with_capacity(v___x_230_);
v___x_232_ = lean_unsigned_to_nat(0u);
v___x_233_ = lean_nat_dec_lt(v___x_232_, v___x_230_);
if (v___x_233_ == 0)
{
return v___x_231_;
}
else
{
size_t v___x_234_; size_t v___x_235_; lean_object* v___x_236_; 
v___x_234_ = ((size_t)0ULL);
v___x_235_ = lean_usize_of_nat(v___x_230_);
v___x_236_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_coalesceText_spec__0___redArg(v_inlines_229_, v___x_234_, v___x_235_, v___x_231_);
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_coalesceText___boxed(lean_object* v_s_237_, lean_object* v_inlines_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_coalesceText(v_s_237_, v_inlines_238_);
lean_dec_ref(v_inlines_238_);
lean_dec_ref(v_s_237_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_coalesceText_spec__0(lean_object* v_s_240_, lean_object* v_as_241_, size_t v_i_242_, size_t v_stop_243_, lean_object* v_b_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_coalesceText_spec__0___redArg(v_as_241_, v_i_242_, v_stop_243_, v_b_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_coalesceText_spec__0___boxed(lean_object* v_s_246_, lean_object* v_as_247_, lean_object* v_i_248_, lean_object* v_stop_249_, lean_object* v_b_250_){
_start:
{
size_t v_i_boxed_251_; size_t v_stop_boxed_252_; lean_object* v_res_253_; 
v_i_boxed_251_ = lean_unbox_usize(v_i_248_);
lean_dec(v_i_248_);
v_stop_boxed_252_ = lean_unbox_usize(v_stop_249_);
lean_dec(v_stop_249_);
v_res_253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_coalesceText_spec__0(v_s_246_, v_as_247_, v_i_boxed_251_, v_stop_boxed_252_, v_b_250_);
lean_dec_ref(v_as_247_);
lean_dec_ref(v_s_246_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_emit___redArg(lean_object* v_inl_254_, lean_object* v_a_255_){
_start:
{
lean_object* v_delimiters_256_; lean_object* v_output_257_; lean_object* v_mathOpeners_258_; lean_object* v_openersBottom_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_269_; 
v_delimiters_256_ = lean_ctor_get(v_a_255_, 0);
v_output_257_ = lean_ctor_get(v_a_255_, 1);
v_mathOpeners_258_ = lean_ctor_get(v_a_255_, 2);
v_openersBottom_259_ = lean_ctor_get(v_a_255_, 3);
v_isSharedCheck_269_ = !lean_is_exclusive(v_a_255_);
if (v_isSharedCheck_269_ == 0)
{
v___x_261_ = v_a_255_;
v_isShared_262_ = v_isSharedCheck_269_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_openersBottom_259_);
lean_inc(v_mathOpeners_258_);
lean_inc(v_output_257_);
lean_inc(v_delimiters_256_);
lean_dec(v_a_255_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_269_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_263_ = lean_box(0);
v___x_264_ = lean_array_push(v_output_257_, v_inl_254_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v___x_264_);
v___x_266_ = v___x_261_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_delimiters_256_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v___x_264_);
lean_ctor_set(v_reuseFailAlloc_268_, 2, v_mathOpeners_258_);
lean_ctor_set(v_reuseFailAlloc_268_, 3, v_openersBottom_259_);
v___x_266_ = v_reuseFailAlloc_268_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_267_; 
v___x_267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_263_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
return v___x_267_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_emit(lean_object* v_s_270_, lean_object* v_inl_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_emit___redArg(v_inl_271_, v_a_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_emit___boxed(lean_object* v_s_275_, lean_object* v_inl_276_, lean_object* v_a_277_, lean_object* v_a_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_emit(v_s_275_, v_inl_276_, v_a_277_, v_a_278_);
lean_dec_ref(v_a_277_);
lean_dec_ref(v_s_275_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_openDelimiter_spec__0(lean_object* v_size_280_, size_t v_sz_281_, size_t v_i_282_, lean_object* v_bs_283_){
_start:
{
uint8_t v___x_284_; 
v___x_284_ = lean_usize_dec_lt(v_i_282_, v_sz_281_);
if (v___x_284_ == 0)
{
lean_dec(v_size_280_);
return v_bs_283_;
}
else
{
lean_object* v_v_285_; lean_object* v___x_286_; lean_object* v_bs_x27_287_; lean_object* v___y_289_; uint8_t v___x_294_; 
v_v_285_ = lean_array_uget(v_bs_283_, v_i_282_);
v___x_286_ = lean_unsigned_to_nat(0u);
v_bs_x27_287_ = lean_array_uset(v_bs_283_, v_i_282_, v___x_286_);
v___x_294_ = lean_nat_dec_le(v_v_285_, v_size_280_);
if (v___x_294_ == 0)
{
lean_dec(v_v_285_);
lean_inc(v_size_280_);
v___y_289_ = v_size_280_;
goto v___jp_288_;
}
else
{
v___y_289_ = v_v_285_;
goto v___jp_288_;
}
v___jp_288_:
{
size_t v___x_290_; size_t v___x_291_; lean_object* v___x_292_; 
v___x_290_ = ((size_t)1ULL);
v___x_291_ = lean_usize_add(v_i_282_, v___x_290_);
v___x_292_ = lean_array_uset(v_bs_x27_287_, v_i_282_, v___y_289_);
v_i_282_ = v___x_291_;
v_bs_283_ = v___x_292_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_openDelimiter_spec__0___boxed(lean_object* v_size_295_, lean_object* v_sz_296_, lean_object* v_i_297_, lean_object* v_bs_298_){
_start:
{
size_t v_sz_boxed_299_; size_t v_i_boxed_300_; lean_object* v_res_301_; 
v_sz_boxed_299_ = lean_unbox_usize(v_sz_296_);
lean_dec(v_sz_296_);
v_i_boxed_300_ = lean_unbox_usize(v_i_297_);
lean_dec(v_i_297_);
v_res_301_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_openDelimiter_spec__0(v_size_295_, v_sz_boxed_299_, v_i_boxed_300_, v_bs_298_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_openDelimiter___redArg(lean_object* v_s_302_, uint32_t v_ch_303_, lean_object* v_startPos_304_, lean_object* v_origLen_305_, lean_object* v_remaining_306_, uint8_t v_canClose_307_, lean_object* v_a_308_){
_start:
{
lean_object* v_delimiters_309_; lean_object* v_output_310_; lean_object* v_mathOpeners_311_; lean_object* v_openersBottom_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_331_; 
v_delimiters_309_ = lean_ctor_get(v_a_308_, 0);
v_output_310_ = lean_ctor_get(v_a_308_, 1);
v_mathOpeners_311_ = lean_ctor_get(v_a_308_, 2);
v_openersBottom_312_ = lean_ctor_get(v_a_308_, 3);
v_isSharedCheck_331_ = !lean_is_exclusive(v_a_308_);
if (v_isSharedCheck_331_ == 0)
{
v___x_314_ = v_a_308_;
v_isShared_315_ = v_isSharedCheck_331_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_openersBottom_312_);
lean_inc(v_mathOpeners_311_);
lean_inc(v_output_310_);
lean_inc(v_delimiters_309_);
lean_dec(v_a_308_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_331_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v_size_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; size_t v_sz_324_; size_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_316_ = lean_box(0);
v_size_317_ = lean_array_get_size(v_delimiters_309_);
v___x_318_ = lean_array_get_size(v_output_310_);
lean_inc(v_remaining_306_);
lean_inc(v_startPos_304_);
v___x_319_ = lean_alloc_ctor(0, 4, 5);
lean_ctor_set(v___x_319_, 0, v_startPos_304_);
lean_ctor_set(v___x_319_, 1, v_origLen_305_);
lean_ctor_set(v___x_319_, 2, v_remaining_306_);
lean_ctor_set(v___x_319_, 3, v___x_318_);
lean_ctor_set_uint32(v___x_319_, sizeof(void*)*4, v_ch_303_);
lean_ctor_set_uint8(v___x_319_, sizeof(void*)*4 + 4, v_canClose_307_);
v___x_320_ = lean_array_push(v_delimiters_309_, v___x_319_);
v___x_321_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_delimiterSubslice(v_s_302_, v_startPos_304_, v_remaining_306_);
v___x_322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
v___x_323_ = lean_array_push(v_output_310_, v___x_322_);
v_sz_324_ = lean_array_size(v_openersBottom_312_);
v___x_325_ = ((size_t)0ULL);
v___x_326_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_openDelimiter_spec__0(v_size_317_, v_sz_324_, v___x_325_, v_openersBottom_312_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 3, v___x_326_);
lean_ctor_set(v___x_314_, 1, v___x_323_);
lean_ctor_set(v___x_314_, 0, v___x_320_);
v___x_328_ = v___x_314_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_320_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v___x_323_);
lean_ctor_set(v_reuseFailAlloc_330_, 2, v_mathOpeners_311_);
lean_ctor_set(v_reuseFailAlloc_330_, 3, v___x_326_);
v___x_328_ = v_reuseFailAlloc_330_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; 
v___x_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_316_);
lean_ctor_set(v___x_329_, 1, v___x_328_);
return v___x_329_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_openDelimiter___redArg___boxed(lean_object* v_s_332_, lean_object* v_ch_333_, lean_object* v_startPos_334_, lean_object* v_origLen_335_, lean_object* v_remaining_336_, lean_object* v_canClose_337_, lean_object* v_a_338_){
_start:
{
uint32_t v_ch_boxed_339_; uint8_t v_canClose_boxed_340_; lean_object* v_res_341_; 
v_ch_boxed_339_ = lean_unbox_uint32(v_ch_333_);
lean_dec(v_ch_333_);
v_canClose_boxed_340_ = lean_unbox(v_canClose_337_);
v_res_341_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_openDelimiter___redArg(v_s_332_, v_ch_boxed_339_, v_startPos_334_, v_origLen_335_, v_remaining_336_, v_canClose_boxed_340_, v_a_338_);
lean_dec_ref(v_s_332_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_openDelimiter(lean_object* v_s_342_, uint32_t v_ch_343_, lean_object* v_startPos_344_, lean_object* v_origLen_345_, lean_object* v_remaining_346_, uint8_t v_canClose_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v___x_350_; 
v___x_350_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_openDelimiter___redArg(v_s_342_, v_ch_343_, v_startPos_344_, v_origLen_345_, v_remaining_346_, v_canClose_347_, v_a_349_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_openDelimiter___boxed(lean_object* v_s_351_, lean_object* v_ch_352_, lean_object* v_startPos_353_, lean_object* v_origLen_354_, lean_object* v_remaining_355_, lean_object* v_canClose_356_, lean_object* v_a_357_, lean_object* v_a_358_){
_start:
{
uint32_t v_ch_boxed_359_; uint8_t v_canClose_boxed_360_; lean_object* v_res_361_; 
v_ch_boxed_359_ = lean_unbox_uint32(v_ch_352_);
lean_dec(v_ch_352_);
v_canClose_boxed_360_ = lean_unbox(v_canClose_356_);
v_res_361_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_openDelimiter(v_s_351_, v_ch_boxed_359_, v_startPos_353_, v_origLen_354_, v_remaining_355_, v_canClose_boxed_360_, v_a_357_, v_a_358_);
lean_dec_ref(v_a_357_);
lean_dec_ref(v_s_351_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_abandonOpener___redArg(lean_object* v_a_362_){
_start:
{
lean_object* v_delimiters_363_; lean_object* v_output_364_; lean_object* v_mathOpeners_365_; lean_object* v_openersBottom_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_376_; 
v_delimiters_363_ = lean_ctor_get(v_a_362_, 0);
v_output_364_ = lean_ctor_get(v_a_362_, 1);
v_mathOpeners_365_ = lean_ctor_get(v_a_362_, 2);
v_openersBottom_366_ = lean_ctor_get(v_a_362_, 3);
v_isSharedCheck_376_ = !lean_is_exclusive(v_a_362_);
if (v_isSharedCheck_376_ == 0)
{
v___x_368_ = v_a_362_;
v_isShared_369_ = v_isSharedCheck_376_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_openersBottom_366_);
lean_inc(v_mathOpeners_365_);
lean_inc(v_output_364_);
lean_inc(v_delimiters_363_);
lean_dec(v_a_362_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_376_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_370_ = lean_box(0);
v___x_371_ = lean_array_pop(v_delimiters_363_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 0, v___x_371_);
v___x_373_ = v___x_368_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_output_364_);
lean_ctor_set(v_reuseFailAlloc_375_, 2, v_mathOpeners_365_);
lean_ctor_set(v_reuseFailAlloc_375_, 3, v_openersBottom_366_);
v___x_373_ = v_reuseFailAlloc_375_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; 
v___x_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_370_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
return v___x_374_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_abandonOpener(lean_object* v_s_377_, lean_object* v_a_378_, lean_object* v_a_379_){
_start:
{
lean_object* v___x_380_; 
v___x_380_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_abandonOpener___redArg(v_a_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_abandonOpener___boxed(lean_object* v_s_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_abandonOpener(v_s_381_, v_a_382_, v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec_ref(v_s_381_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_closeMatched_spec__0(lean_object* v___x_385_, lean_object* v_as_386_, size_t v_i_387_, size_t v_stop_388_, lean_object* v_b_389_){
_start:
{
lean_object* v___y_391_; uint8_t v___x_395_; 
v___x_395_ = lean_usize_dec_eq(v_i_387_, v_stop_388_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v_snd_397_; lean_object* v_snd_398_; uint8_t v___x_399_; 
v___x_396_ = lean_array_uget_borrowed(v_as_386_, v_i_387_);
v_snd_397_ = lean_ctor_get(v___x_396_, 1);
v_snd_398_ = lean_ctor_get(v_snd_397_, 1);
v___x_399_ = lean_nat_dec_le(v_snd_398_, v___x_385_);
if (v___x_399_ == 0)
{
v___y_391_ = v_b_389_;
goto v___jp_390_;
}
else
{
lean_object* v___x_400_; 
lean_inc(v___x_396_);
v___x_400_ = lean_array_push(v_b_389_, v___x_396_);
v___y_391_ = v___x_400_;
goto v___jp_390_;
}
}
else
{
return v_b_389_;
}
v___jp_390_:
{
size_t v___x_392_; size_t v___x_393_; 
v___x_392_ = ((size_t)1ULL);
v___x_393_ = lean_usize_add(v_i_387_, v___x_392_);
v_i_387_ = v___x_393_;
v_b_389_ = v___y_391_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_closeMatched_spec__0___boxed(lean_object* v___x_401_, lean_object* v_as_402_, lean_object* v_i_403_, lean_object* v_stop_404_, lean_object* v_b_405_){
_start:
{
size_t v_i_boxed_406_; size_t v_stop_boxed_407_; lean_object* v_res_408_; 
v_i_boxed_406_ = lean_unbox_usize(v_i_403_);
lean_dec(v_i_403_);
v_stop_boxed_407_ = lean_unbox_usize(v_stop_404_);
lean_dec(v_stop_404_);
v_res_408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_closeMatched_spec__0(v___x_401_, v_as_402_, v_i_boxed_406_, v_stop_boxed_407_, v_b_405_);
lean_dec_ref(v_as_402_);
lean_dec(v___x_401_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_closeMatched___redArg(lean_object* v_s_411_, lean_object* v_matchLen_412_, lean_object* v_openDelim_413_, lean_object* v_closeDelim_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_delimiters_416_; lean_object* v_output_417_; lean_object* v_mathOpeners_418_; lean_object* v_openersBottom_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_483_; 
v_delimiters_416_ = lean_ctor_get(v_a_415_, 0);
v_output_417_ = lean_ctor_get(v_a_415_, 1);
v_mathOpeners_418_ = lean_ctor_get(v_a_415_, 2);
v_openersBottom_419_ = lean_ctor_get(v_a_415_, 3);
v_isSharedCheck_483_ = !lean_is_exclusive(v_a_415_);
if (v_isSharedCheck_483_ == 0)
{
v___x_421_ = v_a_415_;
v_isShared_422_ = v_isSharedCheck_483_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_openersBottom_419_);
lean_inc(v_mathOpeners_418_);
lean_inc(v_output_417_);
lean_inc(v_delimiters_416_);
lean_dec(v_a_415_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_483_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; uint32_t v_ch_428_; lean_object* v_startPos_429_; lean_object* v_origLen_430_; lean_object* v_remaining_431_; uint8_t v_canClose_432_; lean_object* v_outIdx_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_482_; 
v___x_423_ = lean_obj_once(&l_Lean_Markdown_instInhabitedOpenerFrame_default___closed__0, &l_Lean_Markdown_instInhabitedOpenerFrame_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedOpenerFrame_default___closed__0);
v___x_424_ = lean_array_get_size(v_delimiters_416_);
v___x_425_ = lean_unsigned_to_nat(1u);
v___x_426_ = lean_nat_sub(v___x_424_, v___x_425_);
v___x_427_ = lean_array_get(v___x_423_, v_delimiters_416_, v___x_426_);
lean_dec(v___x_426_);
v_ch_428_ = lean_ctor_get_uint32(v___x_427_, sizeof(void*)*4);
v_startPos_429_ = lean_ctor_get(v___x_427_, 0);
v_origLen_430_ = lean_ctor_get(v___x_427_, 1);
v_remaining_431_ = lean_ctor_get(v___x_427_, 2);
v_canClose_432_ = lean_ctor_get_uint8(v___x_427_, sizeof(void*)*4 + 4);
v_outIdx_433_ = lean_ctor_get(v___x_427_, 3);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_427_);
if (v_isSharedCheck_482_ == 0)
{
v___x_435_ = v___x_427_;
v_isShared_436_ = v_isSharedCheck_482_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_outIdx_433_);
lean_inc(v_remaining_431_);
lean_inc(v_origLen_430_);
lean_inc(v_startPos_429_);
lean_dec(v___x_427_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_482_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___y_441_; lean_object* v___y_442_; lean_object* v___y_443_; lean_object* v___y_467_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_437_ = lean_nat_sub(v_remaining_431_, v_matchLen_412_);
lean_dec(v_remaining_431_);
v___x_438_ = lean_box(0);
v___x_439_ = lean_nat_add(v_outIdx_433_, v___x_425_);
v___x_475_ = lean_array_get_size(v_output_417_);
lean_inc(v___x_439_);
v___x_476_ = l_Array_extract___redArg(v_output_417_, v___x_439_, v___x_475_);
v___x_477_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_coalesceText(v_s_411_, v___x_476_);
lean_dec_ref(v___x_476_);
v___x_478_ = lean_unsigned_to_nat(2u);
v___x_479_ = lean_nat_dec_eq(v_matchLen_412_, v___x_478_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; 
v___x_480_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_480_, 0, v_openDelim_413_);
lean_ctor_set(v___x_480_, 1, v___x_477_);
lean_ctor_set(v___x_480_, 2, v_closeDelim_414_);
v___y_467_ = v___x_480_;
goto v___jp_466_;
}
else
{
lean_object* v___x_481_; 
v___x_481_ = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(v___x_481_, 0, v_openDelim_413_);
lean_ctor_set(v___x_481_, 1, v___x_477_);
lean_ctor_set(v___x_481_, 2, v_closeDelim_414_);
v___y_467_ = v___x_481_;
goto v___jp_466_;
}
v___jp_440_:
{
uint8_t v___x_444_; 
v___x_444_ = lean_nat_dec_eq(v___x_437_, v___y_441_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_447_; 
v___x_445_ = lean_array_pop(v_delimiters_416_);
lean_inc(v_outIdx_433_);
lean_inc(v___x_437_);
lean_inc(v_startPos_429_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 2, v___x_437_);
v___x_447_ = v___x_435_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 4, 5);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_startPos_429_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_origLen_430_);
lean_ctor_set(v_reuseFailAlloc_458_, 2, v___x_437_);
lean_ctor_set(v_reuseFailAlloc_458_, 3, v_outIdx_433_);
lean_ctor_set_uint32(v_reuseFailAlloc_458_, sizeof(void*)*4, v_ch_428_);
lean_ctor_set_uint8(v_reuseFailAlloc_458_, sizeof(void*)*4 + 4, v_canClose_432_);
v___x_447_ = v_reuseFailAlloc_458_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_448_ = lean_array_push(v___x_445_, v___x_447_);
v___x_449_ = l_Array_shrink___redArg(v_output_417_, v___x_439_);
lean_dec(v___x_439_);
v___x_450_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_delimiterSubslice(v_s_411_, v_startPos_429_, v___x_437_);
v___x_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
v___x_452_ = lean_array_set(v___x_449_, v_outIdx_433_, v___x_451_);
lean_dec(v_outIdx_433_);
v___x_453_ = lean_array_push(v___x_452_, v___y_442_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 2, v___y_443_);
lean_ctor_set(v___x_421_, 1, v___x_453_);
lean_ctor_set(v___x_421_, 0, v___x_448_);
v___x_455_ = v___x_421_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_457_; 
v_reuseFailAlloc_457_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_457_, 0, v___x_448_);
lean_ctor_set(v_reuseFailAlloc_457_, 1, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_457_, 2, v___y_443_);
lean_ctor_set(v_reuseFailAlloc_457_, 3, v_openersBottom_419_);
v___x_455_ = v_reuseFailAlloc_457_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_456_; 
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v___x_438_);
lean_ctor_set(v___x_456_, 1, v___x_455_);
return v___x_456_;
}
}
}
else
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_463_; 
lean_dec(v___x_439_);
lean_dec(v___x_437_);
lean_del_object(v___x_435_);
lean_dec(v_origLen_430_);
lean_dec(v_startPos_429_);
v___x_459_ = lean_array_pop(v_delimiters_416_);
v___x_460_ = l_Array_shrink___redArg(v_output_417_, v_outIdx_433_);
lean_dec(v_outIdx_433_);
v___x_461_ = lean_array_push(v___x_460_, v___y_442_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 2, v___y_443_);
lean_ctor_set(v___x_421_, 1, v___x_461_);
lean_ctor_set(v___x_421_, 0, v___x_459_);
v___x_463_ = v___x_421_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v___y_443_);
lean_ctor_set(v_reuseFailAlloc_465_, 3, v_openersBottom_419_);
v___x_463_ = v_reuseFailAlloc_465_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; 
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_438_);
lean_ctor_set(v___x_464_, 1, v___x_463_);
return v___x_464_;
}
}
}
v___jp_466_:
{
lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_469_ = lean_array_get_size(v_mathOpeners_418_);
v___x_470_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_closeMatched___redArg___closed__0));
v___x_471_ = lean_nat_dec_lt(v___x_468_, v___x_469_);
if (v___x_471_ == 0)
{
lean_dec_ref(v_mathOpeners_418_);
v___y_441_ = v___x_468_;
v___y_442_ = v___y_467_;
v___y_443_ = v___x_470_;
goto v___jp_440_;
}
else
{
size_t v___x_472_; size_t v___x_473_; lean_object* v___x_474_; 
v___x_472_ = ((size_t)0ULL);
v___x_473_ = lean_usize_of_nat(v___x_469_);
v___x_474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_closeMatched_spec__0(v_outIdx_433_, v_mathOpeners_418_, v___x_472_, v___x_473_, v___x_470_);
lean_dec_ref(v_mathOpeners_418_);
v___y_441_ = v___x_468_;
v___y_442_ = v___y_467_;
v___y_443_ = v___x_474_;
goto v___jp_440_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_closeMatched___redArg___boxed(lean_object* v_s_484_, lean_object* v_matchLen_485_, lean_object* v_openDelim_486_, lean_object* v_closeDelim_487_, lean_object* v_a_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_closeMatched___redArg(v_s_484_, v_matchLen_485_, v_openDelim_486_, v_closeDelim_487_, v_a_488_);
lean_dec(v_matchLen_485_);
lean_dec_ref(v_s_484_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_closeMatched(lean_object* v_s_490_, lean_object* v_matchLen_491_, lean_object* v_openDelim_492_, lean_object* v_closeDelim_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_closeMatched___redArg(v_s_490_, v_matchLen_491_, v_openDelim_492_, v_closeDelim_493_, v_a_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_closeMatched___boxed(lean_object* v_s_497_, lean_object* v_matchLen_498_, lean_object* v_openDelim_499_, lean_object* v_closeDelim_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_closeMatched(v_s_497_, v_matchLen_498_, v_openDelim_499_, v_closeDelim_500_, v_a_501_, v_a_502_);
lean_dec_ref(v_a_501_);
lean_dec(v_matchLen_498_);
lean_dec_ref(v_s_497_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_finalizeEmphasis___redArg(lean_object* v_s_504_, lean_object* v_a_505_){
_start:
{
lean_object* v_output_506_; lean_object* v_mathOpeners_507_; lean_object* v_openersBottom_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_518_; 
v_output_506_ = lean_ctor_get(v_a_505_, 1);
v_mathOpeners_507_ = lean_ctor_get(v_a_505_, 2);
v_openersBottom_508_ = lean_ctor_get(v_a_505_, 3);
v_isSharedCheck_518_ = !lean_is_exclusive(v_a_505_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; 
v_unused_519_ = lean_ctor_get(v_a_505_, 0);
lean_dec(v_unused_519_);
v___x_510_ = v_a_505_;
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_openersBottom_508_);
lean_inc(v_mathOpeners_507_);
lean_inc(v_output_506_);
lean_dec(v_a_505_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_512_; lean_object* v___x_514_; 
v___x_512_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg___closed__0));
lean_inc_ref(v_output_506_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_512_);
v___x_514_ = v___x_510_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_512_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_output_506_);
lean_ctor_set(v_reuseFailAlloc_517_, 2, v_mathOpeners_507_);
lean_ctor_set(v_reuseFailAlloc_517_, 3, v_openersBottom_508_);
v___x_514_ = v_reuseFailAlloc_517_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_515_; lean_object* v___x_516_; 
v___x_515_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_coalesceText(v_s_504_, v_output_506_);
lean_dec_ref(v_output_506_);
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
lean_ctor_set(v___x_516_, 1, v___x_514_);
return v___x_516_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_finalizeEmphasis___redArg___boxed(lean_object* v_s_520_, lean_object* v_a_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_finalizeEmphasis___redArg(v_s_520_, v_a_521_);
lean_dec_ref(v_s_520_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_finalizeEmphasis(lean_object* v_s_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_finalizeEmphasis___redArg(v_s_523_, v_a_525_);
return v___x_526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_finalizeEmphasis___boxed(lean_object* v_s_527_, lean_object* v_a_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_res_530_; 
v_res_530_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_finalizeEmphasis(v_s_527_, v_a_528_, v_a_529_);
lean_dec_ref(v_a_528_);
lean_dec_ref(v_s_527_);
return v_res_530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener_spec__0___redArg(lean_object* v_bottom_533_, lean_object* v_stack_534_, lean_object* v_seq_535_, lean_object* v_a_536_){
_start:
{
lean_object* v_snd_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_581_; 
v_snd_537_ = lean_ctor_get(v_a_536_, 1);
v_isSharedCheck_581_ = !lean_is_exclusive(v_a_536_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; 
v_unused_582_ = lean_ctor_get(v_a_536_, 0);
lean_dec(v_unused_582_);
v___x_539_ = v_a_536_;
v_isShared_540_ = v_isSharedCheck_581_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_snd_537_);
lean_dec(v_a_536_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_581_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_541_ = lean_box(0);
v___x_542_ = lean_nat_dec_lt(v_bottom_533_, v_snd_537_);
if (v___x_542_ == 0)
{
lean_object* v___x_544_; 
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v___x_541_);
v___x_544_ = v___x_539_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_snd_537_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
else
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_546_ = lean_unsigned_to_nat(1u);
v___x_547_ = lean_nat_sub(v_snd_537_, v___x_546_);
lean_dec(v_snd_537_);
v___x_557_ = lean_array_get_size(v_stack_534_);
v___x_558_ = lean_nat_dec_lt(v___x_547_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_del_object(v___x_539_);
v___x_559_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener_spec__0___redArg___closed__0));
v___x_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set(v___x_560_, 1, v___x_547_);
return v___x_560_;
}
else
{
lean_object* v___x_561_; uint32_t v_ch_562_; lean_object* v_origLen_563_; uint8_t v_canClose_564_; uint32_t v_ch_565_; lean_object* v_origLen_566_; uint8_t v_canOpen_567_; uint8_t v___x_568_; 
v___x_561_ = lean_array_fget_borrowed(v_stack_534_, v___x_547_);
v_ch_562_ = lean_ctor_get_uint32(v___x_561_, sizeof(void*)*4);
v_origLen_563_ = lean_ctor_get(v___x_561_, 1);
v_canClose_564_ = lean_ctor_get_uint8(v___x_561_, sizeof(void*)*4 + 4);
v_ch_565_ = lean_ctor_get_uint32(v_seq_535_, sizeof(void*)*2);
v_origLen_566_ = lean_ctor_get(v_seq_535_, 1);
v_canOpen_567_ = lean_ctor_get_uint8(v_seq_535_, sizeof(void*)*2 + 4);
v___x_568_ = lean_uint32_dec_eq(v_ch_562_, v_ch_565_);
if (v___x_568_ == 0)
{
lean_object* v___x_569_; 
lean_del_object(v___x_539_);
v___x_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_541_);
lean_ctor_set(v___x_569_, 1, v___x_547_);
v_a_536_ = v___x_569_;
goto _start;
}
else
{
lean_object* v___x_571_; 
v___x_571_ = lean_nat_add(v_origLen_563_, v_origLen_566_);
if (v_canClose_564_ == 0)
{
if (v_canOpen_567_ == 0)
{
lean_dec(v___x_571_);
lean_del_object(v___x_539_);
goto v___jp_553_;
}
else
{
goto v___jp_572_;
}
}
else
{
goto v___jp_572_;
}
v___jp_572_:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_573_ = lean_unsigned_to_nat(3u);
v___x_574_ = lean_nat_mod(v___x_571_, v___x_573_);
lean_dec(v___x_571_);
v___x_575_ = lean_unsigned_to_nat(0u);
v___x_576_ = lean_nat_dec_eq(v___x_574_, v___x_575_);
lean_dec(v___x_574_);
if (v___x_576_ == 0)
{
lean_del_object(v___x_539_);
goto v___jp_553_;
}
else
{
lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_577_ = lean_nat_mod(v_origLen_563_, v___x_573_);
v___x_578_ = lean_nat_dec_eq(v___x_577_, v___x_575_);
lean_dec(v___x_577_);
if (v___x_578_ == 0)
{
goto v___jp_548_;
}
else
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = lean_nat_mod(v_origLen_566_, v___x_573_);
v___x_580_ = lean_nat_dec_eq(v___x_579_, v___x_575_);
lean_dec(v___x_579_);
if (v___x_580_ == 0)
{
goto v___jp_548_;
}
else
{
lean_del_object(v___x_539_);
goto v___jp_553_;
}
}
}
}
}
}
v___jp_548_:
{
lean_object* v___x_550_; 
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 1, v___x_547_);
lean_ctor_set(v___x_539_, 0, v___x_541_);
v___x_550_ = v___x_539_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v___x_541_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v___x_547_);
v___x_550_ = v_reuseFailAlloc_552_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
v_a_536_ = v___x_550_;
goto _start;
}
}
v___jp_553_:
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
lean_inc(v___x_547_);
v___x_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_547_);
v___x_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
v___x_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
lean_ctor_set(v___x_556_, 1, v___x_547_);
return v___x_556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener_spec__0___redArg___boxed(lean_object* v_bottom_583_, lean_object* v_stack_584_, lean_object* v_seq_585_, lean_object* v_a_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener_spec__0___redArg(v_bottom_583_, v_stack_584_, v_seq_585_, v_a_586_);
lean_dec_ref(v_seq_585_);
lean_dec_ref(v_stack_584_);
lean_dec(v_bottom_583_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener___redArg(lean_object* v_stack_588_, lean_object* v_seq_589_, lean_object* v_bottom_590_){
_start:
{
lean_object* v_i_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v_fst_595_; 
v_i_591_ = lean_array_get_size(v_stack_588_);
v___x_592_ = lean_box(0);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
lean_ctor_set(v___x_593_, 1, v_i_591_);
v___x_594_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener_spec__0___redArg(v_bottom_590_, v_stack_588_, v_seq_589_, v___x_593_);
v_fst_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_fst_595_);
lean_dec_ref(v___x_594_);
if (lean_obj_tag(v_fst_595_) == 0)
{
return v___x_592_;
}
else
{
lean_object* v_val_596_; 
v_val_596_ = lean_ctor_get(v_fst_595_, 0);
lean_inc(v_val_596_);
lean_dec_ref_known(v_fst_595_, 1);
return v_val_596_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener___redArg___boxed(lean_object* v_stack_597_, lean_object* v_seq_598_, lean_object* v_bottom_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener___redArg(v_stack_597_, v_seq_598_, v_bottom_599_);
lean_dec(v_bottom_599_);
lean_dec_ref(v_seq_598_);
lean_dec_ref(v_stack_597_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener(lean_object* v_s_601_, lean_object* v_stack_602_, lean_object* v_seq_603_, lean_object* v_bottom_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener___redArg(v_stack_602_, v_seq_603_, v_bottom_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener___boxed(lean_object* v_s_606_, lean_object* v_stack_607_, lean_object* v_seq_608_, lean_object* v_bottom_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener(v_s_606_, v_stack_607_, v_seq_608_, v_bottom_609_);
lean_dec(v_bottom_609_);
lean_dec_ref(v_seq_608_);
lean_dec_ref(v_stack_607_);
lean_dec_ref(v_s_606_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener_spec__0(lean_object* v_bottom_611_, lean_object* v_stack_612_, lean_object* v_seq_613_, lean_object* v_inst_614_, lean_object* v_a_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener_spec__0___redArg(v_bottom_611_, v_stack_612_, v_seq_613_, v_a_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener_spec__0___boxed(lean_object* v_bottom_617_, lean_object* v_stack_618_, lean_object* v_seq_619_, lean_object* v_inst_620_, lean_object* v_a_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener_spec__0(v_bottom_617_, v_stack_618_, v_seq_619_, v_inst_620_, v_a_621_);
lean_dec_ref(v_seq_619_);
lean_dec_ref(v_stack_618_);
lean_dec(v_bottom_617_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__0___redArg(lean_object* v_val_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_delimiters_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v_delimiters_625_ = lean_ctor_get(v___y_624_, 0);
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = lean_nat_add(v_val_623_, v___x_626_);
v___x_628_ = lean_array_get_size(v_delimiters_625_);
v___x_629_ = lean_nat_dec_lt(v___x_627_, v___x_628_);
lean_dec(v___x_627_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_box(0);
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v___y_624_);
return v___x_631_;
}
else
{
lean_object* v___x_632_; lean_object* v_snd_633_; 
v___x_632_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_abandonOpener___redArg(v___y_624_);
v_snd_633_ = lean_ctor_get(v___x_632_, 1);
lean_inc(v_snd_633_);
lean_dec_ref(v___x_632_);
v___y_624_ = v_snd_633_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__0___redArg___boxed(lean_object* v_val_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__0___redArg(v_val_635_, v___y_636_);
lean_dec(v_val_635_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__1___redArg(lean_object* v_key_638_, lean_object* v_s_639_, lean_object* v_seq_640_, lean_object* v_a_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
lean_object* v_fst_644_; lean_object* v_snd_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_711_; 
v_fst_644_ = lean_ctor_get(v_a_641_, 0);
v_snd_645_ = lean_ctor_get(v_a_641_, 1);
v_isSharedCheck_711_ = !lean_is_exclusive(v_a_641_);
if (v_isSharedCheck_711_ == 0)
{
v___x_647_ = v_a_641_;
v_isShared_648_ = v_isSharedCheck_711_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_snd_645_);
lean_inc(v_fst_644_);
lean_dec(v_a_641_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_711_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_649_ = lean_unsigned_to_nat(0u);
v___x_650_ = lean_nat_dec_lt(v___x_649_, v_fst_644_);
if (v___x_650_ == 0)
{
lean_object* v___x_652_; 
if (v_isShared_648_ == 0)
{
v___x_652_ = v___x_647_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_fst_644_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_snd_645_);
v___x_652_ = v_reuseFailAlloc_654_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
lean_object* v___x_653_; 
v___x_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v___y_643_);
return v___x_653_;
}
}
else
{
lean_object* v_delimiters_655_; lean_object* v_output_656_; lean_object* v_mathOpeners_657_; lean_object* v_openersBottom_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v_delimiters_655_ = lean_ctor_get(v___y_643_, 0);
v_output_656_ = lean_ctor_get(v___y_643_, 1);
v_mathOpeners_657_ = lean_ctor_get(v___y_643_, 2);
v_openersBottom_658_ = lean_ctor_get(v___y_643_, 3);
v___x_659_ = lean_array_fget_borrowed(v_openersBottom_658_, v_key_638_);
v___x_660_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_findMatchingOpener___redArg(v_delimiters_655_, v_seq_640_, v___x_659_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_673_; 
lean_inc_ref(v_openersBottom_658_);
lean_inc_ref(v_mathOpeners_657_);
lean_inc_ref(v_output_656_);
lean_inc_ref(v_delimiters_655_);
v_isSharedCheck_673_ = !lean_is_exclusive(v___y_643_);
if (v_isSharedCheck_673_ == 0)
{
lean_object* v_unused_674_; lean_object* v_unused_675_; lean_object* v_unused_676_; lean_object* v_unused_677_; 
v_unused_674_ = lean_ctor_get(v___y_643_, 3);
lean_dec(v_unused_674_);
v_unused_675_ = lean_ctor_get(v___y_643_, 2);
lean_dec(v_unused_675_);
v_unused_676_ = lean_ctor_get(v___y_643_, 1);
lean_dec(v_unused_676_);
v_unused_677_ = lean_ctor_get(v___y_643_, 0);
lean_dec(v_unused_677_);
v___x_662_ = v___y_643_;
v_isShared_663_ = v_isSharedCheck_673_;
goto v_resetjp_661_;
}
else
{
lean_dec(v___y_643_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_673_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_664_ = lean_array_get_size(v_delimiters_655_);
v___x_665_ = lean_array_fset(v_openersBottom_658_, v_key_638_, v___x_664_);
if (v_isShared_663_ == 0)
{
lean_ctor_set(v___x_662_, 3, v___x_665_);
v___x_667_ = v___x_662_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_delimiters_655_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_output_656_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v_mathOpeners_657_);
lean_ctor_set(v_reuseFailAlloc_672_, 3, v___x_665_);
v___x_667_ = v_reuseFailAlloc_672_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_669_; 
if (v_isShared_648_ == 0)
{
v___x_669_ = v___x_647_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_fst_644_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_snd_645_);
v___x_669_ = v_reuseFailAlloc_671_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
lean_object* v___x_670_; 
v___x_670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
lean_ctor_set(v___x_670_, 1, v___x_667_);
return v___x_670_;
}
}
}
}
else
{
lean_object* v_val_678_; lean_object* v___x_679_; lean_object* v_snd_680_; lean_object* v_delimiters_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v_startPos_687_; lean_object* v_remaining_688_; lean_object* v___y_690_; lean_object* v___x_708_; uint8_t v___x_709_; 
lean_del_object(v___x_647_);
v_val_678_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_val_678_);
lean_dec_ref_known(v___x_660_, 1);
v___x_679_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__0___redArg(v_val_678_, v___y_643_);
lean_dec(v_val_678_);
v_snd_680_ = lean_ctor_get(v___x_679_, 1);
lean_inc(v_snd_680_);
lean_dec_ref(v___x_679_);
v_delimiters_681_ = lean_ctor_get(v_snd_680_, 0);
v___x_682_ = lean_obj_once(&l_Lean_Markdown_instInhabitedOpenerFrame_default___closed__0, &l_Lean_Markdown_instInhabitedOpenerFrame_default___closed__0_once, _init_l_Lean_Markdown_instInhabitedOpenerFrame_default___closed__0);
v___x_683_ = lean_array_get_size(v_delimiters_681_);
v___x_684_ = lean_unsigned_to_nat(1u);
v___x_685_ = lean_nat_sub(v___x_683_, v___x_684_);
v___x_686_ = lean_array_get_borrowed(v___x_682_, v_delimiters_681_, v___x_685_);
lean_dec(v___x_685_);
v_startPos_687_ = lean_ctor_get(v___x_686_, 0);
v_remaining_688_ = lean_ctor_get(v___x_686_, 2);
v___x_708_ = lean_unsigned_to_nat(2u);
v___x_709_ = lean_nat_dec_le(v___x_708_, v_remaining_688_);
if (v___x_709_ == 0)
{
v___y_690_ = v___x_684_;
goto v___jp_689_;
}
else
{
uint8_t v___x_710_; 
v___x_710_ = lean_nat_dec_le(v___x_708_, v_fst_644_);
if (v___x_710_ == 0)
{
v___y_690_ = v___x_684_;
goto v___jp_689_;
}
else
{
v___y_690_ = v___x_708_;
goto v___jp_689_;
}
}
v___jp_689_:
{
lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v_snd_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_706_; 
v___x_691_ = lean_nat_sub(v_remaining_688_, v___y_690_);
lean_inc(v_startPos_687_);
v___x_692_ = l_String_Slice_Pos_nextn(v_s_639_, v_startPos_687_, v___x_691_);
lean_inc_n(v___y_690_, 2);
v___x_693_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_delimiterSubslice(v_s_639_, v___x_692_, v___y_690_);
lean_inc(v_snd_645_);
v___x_694_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_delimiterSubslice(v_s_639_, v_snd_645_, v___y_690_);
v___x_695_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_closeMatched___redArg(v_s_639_, v___y_690_, v___x_693_, v___x_694_, v_snd_680_);
v_snd_696_ = lean_ctor_get(v___x_695_, 1);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_695_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; 
v_unused_707_ = lean_ctor_get(v___x_695_, 0);
lean_dec(v_unused_707_);
v___x_698_ = v___x_695_;
v_isShared_699_ = v_isSharedCheck_706_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_snd_696_);
lean_dec(v___x_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_706_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_703_; 
v___x_700_ = lean_nat_sub(v_fst_644_, v___y_690_);
lean_dec(v_fst_644_);
v___x_701_ = l_String_Slice_Pos_nextn(v_s_639_, v_snd_645_, v___y_690_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v___x_701_);
lean_ctor_set(v___x_698_, 0, v___x_700_);
v___x_703_ = v___x_698_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v___x_701_);
v___x_703_ = v_reuseFailAlloc_705_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
v_a_641_ = v___x_703_;
v___y_643_ = v_snd_696_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__1___redArg___boxed(lean_object* v_key_712_, lean_object* v_s_713_, lean_object* v_seq_714_, lean_object* v_a_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__1___redArg(v_key_712_, v_s_713_, v_seq_714_, v_a_715_, v___y_716_, v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec_ref(v_seq_714_);
lean_dec_ref(v_s_713_);
lean_dec(v_key_712_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence(lean_object* v_s_719_, lean_object* v_seq_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
lean_object* v_startPos_723_; uint32_t v_ch_724_; lean_object* v_origLen_725_; uint8_t v_canOpen_726_; uint8_t v_canClose_727_; lean_object* v_seqRem_729_; lean_object* v_seqStart_730_; lean_object* v___y_731_; 
v_startPos_723_ = lean_ctor_get(v_seq_720_, 0);
v_ch_724_ = lean_ctor_get_uint32(v_seq_720_, sizeof(void*)*2);
v_origLen_725_ = lean_ctor_get(v_seq_720_, 1);
lean_inc(v_origLen_725_);
v_canOpen_726_ = lean_ctor_get_uint8(v_seq_720_, sizeof(void*)*2 + 4);
v_canClose_727_ = lean_ctor_get_uint8(v_seq_720_, sizeof(void*)*2 + 5);
if (v_canClose_727_ == 0)
{
lean_inc(v_startPos_723_);
lean_dec_ref(v_seq_720_);
lean_inc(v_origLen_725_);
v_seqRem_729_ = v_origLen_725_;
v_seqStart_730_ = v_startPos_723_;
v___y_731_ = v_a_722_;
goto v___jp_728_;
}
else
{
lean_object* v_key_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v_fst_743_; lean_object* v_snd_744_; lean_object* v_fst_745_; lean_object* v_snd_746_; 
v_key_740_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_bottomKey___redArg(v_seq_720_);
lean_inc(v_startPos_723_);
lean_inc(v_origLen_725_);
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v_origLen_725_);
lean_ctor_set(v___x_741_, 1, v_startPos_723_);
v___x_742_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__1___redArg(v_key_740_, v_s_719_, v_seq_720_, v___x_741_, v_a_721_, v_a_722_);
lean_dec_ref(v_seq_720_);
lean_dec(v_key_740_);
v_fst_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_fst_743_);
v_snd_744_ = lean_ctor_get(v___x_742_, 1);
lean_inc(v_snd_744_);
lean_dec_ref(v___x_742_);
v_fst_745_ = lean_ctor_get(v_fst_743_, 0);
lean_inc(v_fst_745_);
v_snd_746_ = lean_ctor_get(v_fst_743_, 1);
lean_inc(v_snd_746_);
lean_dec(v_fst_743_);
v_seqRem_729_ = v_fst_745_;
v_seqStart_730_ = v_snd_746_;
v___y_731_ = v_snd_744_;
goto v___jp_728_;
}
v___jp_728_:
{
lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_732_ = lean_unsigned_to_nat(0u);
v___x_733_ = lean_nat_dec_lt(v___x_732_, v_seqRem_729_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; 
lean_dec(v_seqStart_730_);
lean_dec(v_seqRem_729_);
lean_dec(v_origLen_725_);
v___x_734_ = lean_box(0);
v___x_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
lean_ctor_set(v___x_735_, 1, v___y_731_);
return v___x_735_;
}
else
{
if (v_canOpen_726_ == 0)
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
lean_dec(v_origLen_725_);
v___x_736_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_delimiterSubslice(v_s_719_, v_seqStart_730_, v_seqRem_729_);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
v___x_738_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_emit___redArg(v___x_737_, v___y_731_);
return v___x_738_;
}
else
{
lean_object* v___x_739_; 
v___x_739_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_openDelimiter___redArg(v_s_719_, v_ch_724_, v_seqStart_730_, v_origLen_725_, v_seqRem_729_, v_canClose_727_, v___y_731_);
return v___x_739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence___boxed(lean_object* v_s_747_, lean_object* v_seq_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence(v_s_747_, v_seq_748_, v_a_749_, v_a_750_);
lean_dec_ref(v_a_749_);
lean_dec_ref(v_s_747_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__0(lean_object* v_val_752_, lean_object* v_s_753_, lean_object* v_inst_754_, lean_object* v_a_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__0___redArg(v_val_752_, v___y_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__0___boxed(lean_object* v_val_759_, lean_object* v_s_760_, lean_object* v_inst_761_, lean_object* v_a_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__0(v_val_759_, v_s_760_, v_inst_761_, v_a_762_, v___y_763_, v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec_ref(v_s_760_);
lean_dec(v_val_759_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__1(lean_object* v_key_766_, lean_object* v_s_767_, lean_object* v_seq_768_, lean_object* v_inst_769_, lean_object* v_a_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__1___redArg(v_key_766_, v_s_767_, v_seq_768_, v_a_770_, v___y_771_, v___y_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__1___boxed(lean_object* v_key_774_, lean_object* v_s_775_, lean_object* v_seq_776_, lean_object* v_inst_777_, lean_object* v_a_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence_spec__1(v_key_774_, v_s_775_, v_seq_776_, v_inst_777_, v_a_778_, v___y_779_, v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec_ref(v_seq_776_);
lean_dec_ref(v_s_775_);
lean_dec(v_key_774_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processMathSequence_spec__1(lean_object* v_snd_782_, lean_object* v_as_783_, size_t v_i_784_, size_t v_stop_785_, lean_object* v_b_786_){
_start:
{
lean_object* v___y_788_; uint8_t v___x_792_; 
v___x_792_ = lean_usize_dec_eq(v_i_784_, v_stop_785_);
if (v___x_792_ == 0)
{
lean_object* v___x_793_; lean_object* v_outIdx_794_; uint8_t v___x_795_; 
v___x_793_ = lean_array_uget_borrowed(v_as_783_, v_i_784_);
v_outIdx_794_ = lean_ctor_get(v___x_793_, 3);
v___x_795_ = lean_nat_dec_lt(v_outIdx_794_, v_snd_782_);
if (v___x_795_ == 0)
{
v___y_788_ = v_b_786_;
goto v___jp_787_;
}
else
{
lean_object* v___x_796_; 
lean_inc(v___x_793_);
v___x_796_ = lean_array_push(v_b_786_, v___x_793_);
v___y_788_ = v___x_796_;
goto v___jp_787_;
}
}
else
{
return v_b_786_;
}
v___jp_787_:
{
size_t v___x_789_; size_t v___x_790_; 
v___x_789_ = ((size_t)1ULL);
v___x_790_ = lean_usize_add(v_i_784_, v___x_789_);
v_i_784_ = v___x_790_;
v_b_786_ = v___y_788_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processMathSequence_spec__1___boxed(lean_object* v_snd_797_, lean_object* v_as_798_, lean_object* v_i_799_, lean_object* v_stop_800_, lean_object* v_b_801_){
_start:
{
size_t v_i_boxed_802_; size_t v_stop_boxed_803_; lean_object* v_res_804_; 
v_i_boxed_802_ = lean_unbox_usize(v_i_799_);
lean_dec(v_i_799_);
v_stop_boxed_803_ = lean_unbox_usize(v_stop_800_);
lean_dec(v_stop_800_);
v_res_804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processMathSequence_spec__1(v_snd_797_, v_as_798_, v_i_boxed_802_, v_stop_boxed_803_, v_b_801_);
lean_dec_ref(v_as_798_);
lean_dec(v_snd_797_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processMathSequence_spec__0(lean_object* v___y_805_, size_t v_sz_806_, size_t v_i_807_, lean_object* v_bs_808_){
_start:
{
uint8_t v___x_809_; 
v___x_809_ = lean_usize_dec_lt(v_i_807_, v_sz_806_);
if (v___x_809_ == 0)
{
return v_bs_808_;
}
else
{
lean_object* v_v_810_; lean_object* v___x_811_; lean_object* v_bs_x27_812_; lean_object* v___y_814_; lean_object* v___x_819_; uint8_t v___x_820_; 
v_v_810_ = lean_array_uget(v_bs_808_, v_i_807_);
v___x_811_ = lean_unsigned_to_nat(0u);
v_bs_x27_812_ = lean_array_uset(v_bs_808_, v_i_807_, v___x_811_);
v___x_819_ = lean_array_get_size(v___y_805_);
v___x_820_ = lean_nat_dec_le(v_v_810_, v___x_819_);
if (v___x_820_ == 0)
{
lean_dec(v_v_810_);
v___y_814_ = v___x_819_;
goto v___jp_813_;
}
else
{
v___y_814_ = v_v_810_;
goto v___jp_813_;
}
v___jp_813_:
{
size_t v___x_815_; size_t v___x_816_; lean_object* v___x_817_; 
v___x_815_ = ((size_t)1ULL);
v___x_816_ = lean_usize_add(v_i_807_, v___x_815_);
v___x_817_ = lean_array_uset(v_bs_x27_812_, v_i_807_, v___y_814_);
v_i_807_ = v___x_816_;
v_bs_808_ = v___x_817_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processMathSequence_spec__0___boxed(lean_object* v___y_821_, lean_object* v_sz_822_, lean_object* v_i_823_, lean_object* v_bs_824_){
_start:
{
size_t v_sz_boxed_825_; size_t v_i_boxed_826_; lean_object* v_res_827_; 
v_sz_boxed_825_ = lean_unbox_usize(v_sz_822_);
lean_dec(v_sz_822_);
v_i_boxed_826_ = lean_unbox_usize(v_i_823_);
lean_dec(v_i_823_);
v_res_827_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processMathSequence_spec__0(v___y_821_, v_sz_boxed_825_, v_i_boxed_826_, v_bs_824_);
lean_dec_ref(v___y_821_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processMathSequence(lean_object* v_s_828_, lean_object* v_seq_829_, lean_object* v_a_830_, lean_object* v_a_831_){
_start:
{
lean_object* v_startPos_832_; lean_object* v_origLen_833_; uint8_t v_canOpen_834_; uint8_t v_canClose_835_; lean_object* v___x_836_; lean_object* v___y_838_; 
v_startPos_832_ = lean_ctor_get(v_seq_829_, 0);
lean_inc_n(v_startPos_832_, 2);
v_origLen_833_ = lean_ctor_get(v_seq_829_, 1);
lean_inc_n(v_origLen_833_, 2);
v_canOpen_834_ = lean_ctor_get_uint8(v_seq_829_, sizeof(void*)*2 + 4);
v_canClose_835_ = lean_ctor_get_uint8(v_seq_829_, sizeof(void*)*2 + 5);
lean_dec_ref(v_seq_829_);
v___x_836_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_delimiterSubslice(v_s_828_, v_startPos_832_, v_origLen_833_);
if (v_canClose_835_ == 0)
{
lean_inc_ref(v_a_831_);
v___y_838_ = v_a_831_;
goto v___jp_837_;
}
else
{
lean_object* v_delimiters_860_; lean_object* v_output_861_; lean_object* v_mathOpeners_862_; lean_object* v_openersBottom_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v_delimiters_860_ = lean_ctor_get(v_a_831_, 0);
v_output_861_ = lean_ctor_get(v_a_831_, 1);
v_mathOpeners_862_ = lean_ctor_get(v_a_831_, 2);
v_openersBottom_863_ = lean_ctor_get(v_a_831_, 3);
v___x_864_ = lean_array_get_size(v_mathOpeners_862_);
v___x_865_ = lean_unsigned_to_nat(1u);
v___x_866_ = lean_nat_sub(v___x_864_, v___x_865_);
v___x_867_ = lean_nat_dec_lt(v___x_866_, v___x_864_);
if (v___x_867_ == 0)
{
lean_dec(v___x_866_);
lean_inc_ref(v_a_831_);
v___y_838_ = v_a_831_;
goto v___jp_837_;
}
else
{
lean_object* v___x_868_; lean_object* v_snd_869_; lean_object* v_fst_870_; lean_object* v_fst_871_; lean_object* v_snd_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_914_; 
v___x_868_ = lean_array_fget_borrowed(v_mathOpeners_862_, v___x_866_);
lean_dec(v___x_866_);
v_snd_869_ = lean_ctor_get(v___x_868_, 1);
lean_inc(v_snd_869_);
v_fst_870_ = lean_ctor_get(v___x_868_, 0);
v_fst_871_ = lean_ctor_get(v_snd_869_, 0);
v_snd_872_ = lean_ctor_get(v_snd_869_, 1);
v_isSharedCheck_914_ = !lean_is_exclusive(v_snd_869_);
if (v_isSharedCheck_914_ == 0)
{
v___x_874_ = v_snd_869_;
v_isShared_875_ = v_isSharedCheck_914_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_snd_872_);
lean_inc(v_fst_871_);
lean_dec(v_snd_869_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_914_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
uint8_t v___x_876_; 
v___x_876_ = lean_nat_dec_eq(v_fst_871_, v_origLen_833_);
if (v___x_876_ == 0)
{
lean_del_object(v___x_874_);
lean_dec(v_snd_872_);
lean_dec(v_fst_871_);
lean_inc_ref(v_a_831_);
v___y_838_ = v_a_831_;
goto v___jp_837_;
}
else
{
lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_909_; 
lean_inc(v_fst_870_);
lean_inc_ref(v_openersBottom_863_);
lean_inc_ref(v_output_861_);
lean_inc_ref(v_delimiters_860_);
v_isSharedCheck_909_ = !lean_is_exclusive(v_a_831_);
if (v_isSharedCheck_909_ == 0)
{
lean_object* v_unused_910_; lean_object* v_unused_911_; lean_object* v_unused_912_; lean_object* v_unused_913_; 
v_unused_910_ = lean_ctor_get(v_a_831_, 3);
lean_dec(v_unused_910_);
v_unused_911_ = lean_ctor_get(v_a_831_, 2);
lean_dec(v_unused_911_);
v_unused_912_ = lean_ctor_get(v_a_831_, 1);
lean_dec(v_unused_912_);
v_unused_913_ = lean_ctor_get(v_a_831_, 0);
lean_dec(v_unused_913_);
v___x_878_ = v_a_831_;
v_isShared_879_ = v_isSharedCheck_909_;
goto v_resetjp_877_;
}
else
{
lean_dec(v_a_831_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_909_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v_src_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; lean_object* v___x_886_; lean_object* v___y_888_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v_src_880_ = lean_ctor_get(v_a_830_, 1);
lean_inc(v_fst_871_);
lean_inc(v_fst_870_);
v___x_881_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_delimiterSubslice(v_s_828_, v_fst_870_, v_fst_871_);
v___x_882_ = l_String_Slice_Pos_nextn(v_s_828_, v_fst_870_, v_fst_871_);
v___x_883_ = l_Lean_Markdown_InlineSource_linesBetween(v_s_828_, v_src_880_, v___x_882_, v_startPos_832_);
v___x_884_ = lean_unsigned_to_nat(2u);
v___x_885_ = lean_nat_dec_eq(v_origLen_833_, v___x_884_);
lean_dec(v_origLen_833_);
v___x_886_ = lean_alloc_ctor(8, 3, 1);
lean_ctor_set(v___x_886_, 0, v___x_881_);
lean_ctor_set(v___x_886_, 1, v___x_883_);
lean_ctor_set(v___x_886_, 2, v___x_836_);
lean_ctor_set_uint8(v___x_886_, sizeof(void*)*3, v___x_885_);
v___x_902_ = lean_unsigned_to_nat(0u);
v___x_903_ = lean_array_get_size(v_delimiters_860_);
v___x_904_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___redArg___closed__0));
v___x_905_ = lean_nat_dec_lt(v___x_902_, v___x_903_);
if (v___x_905_ == 0)
{
lean_dec_ref(v_delimiters_860_);
v___y_888_ = v___x_904_;
goto v___jp_887_;
}
else
{
size_t v___x_906_; size_t v___x_907_; lean_object* v___x_908_; 
v___x_906_ = ((size_t)0ULL);
v___x_907_ = lean_usize_of_nat(v___x_903_);
v___x_908_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processMathSequence_spec__1(v_snd_872_, v_delimiters_860_, v___x_906_, v___x_907_, v___x_904_);
lean_dec_ref(v_delimiters_860_);
v___y_888_ = v___x_908_;
goto v___jp_887_;
}
v___jp_887_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; size_t v_sz_892_; size_t v___x_893_; lean_object* v___x_894_; lean_object* v___x_896_; 
v___x_889_ = l_Array_shrink___redArg(v_output_861_, v_snd_872_);
lean_dec(v_snd_872_);
v___x_890_ = lean_array_push(v___x_889_, v___x_886_);
v___x_891_ = ((lean_object*)(l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_closeMatched___redArg___closed__0));
v_sz_892_ = lean_array_size(v_openersBottom_863_);
v___x_893_ = ((size_t)0ULL);
v___x_894_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processMathSequence_spec__0(v___y_888_, v_sz_892_, v___x_893_, v_openersBottom_863_);
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 3, v___x_894_);
lean_ctor_set(v___x_878_, 2, v___x_891_);
lean_ctor_set(v___x_878_, 1, v___x_890_);
lean_ctor_set(v___x_878_, 0, v___y_888_);
v___x_896_ = v___x_878_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___y_888_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_901_, 2, v___x_891_);
lean_ctor_set(v_reuseFailAlloc_901_, 3, v___x_894_);
v___x_896_ = v_reuseFailAlloc_901_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_897_ = lean_box(0);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 1, v___x_896_);
lean_ctor_set(v___x_874_, 0, v___x_897_);
v___x_899_ = v___x_874_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v___x_896_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
}
}
}
v___jp_837_:
{
if (v_canOpen_834_ == 0)
{
lean_object* v___x_839_; lean_object* v___x_840_; 
lean_dec(v_origLen_833_);
lean_dec(v_startPos_832_);
lean_dec_ref(v_a_831_);
v___x_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_839_, 0, v___x_836_);
v___x_840_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_emit___redArg(v___x_839_, v___y_838_);
return v___x_840_;
}
else
{
lean_object* v_delimiters_841_; lean_object* v_output_842_; lean_object* v_mathOpeners_843_; lean_object* v_openersBottom_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_859_; 
lean_dec_ref(v___y_838_);
v_delimiters_841_ = lean_ctor_get(v_a_831_, 0);
v_output_842_ = lean_ctor_get(v_a_831_, 1);
v_mathOpeners_843_ = lean_ctor_get(v_a_831_, 2);
v_openersBottom_844_ = lean_ctor_get(v_a_831_, 3);
v_isSharedCheck_859_ = !lean_is_exclusive(v_a_831_);
if (v_isSharedCheck_859_ == 0)
{
v___x_846_ = v_a_831_;
v_isShared_847_ = v_isSharedCheck_859_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_openersBottom_844_);
lean_inc(v_mathOpeners_843_);
lean_inc(v_output_842_);
lean_inc(v_delimiters_841_);
lean_dec(v_a_831_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_859_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_836_);
lean_inc_ref(v_output_842_);
v___x_849_ = lean_array_push(v_output_842_, v___x_848_);
v___x_850_ = lean_array_get_size(v_output_842_);
lean_dec_ref(v_output_842_);
v___x_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_851_, 0, v_origLen_833_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_852_, 0, v_startPos_832_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
v___x_853_ = lean_array_push(v_mathOpeners_843_, v___x_852_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 2, v___x_853_);
lean_ctor_set(v___x_846_, 1, v___x_849_);
v___x_855_ = v___x_846_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_delimiters_841_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v___x_849_);
lean_ctor_set(v_reuseFailAlloc_858_, 2, v___x_853_);
lean_ctor_set(v_reuseFailAlloc_858_, 3, v_openersBottom_844_);
v___x_855_ = v_reuseFailAlloc_858_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = lean_box(0);
v___x_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
lean_ctor_set(v___x_857_, 1, v___x_855_);
return v___x_857_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processMathSequence___boxed(lean_object* v_s_915_, lean_object* v_seq_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processMathSequence(v_s_915_, v_seq_916_, v_a_917_, v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec_ref(v_s_915_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Markdown_processEmphasis_spec__0(lean_object* v_s_920_, lean_object* v_as_921_, size_t v_sz_922_, size_t v_i_923_, lean_object* v_b_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_a_928_; lean_object* v_snd_929_; uint8_t v___x_933_; 
v___x_933_ = lean_usize_dec_lt(v_i_923_, v_sz_922_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; 
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_b_924_);
lean_ctor_set(v___x_934_, 1, v___y_926_);
return v___x_934_;
}
else
{
lean_object* v___x_935_; lean_object* v_a_936_; 
v___x_935_ = lean_box(0);
v_a_936_ = lean_array_uget_borrowed(v_as_921_, v_i_923_);
if (lean_obj_tag(v_a_936_) == 0)
{
lean_object* v_i_937_; lean_object* v___x_938_; lean_object* v_snd_939_; 
v_i_937_ = lean_ctor_get(v_a_936_, 0);
lean_inc_ref(v_i_937_);
v___x_938_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_emit___redArg(v_i_937_, v___y_926_);
v_snd_939_ = lean_ctor_get(v___x_938_, 1);
lean_inc(v_snd_939_);
lean_dec_ref(v___x_938_);
v_a_928_ = v___x_935_;
v_snd_929_ = v_snd_939_;
goto v___jp_927_;
}
else
{
lean_object* v_seq_940_; uint32_t v_ch_941_; uint32_t v___x_942_; uint8_t v___x_943_; 
v_seq_940_ = lean_ctor_get(v_a_936_, 0);
v_ch_941_ = lean_ctor_get_uint32(v_seq_940_, sizeof(void*)*2);
v___x_942_ = 36;
v___x_943_ = lean_uint32_dec_eq(v_ch_941_, v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; lean_object* v_snd_945_; 
lean_inc_ref(v_seq_940_);
v___x_944_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processDelimSequence(v_s_920_, v_seq_940_, v___y_925_, v___y_926_);
v_snd_945_ = lean_ctor_get(v___x_944_, 1);
lean_inc(v_snd_945_);
lean_dec_ref(v___x_944_);
v_a_928_ = v___x_935_;
v_snd_929_ = v_snd_945_;
goto v___jp_927_;
}
else
{
lean_object* v___x_946_; lean_object* v_snd_947_; 
lean_inc_ref(v_seq_940_);
v___x_946_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_processMathSequence(v_s_920_, v_seq_940_, v___y_925_, v___y_926_);
v_snd_947_ = lean_ctor_get(v___x_946_, 1);
lean_inc(v_snd_947_);
lean_dec_ref(v___x_946_);
v_a_928_ = v___x_935_;
v_snd_929_ = v_snd_947_;
goto v___jp_927_;
}
}
}
v___jp_927_:
{
size_t v___x_930_; size_t v___x_931_; 
v___x_930_ = ((size_t)1ULL);
v___x_931_ = lean_usize_add(v_i_923_, v___x_930_);
v_i_923_ = v___x_931_;
v_b_924_ = v_a_928_;
v___y_926_ = v_snd_929_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Markdown_processEmphasis_spec__0___boxed(lean_object* v_s_948_, lean_object* v_as_949_, lean_object* v_sz_950_, lean_object* v_i_951_, lean_object* v_b_952_, lean_object* v___y_953_, lean_object* v___y_954_){
_start:
{
size_t v_sz_boxed_955_; size_t v_i_boxed_956_; lean_object* v_res_957_; 
v_sz_boxed_955_ = lean_unbox_usize(v_sz_950_);
lean_dec(v_sz_950_);
v_i_boxed_956_ = lean_unbox_usize(v_i_951_);
lean_dec(v_i_951_);
v_res_957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Markdown_processEmphasis_spec__0(v_s_948_, v_as_949_, v_sz_boxed_955_, v_i_boxed_956_, v_b_952_, v___y_953_, v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec_ref(v_as_949_);
lean_dec_ref(v_s_948_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_processEmphasis(lean_object* v_s_958_, lean_object* v_ctx_959_, lean_object* v_toks_960_){
_start:
{
lean_object* v___x_961_; size_t v_sz_962_; size_t v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v_snd_966_; lean_object* v___x_967_; lean_object* v_fst_968_; 
v___x_961_ = lean_box(0);
v_sz_962_ = lean_array_size(v_toks_960_);
v___x_963_ = ((size_t)0ULL);
v___x_964_ = lean_obj_once(&l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___closed__0, &l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___closed__0_once, _init_l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_DelimiterMatchState_empty___closed__0);
v___x_965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Markdown_processEmphasis_spec__0(v_s_958_, v_toks_960_, v_sz_962_, v___x_963_, v___x_961_, v_ctx_959_, v___x_964_);
v_snd_966_ = lean_ctor_get(v___x_965_, 1);
lean_inc(v_snd_966_);
lean_dec_ref(v___x_965_);
v___x_967_ = l___private_Lean_Data_Markdown_Parser_Emphasis_0__Lean_Markdown_finalizeEmphasis___redArg(v_s_958_, v_snd_966_);
v_fst_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_fst_968_);
lean_dec_ref(v___x_967_);
return v_fst_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Markdown_processEmphasis___boxed(lean_object* v_s_969_, lean_object* v_ctx_970_, lean_object* v_toks_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_Markdown_processEmphasis(v_s_969_, v_ctx_970_, v_toks_971_);
lean_dec_ref(v_toks_971_);
lean_dec_ref(v_ctx_970_);
lean_dec_ref(v_s_969_);
return v_res_972_;
}
}
lean_object* runtime_initialize_Init_While(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_Inline(uint8_t builtin);
lean_object* runtime_initialize_Lean_Data_Markdown_InlineCursor(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Markdown_Parser_Emphasis(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Inline(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_InlineCursor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Markdown_Parser_Emphasis(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_While(uint8_t builtin);
lean_object* initialize_Init_Data_Vector_Basic(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_Inline(uint8_t builtin);
lean_object* initialize_Lean_Data_Markdown_InlineCursor(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Markdown_Parser_Emphasis(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Vector_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_Inline(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Markdown_InlineCursor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Markdown_Parser_Emphasis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Markdown_Parser_Emphasis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Markdown_Parser_Emphasis(builtin);
}
#ifdef __cplusplus
}
#endif
