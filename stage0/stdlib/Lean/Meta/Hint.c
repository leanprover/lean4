// Lean compiler output
// Module: Lean.Meta.Hint
// Imports: public import Lean.Meta.TryThis public import Lean.Util.Diff
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
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_foldl___at___00Array_appendList_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_Diff_instBEqAction_beq(uint8_t, uint8_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint32_to_uint64(uint32_t);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_data(lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_drop___redArg(lean_object*, lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* l_Subarray_take___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Subarray_split___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_string_mk(lean_object*);
lean_object* l_Lean_MessageData_nestD(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Lsp_instToJsonRange_toJson(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_Range_includes(lean_object*, lean_object*, uint8_t, uint8_t);
extern lean_object* l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_;
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_format(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_ofRange(lean_object*, uint8_t);
lean_object* l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_string_object l_Lean_Meta_Hint_textInsertionWidget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1770, .m_capacity = 1770, .m_length = 1769, .m_data = "\nimport * as React from 'react';\nimport { EditorContext, EnvPosContext } from '@leanprover/infoview';\n\nconst e = React.createElement;\nexport default function ({ range, suggestion, acceptSuggestionProps }) {\n  const pos = React.useContext(EnvPosContext)\n  const editorConnection = React.useContext(EditorContext)\n  function onClick() {\n    editorConnection.api.applyEdit({\n      changes: { [pos.uri]: [{ range, newText: suggestion }] }\n    })\n  }\n\n  if (acceptSuggestionProps.kind === 'text') {\n    return e('span', {\n        onClick,\n        title: acceptSuggestionProps.hoverText,\n        className: 'link pointer dim font-code',\n        style: { color: 'var(--vscode-textLink-foreground)' }\n      },\n      acceptSuggestionProps.linkText)\n  } else if (acceptSuggestionProps.kind === 'icon') {\n    if (acceptSuggestionProps.gaps) {\n      const icon = e('span', {\n        className: `codicon codicon-${acceptSuggestionProps.codiconName}`,\n        style: {\n          verticalAlign: 'sub',\n          fontSize: 'var(--vscode-editor-font-size)'\n        }\n      })\n      return e('span', {\n        onClick,\n        title: acceptSuggestionProps.hoverText,\n        className: `link pointer dim font-code`,\n        style: { color: 'var(--vscode-textLink-foreground)' }\n      }, ' ', icon, ' ')\n    } else {\n      return e('span', {\n        onClick,\n        title: acceptSuggestionProps.hoverText,\n        className: `link pointer dim font-code codicon codicon-${acceptSuggestionProps.codiconName}`,\n        style: {\n          color: 'var(--vscode-textLink-foreground)',\n          verticalAlign: 'sub',\n          fontSize: 'var(--vscode-editor-font-size)'\n        }\n      })\n    }\n\n  }\n  throw new Error('Unexpected `acceptSuggestionProps` kind: ' + acceptSuggestionProps.kind)\n}"};
static const lean_object* l_Lean_Meta_Hint_textInsertionWidget___closed__0 = (const lean_object*)&l_Lean_Meta_Hint_textInsertionWidget___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Hint_textInsertionWidget___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Hint_textInsertionWidget___closed__1;
static lean_once_cell_t l_Lean_Meta_Hint_textInsertionWidget___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Hint_textInsertionWidget___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_textInsertionWidget;
static const lean_string_object l_Lean_Meta_Hint_tryThisDiffWidget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1142, .m_capacity = 1142, .m_length = 1141, .m_data = "\nimport * as React from 'react';\nimport { EditorContext, EnvPosContext } from '@leanprover/infoview';\n\nconst e = React.createElement;\nexport default function ({ diff, range, suggestion }) {\n  const pos = React.useContext(EnvPosContext)\n  const editorConnection = React.useContext(EditorContext)\n  const insStyle = {\n    style: { color: 'var(--vscode-textLink-foreground)' }\n  }\n  const delStyle = {\n    style: { color: 'var(--vscode-editorError-foreground)', textDecoration: 'line-through' }\n  }\n  const defStyle = {\n    style: { color: 'var(--vscode-editor-foreground)' }\n  }\n  function onClick() {\n    editorConnection.api.applyEdit({\n      changes: { [pos.uri]: [{ range, newText: suggestion }] }\n    })\n  }\n\n  const spans = diff.map (comp =>\n    comp.type === 'deletion' \? e('span', delStyle, comp.text) :\n    comp.type === 'insertion' \? e('span', insStyle, comp.text) :\n      e('span', defStyle, comp.text)\n  )\n  const fullDiff = e('span',\n    { onClick,\n      title: 'Apply suggestion',\n      className: 'link pointer dim font-code',\n      style: { display: 'inline-block', verticalAlign: 'text-top' } },\n    spans)\n  return fullDiff\n}"};
static const lean_object* l_Lean_Meta_Hint_tryThisDiffWidget___closed__0 = (const lean_object*)&l_Lean_Meta_Hint_tryThisDiffWidget___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Hint_tryThisDiffWidget___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Hint_tryThisDiffWidget___closed__1;
static lean_once_cell_t l_Lean_Meta_Hint_tryThisDiffWidget___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Hint_tryThisDiffWidget___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_tryThisDiffWidget;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "type"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "insertion"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__1_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__0_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__2_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "deletion"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__5_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__5_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__0_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__6_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "unchanged"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__8_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__8_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__9_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__0_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__9_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__10_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0(lean_object*, lean_object*);
static const lean_array_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0 = (const lean_object*)&l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_instCoeSuggestionTextSuggestion___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_Hint_instCoeSuggestionTextSuggestion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Hint_instCoeSuggestionTextSuggestion___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Hint_instCoeSuggestionTextSuggestion___closed__0 = (const lean_object*)&l_Lean_Meta_Hint_instCoeSuggestionTextSuggestion___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Hint_instCoeSuggestionTextSuggestion = (const lean_object*)&l_Lean_Meta_Hint_instCoeSuggestionTextSuggestion___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_instToMessageDataSuggestion___lam__0(lean_object*);
static const lean_closure_object l_Lean_Meta_Hint_instToMessageDataSuggestion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Hint_instToMessageDataSuggestion___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Hint_instToMessageDataSuggestion___closed__0 = (const lean_object*)&l_Lean_Meta_Hint_instToMessageDataSuggestion___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Hint_instToMessageDataSuggestion = (const lean_object*)&l_Lean_Meta_Hint_instToMessageDataSuggestion___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11_spec__21___redArg(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11___redArg(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23_spec__28___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23_spec__28___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10_spec__19___redArg(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10_spec__19___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10___redArg(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7___redArg(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0;
static lean_once_cell_t l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1;
static lean_once_cell_t l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg(lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0 = (const lean_object*)&l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0_value;
static const lean_ctor_object l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__1 = (const lean_object*)&l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__1_value;
static const lean_ctor_object l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0_value),((lean_object*)&l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__1_value)}};
static const lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__2 = (const lean_object*)&l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10_spec__19(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11_spec__21(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23_spec__28(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0 = (const lean_object*)&l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23_spec__28___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23_spec__28___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10_spec__19___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10_spec__19___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0;
static lean_once_cell_t l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1;
static lean_once_cell_t l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__0 = (const lean_object*)&l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__0_value;
static const lean_ctor_object l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__0_value),((lean_object*)&l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__1_value)}};
static const lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__1 = (const lean_object*)&l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__0 = (const lean_object*)&l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__1 = (const lean_object*)&l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__0_value),((lean_object*)&l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__1_value)}};
static const lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__2 = (const lean_object*)&l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10_spec__19(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10_spec__19___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23_spec__28(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23_spec__28___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0;
static lean_once_cell_t l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "• "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Hint"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__6_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "tryThisDiffWidget"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__7_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(141, 179, 88, 64, 208, 112, 210, 214)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__7_value),LEAN_SCALAR_PTR_LITERAL(174, 189, 209, 40, 106, 230, 251, 8)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "diff"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__9_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "suggestion"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "range"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "linkText"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__12 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__12_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "[apply]"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__13 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__13_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__13_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__14 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__14_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__12_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__14_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__15 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__15_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__15_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__16 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__16_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "textInsertionWidget"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__17 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__17_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__5_value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18_value_aux_1),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__6_value),LEAN_SCALAR_PTR_LITERAL(141, 179, 88, 64, 208, 112, 210, 214)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__17_value),LEAN_SCALAR_PTR_LITERAL(137, 84, 167, 88, 42, 220, 7, 88)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "acceptSuggestionProps"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__19 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__19_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "kind"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__20 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__20_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__4_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__21 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__21_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__20_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__21_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__22 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__22_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "hoverText"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__23 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__23_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Apply suggestion"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__24 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__24_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__24_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__25 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__25_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__23_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__25_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__26 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__26_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__26_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__16_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__27 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__27_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__22_value),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__27_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__28 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__28_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__13_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__32 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__32_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__34 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__34_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Try this: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__36 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__36_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_MessageData_hint___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hint"};
static const lean_object* l_Lean_MessageData_hint___closed__0 = (const lean_object*)&l_Lean_MessageData_hint___closed__0_value;
static const lean_ctor_object l_Lean_MessageData_hint___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_MessageData_hint___closed__0_value),LEAN_SCALAR_PTR_LITERAL(166, 129, 8, 98, 135, 223, 96, 106)}};
static const lean_object* l_Lean_MessageData_hint___closed__1 = (const lean_object*)&l_Lean_MessageData_hint___closed__1_value;
static const lean_string_object l_Lean_MessageData_hint___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "\n\nHint: "};
static const lean_object* l_Lean_MessageData_hint___closed__2 = (const lean_object*)&l_Lean_MessageData_hint___closed__2_value;
static lean_once_cell_t l_Lean_MessageData_hint___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_MessageData_hint___closed__3;
LEAN_EXPORT lean_object* l_Lean_MessageData_hint(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MessageData_hint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static uint64_t _init_l_Lean_Meta_Hint_textInsertionWidget___closed__1(void){
_start:
{
lean_object* v___x_2_; uint64_t v___x_3_; 
v___x_2_ = ((lean_object*)(l_Lean_Meta_Hint_textInsertionWidget___closed__0));
v___x_3_ = lean_string_hash(v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_Meta_Hint_textInsertionWidget___closed__2(void){
_start:
{
uint64_t v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_uint64_once(&l_Lean_Meta_Hint_textInsertionWidget___closed__1, &l_Lean_Meta_Hint_textInsertionWidget___closed__1_once, _init_l_Lean_Meta_Hint_textInsertionWidget___closed__1);
v___x_5_ = ((lean_object*)(l_Lean_Meta_Hint_textInsertionWidget___closed__0));
v___x_6_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_6_, 0, v___x_5_);
lean_ctor_set_uint64(v___x_6_, sizeof(void*)*1, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Meta_Hint_textInsertionWidget(void){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_obj_once(&l_Lean_Meta_Hint_textInsertionWidget___closed__2, &l_Lean_Meta_Hint_textInsertionWidget___closed__2_once, _init_l_Lean_Meta_Hint_textInsertionWidget___closed__2);
return v___x_7_;
}
}
static uint64_t _init_l_Lean_Meta_Hint_tryThisDiffWidget___closed__1(void){
_start:
{
lean_object* v___x_9_; uint64_t v___x_10_; 
v___x_9_ = ((lean_object*)(l_Lean_Meta_Hint_tryThisDiffWidget___closed__0));
v___x_10_ = lean_string_hash(v___x_9_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_Meta_Hint_tryThisDiffWidget___closed__2(void){
_start:
{
uint64_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_11_ = lean_uint64_once(&l_Lean_Meta_Hint_tryThisDiffWidget___closed__1, &l_Lean_Meta_Hint_tryThisDiffWidget___closed__1_once, _init_l_Lean_Meta_Hint_tryThisDiffWidget___closed__1);
v___x_12_ = ((lean_object*)(l_Lean_Meta_Hint_tryThisDiffWidget___closed__0));
v___x_13_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_13_, 0, v___x_12_);
lean_ctor_set_uint64(v___x_13_, sizeof(void*)*1, v___x_11_);
return v___x_13_;
}
}
static lean_object* _init_l_Lean_Meta_Hint_tryThisDiffWidget(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = lean_obj_once(&l_Lean_Meta_Hint_tryThisDiffWidget___closed__2, &l_Lean_Meta_Hint_tryThisDiffWidget___closed__2_once, _init_l_Lean_Meta_Hint_tryThisDiffWidget___closed__2);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1(size_t v_sz_15_, size_t v_i_16_, lean_object* v_bs_17_){
_start:
{
uint8_t v___x_18_; 
v___x_18_ = lean_usize_dec_lt(v_i_16_, v_sz_15_);
if (v___x_18_ == 0)
{
return v_bs_17_;
}
else
{
lean_object* v_v_19_; lean_object* v___x_20_; lean_object* v_bs_x27_21_; size_t v___x_22_; size_t v___x_23_; lean_object* v___x_24_; 
v_v_19_ = lean_array_uget(v_bs_17_, v_i_16_);
v___x_20_ = lean_unsigned_to_nat(0u);
v_bs_x27_21_ = lean_array_uset(v_bs_17_, v_i_16_, v___x_20_);
v___x_22_ = ((size_t)1ULL);
v___x_23_ = lean_usize_add(v_i_16_, v___x_22_);
v___x_24_ = lean_array_uset(v_bs_x27_21_, v_i_16_, v_v_19_);
v_i_16_ = v___x_23_;
v_bs_17_ = v___x_24_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1___boxed(lean_object* v_sz_26_, lean_object* v_i_27_, lean_object* v_bs_28_){
_start:
{
size_t v_sz_boxed_29_; size_t v_i_boxed_30_; lean_object* v_res_31_; 
v_sz_boxed_29_ = lean_unbox_usize(v_sz_26_);
lean_dec(v_sz_26_);
v_i_boxed_30_ = lean_unbox_usize(v_i_27_);
lean_dec(v_i_27_);
v_res_31_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1(v_sz_boxed_29_, v_i_boxed_30_, v_bs_28_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1(lean_object* v_a_32_){
_start:
{
size_t v_sz_33_; size_t v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_sz_33_ = lean_array_size(v_a_32_);
v___x_34_ = ((size_t)0ULL);
v___x_35_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1(v_sz_33_, v___x_34_, v_a_32_);
v___x_36_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0(size_t v_sz_57_, size_t v_i_58_, lean_object* v_bs_59_){
_start:
{
uint8_t v___x_60_; 
v___x_60_ = lean_usize_dec_lt(v_i_58_, v_sz_57_);
if (v___x_60_ == 0)
{
return v_bs_59_;
}
else
{
lean_object* v_v_61_; lean_object* v_fst_62_; lean_object* v_snd_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_106_; 
v_v_61_ = lean_array_uget(v_bs_59_, v_i_58_);
v_fst_62_ = lean_ctor_get(v_v_61_, 0);
v_snd_63_ = lean_ctor_get(v_v_61_, 1);
v_isSharedCheck_106_ = !lean_is_exclusive(v_v_61_);
if (v_isSharedCheck_106_ == 0)
{
v___x_65_ = v_v_61_;
v_isShared_66_ = v_isSharedCheck_106_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_snd_63_);
lean_inc(v_fst_62_);
lean_dec(v_v_61_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_106_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v___x_67_; lean_object* v_bs_x27_68_; lean_object* v___y_70_; uint8_t v___x_75_; 
v___x_67_ = lean_unsigned_to_nat(0u);
v_bs_x27_68_ = lean_array_uset(v_bs_59_, v_i_58_, v___x_67_);
v___x_75_ = lean_unbox(v_fst_62_);
lean_dec(v_fst_62_);
switch(v___x_75_)
{
case 0:
{
lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_76_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__3));
v___x_77_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__4));
v___x_78_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_78_, 0, v_snd_63_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v___x_78_);
lean_ctor_set(v___x_65_, 0, v___x_77_);
v___x_80_ = v___x_65_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_77_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v___x_78_);
v___x_80_ = v_reuseFailAlloc_85_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_81_ = lean_box(0);
v___x_82_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_80_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_76_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
v___x_84_ = l_Lean_Json_mkObj(v___x_83_);
lean_dec_ref_known(v___x_83_, 2);
v___y_70_ = v___x_84_;
goto v___jp_69_;
}
}
case 1:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_90_; 
v___x_86_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__7));
v___x_87_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__4));
v___x_88_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_88_, 0, v_snd_63_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v___x_88_);
lean_ctor_set(v___x_65_, 0, v___x_87_);
v___x_90_ = v___x_65_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_87_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v___x_88_);
v___x_90_ = v_reuseFailAlloc_95_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_91_ = lean_box(0);
v___x_92_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_92_, 0, v___x_90_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
v___x_93_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_86_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = l_Lean_Json_mkObj(v___x_93_);
lean_dec_ref_known(v___x_93_, 2);
v___y_70_ = v___x_94_;
goto v___jp_69_;
}
}
default: 
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_100_; 
v___x_96_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__10));
v___x_97_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__4));
v___x_98_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_98_, 0, v_snd_63_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v___x_98_);
lean_ctor_set(v___x_65_, 0, v___x_97_);
v___x_100_ = v___x_65_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_97_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v___x_98_);
v___x_100_ = v_reuseFailAlloc_105_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_101_ = lean_box(0);
v___x_102_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_100_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
v___x_103_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_96_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v___x_104_ = l_Lean_Json_mkObj(v___x_103_);
lean_dec_ref_known(v___x_103_, 2);
v___y_70_ = v___x_104_;
goto v___jp_69_;
}
}
}
v___jp_69_:
{
size_t v___x_71_; size_t v___x_72_; lean_object* v___x_73_; 
v___x_71_ = ((size_t)1ULL);
v___x_72_ = lean_usize_add(v_i_58_, v___x_71_);
v___x_73_ = lean_array_uset(v_bs_x27_68_, v_i_58_, v___y_70_);
v_i_58_ = v___x_72_;
v_bs_59_ = v___x_73_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___boxed(lean_object* v_sz_107_, lean_object* v_i_108_, lean_object* v_bs_109_){
_start:
{
size_t v_sz_boxed_110_; size_t v_i_boxed_111_; lean_object* v_res_112_; 
v_sz_boxed_110_ = lean_unbox_usize(v_sz_107_);
lean_dec(v_sz_107_);
v_i_boxed_111_ = lean_unbox_usize(v_i_108_);
lean_dec(v_i_108_);
v_res_112_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0(v_sz_boxed_110_, v_i_boxed_111_, v_bs_109_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson(lean_object* v_ds_113_){
_start:
{
size_t v_sz_114_; size_t v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_sz_114_ = lean_array_size(v_ds_113_);
v___x_115_ = ((size_t)0ULL);
v___x_116_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0(v_sz_114_, v___x_115_, v_ds_113_);
v___x_117_ = l_Lean_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1(v___x_116_);
return v___x_117_;
}
}
static lean_object* _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_118_; lean_object* v___x_119_; 
v___x_118_ = 821;
v___x_119_ = lean_box_uint32(v___x_118_);
return v___x_119_;
}
}
static lean_object* _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_120_ = lean_box(0);
v___x_121_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0___boxed__const__1;
v___x_122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
lean_ctor_set(v___x_122_, 1, v___x_120_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1(lean_object* v_a_123_, lean_object* v_a_124_){
_start:
{
if (lean_obj_tag(v_a_123_) == 0)
{
lean_object* v___x_125_; 
v___x_125_ = lean_array_to_list(v_a_124_);
return v___x_125_;
}
else
{
lean_object* v_head_126_; lean_object* v_tail_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_137_; 
v_head_126_ = lean_ctor_get(v_a_123_, 0);
v_tail_127_ = lean_ctor_get(v_a_123_, 1);
v_isSharedCheck_137_ = !lean_is_exclusive(v_a_123_);
if (v_isSharedCheck_137_ == 0)
{
v___x_129_ = v_a_123_;
v_isShared_130_ = v_isSharedCheck_137_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_tail_127_);
lean_inc(v_head_126_);
lean_dec(v_a_123_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_137_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_131_ = lean_obj_once(&l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0, &l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0_once, _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 1, v___x_131_);
v___x_133_ = v___x_129_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_head_126_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v___x_131_);
v___x_133_ = v_reuseFailAlloc_136_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_134_; 
v___x_134_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_124_, v___x_133_);
v_a_123_ = v_tail_127_;
v_a_124_ = v___x_134_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_138_; lean_object* v___x_139_; 
v___x_138_ = 818;
v___x_139_ = lean_box_uint32(v___x_138_);
return v___x_139_;
}
}
static lean_object* _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_140_ = lean_box(0);
v___x_141_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0___boxed__const__1;
v___x_142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_141_);
lean_ctor_set(v___x_142_, 1, v___x_140_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0(lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
if (lean_obj_tag(v_a_143_) == 0)
{
lean_object* v___x_145_; 
v___x_145_ = lean_array_to_list(v_a_144_);
return v___x_145_;
}
else
{
lean_object* v_head_146_; lean_object* v_tail_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_157_; 
v_head_146_ = lean_ctor_get(v_a_143_, 0);
v_tail_147_ = lean_ctor_get(v_a_143_, 1);
v_isSharedCheck_157_ = !lean_is_exclusive(v_a_143_);
if (v_isSharedCheck_157_ == 0)
{
v___x_149_ = v_a_143_;
v_isShared_150_ = v_isSharedCheck_157_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_tail_147_);
lean_inc(v_head_146_);
lean_dec(v_a_143_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_157_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_151_ = lean_obj_once(&l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0, &l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0_once, _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 1, v___x_151_);
v___x_153_ = v___x_149_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_head_146_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v___x_151_);
v___x_153_ = v_reuseFailAlloc_156_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
lean_object* v___x_154_; 
v___x_154_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_144_, v___x_153_);
v_a_143_ = v_tail_147_;
v_a_144_ = v___x_154_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2(size_t v_sz_160_, size_t v_i_161_, lean_object* v_bs_162_){
_start:
{
uint8_t v___x_163_; 
v___x_163_ = lean_usize_dec_lt(v_i_161_, v_sz_160_);
if (v___x_163_ == 0)
{
return v_bs_162_;
}
else
{
lean_object* v_v_164_; lean_object* v_fst_165_; lean_object* v_snd_166_; lean_object* v___x_167_; lean_object* v_bs_x27_168_; lean_object* v___y_170_; uint8_t v___x_175_; 
v_v_164_ = lean_array_uget_borrowed(v_bs_162_, v_i_161_);
v_fst_165_ = lean_ctor_get(v_v_164_, 0);
lean_inc(v_fst_165_);
v_snd_166_ = lean_ctor_get(v_v_164_, 1);
lean_inc(v_snd_166_);
v___x_167_ = lean_unsigned_to_nat(0u);
v_bs_x27_168_ = lean_array_uset(v_bs_162_, v_i_161_, v___x_167_);
v___x_175_ = lean_unbox(v_fst_165_);
lean_dec(v_fst_165_);
switch(v___x_175_)
{
case 0:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_176_ = lean_string_data(v_snd_166_);
v___x_177_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_178_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0(v___x_176_, v___x_177_);
v___x_179_ = lean_string_mk(v___x_178_);
v___y_170_ = v___x_179_;
goto v___jp_169_;
}
case 1:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_180_ = lean_string_data(v_snd_166_);
v___x_181_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_182_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1(v___x_180_, v___x_181_);
v___x_183_ = lean_string_mk(v___x_182_);
v___y_170_ = v___x_183_;
goto v___jp_169_;
}
default: 
{
v___y_170_ = v_snd_166_;
goto v___jp_169_;
}
}
v___jp_169_:
{
size_t v___x_171_; size_t v___x_172_; lean_object* v___x_173_; 
v___x_171_ = ((size_t)1ULL);
v___x_172_ = lean_usize_add(v_i_161_, v___x_171_);
v___x_173_ = lean_array_uset(v_bs_x27_168_, v_i_161_, v___y_170_);
v_i_161_ = v___x_172_;
v_bs_162_ = v___x_173_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___boxed(lean_object* v_sz_184_, lean_object* v_i_185_, lean_object* v_bs_186_){
_start:
{
size_t v_sz_boxed_187_; size_t v_i_boxed_188_; lean_object* v_res_189_; 
v_sz_boxed_187_ = lean_unbox_usize(v_sz_184_);
lean_dec(v_sz_184_);
v_i_boxed_188_ = lean_unbox_usize(v_i_185_);
lean_dec(v_i_185_);
v_res_189_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2(v_sz_boxed_187_, v_i_boxed_188_, v_bs_186_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(lean_object* v_as_190_, size_t v_i_191_, size_t v_stop_192_, lean_object* v_b_193_){
_start:
{
uint8_t v___x_194_; 
v___x_194_ = lean_usize_dec_eq(v_i_191_, v_stop_192_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; size_t v___x_197_; size_t v___x_198_; 
v___x_195_ = lean_array_uget_borrowed(v_as_190_, v_i_191_);
v___x_196_ = lean_string_append(v_b_193_, v___x_195_);
v___x_197_ = ((size_t)1ULL);
v___x_198_ = lean_usize_add(v_i_191_, v___x_197_);
v_i_191_ = v___x_198_;
v_b_193_ = v___x_196_;
goto _start;
}
else
{
return v_b_193_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3___boxed(lean_object* v_as_200_, lean_object* v_i_201_, lean_object* v_stop_202_, lean_object* v_b_203_){
_start:
{
size_t v_i_boxed_204_; size_t v_stop_boxed_205_; lean_object* v_res_206_; 
v_i_boxed_204_ = lean_unbox_usize(v_i_201_);
lean_dec(v_i_201_);
v_stop_boxed_205_ = lean_unbox_usize(v_stop_202_);
lean_dec(v_stop_202_);
v_res_206_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_as_200_, v_i_boxed_204_, v_stop_boxed_205_, v_b_203_);
lean_dec_ref(v_as_200_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString(lean_object* v_ds_208_){
_start:
{
size_t v_sz_209_; size_t v___x_210_; lean_object* v_rangeStrs_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v_sz_209_ = lean_array_size(v_ds_208_);
v___x_210_ = ((size_t)0ULL);
v_rangeStrs_211_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2(v_sz_209_, v___x_210_, v_ds_208_);
v___x_212_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = lean_array_get_size(v_rangeStrs_211_);
v___x_215_ = lean_nat_dec_lt(v___x_213_, v___x_214_);
if (v___x_215_ == 0)
{
lean_dec_ref(v_rangeStrs_211_);
return v___x_212_;
}
else
{
uint8_t v___x_216_; 
v___x_216_ = lean_nat_dec_le(v___x_214_, v___x_214_);
if (v___x_216_ == 0)
{
if (v___x_215_ == 0)
{
lean_dec_ref(v_rangeStrs_211_);
return v___x_212_;
}
else
{
size_t v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_usize_of_nat(v___x_214_);
v___x_218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_rangeStrs_211_, v___x_210_, v___x_217_, v___x_212_);
lean_dec_ref(v_rangeStrs_211_);
return v___x_218_;
}
}
else
{
size_t v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_usize_of_nat(v___x_214_);
v___x_220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_rangeStrs_211_, v___x_210_, v___x_219_, v___x_212_);
lean_dec_ref(v_rangeStrs_211_);
return v___x_220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorIdx(uint8_t v_x_221_){
_start:
{
switch(v_x_221_)
{
case 0:
{
lean_object* v___x_222_; 
v___x_222_ = lean_unsigned_to_nat(0u);
return v___x_222_;
}
case 1:
{
lean_object* v___x_223_; 
v___x_223_ = lean_unsigned_to_nat(1u);
return v___x_223_;
}
case 2:
{
lean_object* v___x_224_; 
v___x_224_ = lean_unsigned_to_nat(2u);
return v___x_224_;
}
case 3:
{
lean_object* v___x_225_; 
v___x_225_ = lean_unsigned_to_nat(3u);
return v___x_225_;
}
default: 
{
lean_object* v___x_226_; 
v___x_226_ = lean_unsigned_to_nat(4u);
return v___x_226_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorIdx___boxed(lean_object* v_x_227_){
_start:
{
uint8_t v_x_boxed_228_; lean_object* v_res_229_; 
v_x_boxed_228_ = lean_unbox(v_x_227_);
v_res_229_ = l_Lean_Meta_Hint_DiffGranularity_ctorIdx(v_x_boxed_228_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim___redArg(lean_object* v_k_230_){
_start:
{
lean_inc(v_k_230_);
return v_k_230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim___redArg___boxed(lean_object* v_k_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l_Lean_Meta_Hint_DiffGranularity_ctorElim___redArg(v_k_231_);
lean_dec(v_k_231_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim(lean_object* v_motive_233_, lean_object* v_ctorIdx_234_, uint8_t v_t_235_, lean_object* v_h_236_, lean_object* v_k_237_){
_start:
{
lean_inc(v_k_237_);
return v_k_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim___boxed(lean_object* v_motive_238_, lean_object* v_ctorIdx_239_, lean_object* v_t_240_, lean_object* v_h_241_, lean_object* v_k_242_){
_start:
{
uint8_t v_t_boxed_243_; lean_object* v_res_244_; 
v_t_boxed_243_ = lean_unbox(v_t_240_);
v_res_244_ = l_Lean_Meta_Hint_DiffGranularity_ctorElim(v_motive_238_, v_ctorIdx_239_, v_t_boxed_243_, v_h_241_, v_k_242_);
lean_dec(v_k_242_);
lean_dec(v_ctorIdx_239_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim___redArg(lean_object* v_auto_245_){
_start:
{
lean_inc(v_auto_245_);
return v_auto_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim___redArg___boxed(lean_object* v_auto_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Meta_Hint_DiffGranularity_auto_elim___redArg(v_auto_246_);
lean_dec(v_auto_246_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim(lean_object* v_motive_248_, uint8_t v_t_249_, lean_object* v_h_250_, lean_object* v_auto_251_){
_start:
{
lean_inc(v_auto_251_);
return v_auto_251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim___boxed(lean_object* v_motive_252_, lean_object* v_t_253_, lean_object* v_h_254_, lean_object* v_auto_255_){
_start:
{
uint8_t v_t_boxed_256_; lean_object* v_res_257_; 
v_t_boxed_256_ = lean_unbox(v_t_253_);
v_res_257_ = l_Lean_Meta_Hint_DiffGranularity_auto_elim(v_motive_252_, v_t_boxed_256_, v_h_254_, v_auto_255_);
lean_dec(v_auto_255_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim___redArg(lean_object* v_char_258_){
_start:
{
lean_inc(v_char_258_);
return v_char_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim___redArg___boxed(lean_object* v_char_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Lean_Meta_Hint_DiffGranularity_char_elim___redArg(v_char_259_);
lean_dec(v_char_259_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim(lean_object* v_motive_261_, uint8_t v_t_262_, lean_object* v_h_263_, lean_object* v_char_264_){
_start:
{
lean_inc(v_char_264_);
return v_char_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim___boxed(lean_object* v_motive_265_, lean_object* v_t_266_, lean_object* v_h_267_, lean_object* v_char_268_){
_start:
{
uint8_t v_t_boxed_269_; lean_object* v_res_270_; 
v_t_boxed_269_ = lean_unbox(v_t_266_);
v_res_270_ = l_Lean_Meta_Hint_DiffGranularity_char_elim(v_motive_265_, v_t_boxed_269_, v_h_267_, v_char_268_);
lean_dec(v_char_268_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim___redArg(lean_object* v_word_271_){
_start:
{
lean_inc(v_word_271_);
return v_word_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim___redArg___boxed(lean_object* v_word_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_Meta_Hint_DiffGranularity_word_elim___redArg(v_word_272_);
lean_dec(v_word_272_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim(lean_object* v_motive_274_, uint8_t v_t_275_, lean_object* v_h_276_, lean_object* v_word_277_){
_start:
{
lean_inc(v_word_277_);
return v_word_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim___boxed(lean_object* v_motive_278_, lean_object* v_t_279_, lean_object* v_h_280_, lean_object* v_word_281_){
_start:
{
uint8_t v_t_boxed_282_; lean_object* v_res_283_; 
v_t_boxed_282_ = lean_unbox(v_t_279_);
v_res_283_ = l_Lean_Meta_Hint_DiffGranularity_word_elim(v_motive_278_, v_t_boxed_282_, v_h_280_, v_word_281_);
lean_dec(v_word_281_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim___redArg(lean_object* v_all_284_){
_start:
{
lean_inc(v_all_284_);
return v_all_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim___redArg___boxed(lean_object* v_all_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_Meta_Hint_DiffGranularity_all_elim___redArg(v_all_285_);
lean_dec(v_all_285_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim(lean_object* v_motive_287_, uint8_t v_t_288_, lean_object* v_h_289_, lean_object* v_all_290_){
_start:
{
lean_inc(v_all_290_);
return v_all_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim___boxed(lean_object* v_motive_291_, lean_object* v_t_292_, lean_object* v_h_293_, lean_object* v_all_294_){
_start:
{
uint8_t v_t_boxed_295_; lean_object* v_res_296_; 
v_t_boxed_295_ = lean_unbox(v_t_292_);
v_res_296_ = l_Lean_Meta_Hint_DiffGranularity_all_elim(v_motive_291_, v_t_boxed_295_, v_h_293_, v_all_294_);
lean_dec(v_all_294_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim___redArg(lean_object* v_none_297_){
_start:
{
lean_inc(v_none_297_);
return v_none_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim___redArg___boxed(lean_object* v_none_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Meta_Hint_DiffGranularity_none_elim___redArg(v_none_298_);
lean_dec(v_none_298_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim(lean_object* v_motive_300_, uint8_t v_t_301_, lean_object* v_h_302_, lean_object* v_none_303_){
_start:
{
lean_inc(v_none_303_);
return v_none_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim___boxed(lean_object* v_motive_304_, lean_object* v_t_305_, lean_object* v_h_306_, lean_object* v_none_307_){
_start:
{
uint8_t v_t_boxed_308_; lean_object* v_res_309_; 
v_t_boxed_308_ = lean_unbox(v_t_305_);
v_res_309_ = l_Lean_Meta_Hint_DiffGranularity_none_elim(v_motive_304_, v_t_boxed_308_, v_h_306_, v_none_307_);
lean_dec(v_none_307_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_instCoeSuggestionTextSuggestion___lam__0(lean_object* v_t_310_){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; lean_object* v___x_314_; 
v___x_311_ = lean_box(0);
v___x_312_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_312_, 0, v_t_310_);
lean_ctor_set(v___x_312_, 1, v___x_311_);
lean_ctor_set(v___x_312_, 2, v___x_311_);
lean_ctor_set(v___x_312_, 3, v___x_311_);
lean_ctor_set(v___x_312_, 4, v___x_311_);
lean_ctor_set(v___x_312_, 5, v___x_311_);
v___x_313_ = 0;
v___x_314_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_314_, 0, v___x_312_);
lean_ctor_set(v___x_314_, 1, v___x_311_);
lean_ctor_set(v___x_314_, 2, v___x_311_);
lean_ctor_set_uint8(v___x_314_, sizeof(void*)*3, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_instToMessageDataSuggestion___lam__0(lean_object* v_s_317_){
_start:
{
lean_object* v_toTryThisSuggestion_318_; lean_object* v_messageData_x3f_319_; 
v_toTryThisSuggestion_318_ = lean_ctor_get(v_s_317_, 0);
lean_inc_ref(v_toTryThisSuggestion_318_);
lean_dec_ref(v_s_317_);
v_messageData_x3f_319_ = lean_ctor_get(v_toTryThisSuggestion_318_, 4);
if (lean_obj_tag(v_messageData_x3f_319_) == 0)
{
lean_object* v_suggestion_320_; 
v_suggestion_320_ = lean_ctor_get(v_toTryThisSuggestion_318_, 0);
lean_inc_ref(v_suggestion_320_);
lean_dec_ref(v_toTryThisSuggestion_318_);
if (lean_obj_tag(v_suggestion_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_322_; 
v_a_321_ = lean_ctor_get(v_suggestion_320_, 1);
lean_inc(v_a_321_);
lean_dec_ref_known(v_suggestion_320_, 2);
v___x_322_ = l_Lean_MessageData_ofSyntax(v_a_321_);
return v___x_322_;
}
else
{
lean_object* v_a_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_331_; 
v_a_323_ = lean_ctor_get(v_suggestion_320_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v_suggestion_320_);
if (v_isSharedCheck_331_ == 0)
{
v___x_325_ = v_suggestion_320_;
v_isShared_326_ = v_isSharedCheck_331_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_a_323_);
lean_dec(v_suggestion_320_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_331_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
lean_ctor_set_tag(v___x_325_, 3);
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_a_323_);
v___x_328_ = v_reuseFailAlloc_330_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_MessageData_ofFormat(v___x_328_);
return v___x_329_;
}
}
}
}
else
{
lean_object* v_val_332_; 
lean_inc_ref(v_messageData_x3f_319_);
lean_dec_ref(v_toTryThisSuggestion_318_);
v_val_332_ = lean_ctor_get(v_messageData_x3f_319_, 0);
lean_inc(v_val_332_);
lean_dec_ref_known(v_messageData_x3f_319_, 1);
return v_val_332_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(lean_object* v_as_335_, size_t v_i_336_, size_t v_stop_337_, lean_object* v_b_338_){
_start:
{
lean_object* v___y_340_; uint8_t v___x_344_; 
v___x_344_ = lean_usize_dec_eq(v_i_336_, v_stop_337_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v_fst_346_; lean_object* v_snd_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_384_; 
v___x_345_ = lean_array_uget(v_as_335_, v_i_336_);
v_fst_346_ = lean_ctor_get(v___x_345_, 0);
v_snd_347_ = lean_ctor_get(v___x_345_, 1);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_345_);
if (v_isSharedCheck_384_ == 0)
{
v___x_349_ = v___x_345_;
v_isShared_350_ = v_isSharedCheck_384_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_snd_347_);
lean_inc(v_fst_346_);
lean_dec(v___x_345_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_384_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
lean_object* v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_351_ = lean_array_get_size(v_b_338_);
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = lean_nat_dec_eq(v___x_351_, v___x_352_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v_fst_357_; lean_object* v_snd_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_376_; 
lean_del_object(v___x_349_);
v___x_354_ = lean_unsigned_to_nat(1u);
v___x_355_ = lean_nat_sub(v___x_351_, v___x_354_);
v___x_356_ = lean_array_fget(v_b_338_, v___x_355_);
v_fst_357_ = lean_ctor_get(v___x_356_, 0);
v_snd_358_ = lean_ctor_get(v___x_356_, 1);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_376_ == 0)
{
v___x_360_ = v___x_356_;
v_isShared_361_ = v_isSharedCheck_376_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_snd_358_);
lean_inc(v_fst_357_);
lean_dec(v___x_356_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_376_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
uint8_t v___x_362_; uint8_t v___x_363_; uint8_t v___x_364_; 
v___x_362_ = lean_unbox(v_fst_346_);
v___x_363_ = lean_unbox(v_fst_357_);
lean_dec(v_fst_357_);
v___x_364_ = l_Lean_Diff_instBEqAction_beq(v___x_362_, v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
lean_dec(v_snd_358_);
lean_dec(v___x_355_);
v___x_365_ = lean_mk_empty_array_with_capacity(v___x_354_);
v___x_366_ = lean_array_push(v___x_365_, v_snd_347_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v___x_366_);
lean_ctor_set(v___x_360_, 0, v_fst_346_);
v___x_368_ = v___x_360_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_fst_346_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v___x_366_);
v___x_368_ = v_reuseFailAlloc_370_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_369_; 
v___x_369_ = lean_array_push(v_b_338_, v___x_368_);
v___y_340_ = v___x_369_;
goto v___jp_339_;
}
}
else
{
lean_object* v___x_371_; lean_object* v___x_373_; 
v___x_371_ = lean_array_push(v_snd_358_, v_snd_347_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v___x_371_);
lean_ctor_set(v___x_360_, 0, v_fst_346_);
v___x_373_ = v___x_360_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_fst_346_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v___x_371_);
v___x_373_ = v_reuseFailAlloc_375_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; 
v___x_374_ = lean_array_fset(v_b_338_, v___x_355_, v___x_373_);
lean_dec(v___x_355_);
v___y_340_ = v___x_374_;
goto v___jp_339_;
}
}
}
}
else
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
lean_dec_ref(v_b_338_);
v___x_377_ = lean_unsigned_to_nat(1u);
v___x_378_ = lean_mk_empty_array_with_capacity(v___x_377_);
lean_inc_ref(v___x_378_);
v___x_379_ = lean_array_push(v___x_378_, v_snd_347_);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 1, v___x_379_);
v___x_381_ = v___x_349_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_fst_346_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v___x_379_);
v___x_381_ = v_reuseFailAlloc_383_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_382_; 
v___x_382_ = lean_array_push(v___x_378_, v___x_381_);
v___y_340_ = v___x_382_;
goto v___jp_339_;
}
}
}
}
else
{
return v_b_338_;
}
v___jp_339_:
{
size_t v___x_341_; size_t v___x_342_; 
v___x_341_ = ((size_t)1ULL);
v___x_342_ = lean_usize_add(v_i_336_, v___x_341_);
v_i_336_ = v___x_342_;
v_b_338_ = v___y_340_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg___boxed(lean_object* v_as_385_, lean_object* v_i_386_, lean_object* v_stop_387_, lean_object* v_b_388_){
_start:
{
size_t v_i_boxed_389_; size_t v_stop_boxed_390_; lean_object* v_res_391_; 
v_i_boxed_389_ = lean_unbox_usize(v_i_386_);
lean_dec(v_i_386_);
v_stop_boxed_390_ = lean_unbox_usize(v_stop_387_);
lean_dec(v_stop_387_);
v_res_391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_as_385_, v_i_boxed_389_, v_stop_boxed_390_, v_b_388_);
lean_dec_ref(v_as_385_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(lean_object* v_ds_394_){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_396_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg___closed__0));
v___x_397_ = lean_array_get_size(v_ds_394_);
v___x_398_ = lean_nat_dec_lt(v___x_395_, v___x_397_);
if (v___x_398_ == 0)
{
return v___x_396_;
}
else
{
uint8_t v___x_399_; 
v___x_399_ = lean_nat_dec_le(v___x_397_, v___x_397_);
if (v___x_399_ == 0)
{
if (v___x_398_ == 0)
{
return v___x_396_;
}
else
{
size_t v___x_400_; size_t v___x_401_; lean_object* v___x_402_; 
v___x_400_ = ((size_t)0ULL);
v___x_401_ = lean_usize_of_nat(v___x_397_);
v___x_402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_ds_394_, v___x_400_, v___x_401_, v___x_396_);
return v___x_402_;
}
}
else
{
size_t v___x_403_; size_t v___x_404_; lean_object* v___x_405_; 
v___x_403_ = ((size_t)0ULL);
v___x_404_ = lean_usize_of_nat(v___x_397_);
v___x_405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_ds_394_, v___x_403_, v___x_404_, v___x_396_);
return v___x_405_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg___boxed(lean_object* v_ds_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_ds_406_);
lean_dec_ref(v_ds_406_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits(lean_object* v_00_u03b1_408_, lean_object* v_ds_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_ds_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___boxed(lean_object* v_00_u03b1_411_, lean_object* v_ds_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits(v_00_u03b1_411_, v_ds_412_);
lean_dec_ref(v_ds_412_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0(lean_object* v_00_u03b1_414_, lean_object* v_as_415_, size_t v_i_416_, size_t v_stop_417_, lean_object* v_b_418_){
_start:
{
lean_object* v___x_419_; 
v___x_419_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_as_415_, v_i_416_, v_stop_417_, v_b_418_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___boxed(lean_object* v_00_u03b1_420_, lean_object* v_as_421_, lean_object* v_i_422_, lean_object* v_stop_423_, lean_object* v_b_424_){
_start:
{
size_t v_i_boxed_425_; size_t v_stop_boxed_426_; lean_object* v_res_427_; 
v_i_boxed_425_ = lean_unbox_usize(v_i_422_);
lean_dec(v_i_422_);
v_stop_boxed_426_ = lean_unbox_usize(v_stop_423_);
lean_dec(v_stop_423_);
v_res_427_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0(v_00_u03b1_420_, v_as_421_, v_i_boxed_425_, v_stop_boxed_426_, v_b_424_);
lean_dec_ref(v_as_421_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(size_t v_sz_428_, size_t v_i_429_, lean_object* v_bs_430_){
_start:
{
uint8_t v___x_431_; 
v___x_431_ = lean_usize_dec_lt(v_i_429_, v_sz_428_);
if (v___x_431_ == 0)
{
return v_bs_430_;
}
else
{
lean_object* v_v_432_; lean_object* v_fst_433_; lean_object* v_snd_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_449_; 
v_v_432_ = lean_array_uget(v_bs_430_, v_i_429_);
v_fst_433_ = lean_ctor_get(v_v_432_, 0);
v_snd_434_ = lean_ctor_get(v_v_432_, 1);
v_isSharedCheck_449_ = !lean_is_exclusive(v_v_432_);
if (v_isSharedCheck_449_ == 0)
{
v___x_436_ = v_v_432_;
v_isShared_437_ = v_isSharedCheck_449_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_snd_434_);
lean_inc(v_fst_433_);
lean_dec(v_v_432_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_449_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v_bs_x27_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_438_ = lean_unsigned_to_nat(0u);
v_bs_x27_439_ = lean_array_uset(v_bs_430_, v_i_429_, v___x_438_);
v___x_440_ = lean_array_to_list(v_snd_434_);
v___x_441_ = lean_string_mk(v___x_440_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 1, v___x_441_);
v___x_443_ = v___x_436_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_fst_433_);
lean_ctor_set(v_reuseFailAlloc_448_, 1, v___x_441_);
v___x_443_ = v_reuseFailAlloc_448_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
size_t v___x_444_; size_t v___x_445_; lean_object* v___x_446_; 
v___x_444_ = ((size_t)1ULL);
v___x_445_ = lean_usize_add(v_i_429_, v___x_444_);
v___x_446_ = lean_array_uset(v_bs_x27_439_, v_i_429_, v___x_443_);
v_i_429_ = v___x_445_;
v_bs_430_ = v___x_446_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0___boxed(lean_object* v_sz_450_, lean_object* v_i_451_, lean_object* v_bs_452_){
_start:
{
size_t v_sz_boxed_453_; size_t v_i_boxed_454_; lean_object* v_res_455_; 
v_sz_boxed_453_ = lean_unbox_usize(v_sz_450_);
lean_dec(v_sz_450_);
v_i_boxed_454_ = lean_unbox_usize(v_i_451_);
lean_dec(v_i_451_);
v_res_455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_boxed_453_, v_i_boxed_454_, v_bs_452_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(lean_object* v_d_456_){
_start:
{
lean_object* v___x_457_; size_t v_sz_458_; size_t v___x_459_; lean_object* v___x_460_; 
v___x_457_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_d_456_);
v_sz_458_ = lean_array_size(v___x_457_);
v___x_459_ = ((size_t)0ULL);
v___x_460_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_458_, v___x_459_, v___x_457_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff___boxed(lean_object* v_d_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v_d_461_);
lean_dec_ref(v_d_461_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(size_t v_sz_463_, size_t v_i_464_, lean_object* v_bs_465_){
_start:
{
uint8_t v___x_466_; 
v___x_466_ = lean_usize_dec_lt(v_i_464_, v_sz_463_);
if (v___x_466_ == 0)
{
return v_bs_465_;
}
else
{
lean_object* v_v_467_; lean_object* v___x_468_; lean_object* v_bs_x27_469_; uint8_t v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; size_t v___x_473_; size_t v___x_474_; lean_object* v___x_475_; 
v_v_467_ = lean_array_uget(v_bs_465_, v_i_464_);
v___x_468_ = lean_unsigned_to_nat(0u);
v_bs_x27_469_ = lean_array_uset(v_bs_465_, v_i_464_, v___x_468_);
v___x_470_ = 0;
v___x_471_ = lean_box(v___x_470_);
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v_v_467_);
v___x_473_ = ((size_t)1ULL);
v___x_474_ = lean_usize_add(v_i_464_, v___x_473_);
v___x_475_ = lean_array_uset(v_bs_x27_469_, v_i_464_, v___x_472_);
v_i_464_ = v___x_474_;
v_bs_465_ = v___x_475_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9___boxed(lean_object* v_sz_477_, lean_object* v_i_478_, lean_object* v_bs_479_){
_start:
{
size_t v_sz_boxed_480_; size_t v_i_boxed_481_; lean_object* v_res_482_; 
v_sz_boxed_480_ = lean_unbox_usize(v_sz_477_);
lean_dec(v_sz_477_);
v_i_boxed_481_ = lean_unbox_usize(v_i_478_);
lean_dec(v_i_478_);
v_res_482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(v_sz_boxed_480_, v_i_boxed_481_, v_bs_479_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(lean_object* v___x_483_, lean_object* v_edited_484_, lean_object* v_a_485_){
_start:
{
lean_object* v_fst_486_; lean_object* v_snd_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_506_; 
v_fst_486_ = lean_ctor_get(v_a_485_, 0);
v_snd_487_ = lean_ctor_get(v_a_485_, 1);
v_isSharedCheck_506_ = !lean_is_exclusive(v_a_485_);
if (v_isSharedCheck_506_ == 0)
{
v___x_489_ = v_a_485_;
v_isShared_490_ = v_isSharedCheck_506_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_snd_487_);
lean_inc(v_fst_486_);
lean_dec(v_a_485_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_506_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
uint8_t v___x_491_; 
v___x_491_ = lean_nat_dec_lt(v_snd_487_, v___x_483_);
if (v___x_491_ == 0)
{
lean_object* v___x_493_; 
if (v_isShared_490_ == 0)
{
v___x_493_ = v___x_489_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_fst_486_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_snd_487_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
else
{
uint8_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_499_; 
v___x_495_ = 0;
v___x_496_ = lean_array_fget_borrowed(v_edited_484_, v_snd_487_);
v___x_497_ = lean_box(v___x_495_);
lean_inc(v___x_496_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 1, v___x_496_);
lean_ctor_set(v___x_489_, 0, v___x_497_);
v___x_499_ = v___x_489_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v___x_496_);
v___x_499_ = v_reuseFailAlloc_505_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_500_ = lean_array_push(v_fst_486_, v___x_499_);
v___x_501_ = lean_unsigned_to_nat(1u);
v___x_502_ = lean_nat_add(v_snd_487_, v___x_501_);
lean_dec(v_snd_487_);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_500_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
v_a_485_ = v___x_503_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg___boxed(lean_object* v___x_507_, lean_object* v_edited_508_, lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_507_, v_edited_508_, v_a_509_);
lean_dec_ref(v_edited_508_);
lean_dec(v___x_507_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(lean_object* v___x_511_, lean_object* v_original_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_fst_514_; lean_object* v_snd_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_534_; 
v_fst_514_ = lean_ctor_get(v_a_513_, 0);
v_snd_515_ = lean_ctor_get(v_a_513_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v_a_513_);
if (v_isSharedCheck_534_ == 0)
{
v___x_517_ = v_a_513_;
v_isShared_518_ = v_isSharedCheck_534_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_snd_515_);
lean_inc(v_fst_514_);
lean_dec(v_a_513_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_534_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
uint8_t v___x_519_; 
v___x_519_ = lean_nat_dec_lt(v_snd_515_, v___x_511_);
if (v___x_519_ == 0)
{
lean_object* v___x_521_; 
if (v_isShared_518_ == 0)
{
v___x_521_ = v___x_517_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_fst_514_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_snd_515_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
else
{
uint8_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_523_ = 1;
v___x_524_ = lean_array_fget_borrowed(v_original_512_, v_snd_515_);
v___x_525_ = lean_box(v___x_523_);
lean_inc(v___x_524_);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 1, v___x_524_);
lean_ctor_set(v___x_517_, 0, v___x_525_);
v___x_527_ = v___x_517_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_525_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v___x_524_);
v___x_527_ = v_reuseFailAlloc_533_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_528_ = lean_array_push(v_fst_514_, v___x_527_);
v___x_529_ = lean_unsigned_to_nat(1u);
v___x_530_ = lean_nat_add(v_snd_515_, v___x_529_);
lean_dec(v_snd_515_);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_528_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v_a_513_ = v___x_531_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg___boxed(lean_object* v___x_535_, lean_object* v_original_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_535_, v_original_536_, v_a_537_);
lean_dec_ref(v_original_536_);
lean_dec(v___x_535_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11_spec__21___redArg(lean_object* v_m_539_, uint32_t v_query_540_, lean_object* v_x_541_, lean_object* v_x_542_, lean_object* v_x_543_){
_start:
{
lean_object* v_zero_544_; uint8_t v_isZero_545_; 
v_zero_544_ = lean_unsigned_to_nat(0u);
v_isZero_545_ = lean_nat_dec_eq(v_x_542_, v_zero_544_);
if (v_isZero_545_ == 1)
{
lean_dec(v_x_543_);
lean_dec(v_x_542_);
if (lean_obj_tag(v_x_541_) == 0)
{
lean_object* v___x_546_; 
v___x_546_ = lean_box(2);
return v___x_546_;
}
else
{
lean_object* v_val_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v_val_547_ = lean_ctor_get(v_x_541_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v_x_541_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v_x_541_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_val_547_);
lean_dec(v_x_541_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_val_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
}
else
{
lean_object* v_keyArray_555_; lean_object* v_valueArray_556_; lean_object* v___x_557_; uint8_t v_isSome_558_; 
v_keyArray_555_ = lean_ctor_get(v_m_539_, 1);
v_valueArray_556_ = lean_ctor_get(v_m_539_, 2);
v___x_557_ = lean_array_fget_borrowed(v_keyArray_555_, v_x_543_);
v_isSome_558_ = lean_noption_is_some(v___x_557_);
if (v_isSome_558_ == 0)
{
lean_dec(v_x_542_);
if (lean_obj_tag(v_x_541_) == 0)
{
lean_object* v___x_559_; 
v___x_559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_559_, 0, v_x_543_);
return v___x_559_;
}
else
{
lean_object* v_val_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_567_; 
lean_dec(v_x_543_);
v_val_560_ = lean_ctor_get(v_x_541_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v_x_541_);
if (v_isSharedCheck_567_ == 0)
{
v___x_562_ = v_x_541_;
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_val_560_);
lean_dec(v_x_541_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_567_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_565_; 
if (v_isShared_563_ == 0)
{
v___x_565_ = v___x_562_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_val_560_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
else
{
lean_object* v_one_568_; lean_object* v_n_569_; lean_object* v___y_571_; 
v_one_568_ = lean_unsigned_to_nat(1u);
v_n_569_ = lean_nat_sub(v_x_542_, v_one_568_);
lean_dec(v_x_542_);
if (v_isSome_558_ == 0)
{
goto v___jp_577_;
}
else
{
lean_object* v___x_579_; uint8_t v_isSome_580_; 
v___x_579_ = lean_array_fget_borrowed(v_valueArray_556_, v_x_543_);
v_isSome_580_ = lean_noption_is_some(v___x_579_);
if (v_isSome_580_ == 0)
{
goto v___jp_577_;
}
else
{
lean_object* v_val_581_; uint32_t v___x_582_; uint8_t v___x_583_; 
lean_inc(v___x_557_);
v_val_581_ = lean_noption_get(v___x_557_);
v___x_582_ = lean_unbox_uint32(v_val_581_);
v___x_583_ = lean_uint32_dec_eq(v___x_582_, v_query_540_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
lean_dec(v_val_581_);
v___x_584_ = lean_array_get_size(v_keyArray_555_);
v___x_585_ = lean_nat_add(v_x_543_, v_one_568_);
lean_dec(v_x_543_);
v___x_586_ = lean_nat_dec_lt(v___x_585_, v___x_584_);
if (v___x_586_ == 0)
{
lean_dec(v___x_585_);
v_x_542_ = v_n_569_;
v_x_543_ = v_zero_544_;
goto _start;
}
else
{
v_x_542_ = v_n_569_;
v_x_543_ = v___x_585_;
goto _start;
}
}
else
{
lean_object* v_val_589_; lean_object* v___x_590_; 
lean_dec(v_n_569_);
lean_dec(v_x_541_);
lean_inc(v___x_579_);
v_val_589_ = lean_noption_get(v___x_579_);
v___x_590_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_590_, 0, v_x_543_);
lean_ctor_set(v___x_590_, 1, v_val_581_);
lean_ctor_set(v___x_590_, 2, v_val_589_);
return v___x_590_;
}
}
}
v___jp_570_:
{
lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_572_ = lean_array_get_size(v_keyArray_555_);
v___x_573_ = lean_nat_add(v_x_543_, v_one_568_);
lean_dec(v_x_543_);
v___x_574_ = lean_nat_dec_lt(v___x_573_, v___x_572_);
if (v___x_574_ == 0)
{
lean_dec(v___x_573_);
v_x_541_ = v___y_571_;
v_x_542_ = v_n_569_;
v_x_543_ = v_zero_544_;
goto _start;
}
else
{
v_x_541_ = v___y_571_;
v_x_542_ = v_n_569_;
v_x_543_ = v___x_573_;
goto _start;
}
}
v___jp_577_:
{
if (lean_obj_tag(v_x_541_) == 0)
{
lean_object* v___x_578_; 
lean_inc(v_x_543_);
v___x_578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_578_, 0, v_x_543_);
v___y_571_ = v___x_578_;
goto v___jp_570_;
}
else
{
v___y_571_ = v_x_541_;
goto v___jp_570_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11_spec__21___redArg___boxed(lean_object* v_m_591_, lean_object* v_query_592_, lean_object* v_x_593_, lean_object* v_x_594_, lean_object* v_x_595_){
_start:
{
uint32_t v_query_boxed_596_; lean_object* v_res_597_; 
v_query_boxed_596_ = lean_unbox_uint32(v_query_592_);
lean_dec(v_query_592_);
v_res_597_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11_spec__21___redArg(v_m_591_, v_query_boxed_596_, v_x_593_, v_x_594_, v_x_595_);
lean_dec_ref(v_m_591_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11___redArg(lean_object* v_m_598_, uint32_t v_query_599_){
_start:
{
lean_object* v_keyArray_600_; lean_object* v___x_601_; uint64_t v___x_602_; uint64_t v___x_603_; uint64_t v___x_604_; uint64_t v_fold_605_; uint64_t v___x_606_; uint64_t v___x_607_; uint64_t v___x_608_; size_t v___x_609_; size_t v___x_610_; size_t v___x_611_; size_t v___x_612_; size_t v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v_keyArray_600_ = lean_ctor_get(v_m_598_, 1);
v___x_601_ = lean_array_get_size(v_keyArray_600_);
v___x_602_ = lean_uint32_to_uint64(v_query_599_);
v___x_603_ = 32ULL;
v___x_604_ = lean_uint64_shift_right(v___x_602_, v___x_603_);
v_fold_605_ = lean_uint64_xor(v___x_602_, v___x_604_);
v___x_606_ = 16ULL;
v___x_607_ = lean_uint64_shift_right(v_fold_605_, v___x_606_);
v___x_608_ = lean_uint64_xor(v_fold_605_, v___x_607_);
v___x_609_ = lean_uint64_to_usize(v___x_608_);
v___x_610_ = lean_usize_of_nat(v___x_601_);
v___x_611_ = ((size_t)1ULL);
v___x_612_ = lean_usize_sub(v___x_610_, v___x_611_);
v___x_613_ = lean_usize_land(v___x_609_, v___x_612_);
v___x_614_ = lean_usize_to_nat(v___x_613_);
v___x_615_ = lean_box(0);
v___x_616_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11_spec__21___redArg(v_m_598_, v_query_599_, v___x_615_, v___x_601_, v___x_614_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11___redArg___boxed(lean_object* v_m_617_, lean_object* v_query_618_){
_start:
{
uint32_t v_query_boxed_619_; lean_object* v_res_620_; 
v_query_boxed_619_ = lean_unbox_uint32(v_query_618_);
lean_dec(v_query_618_);
v_res_620_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11___redArg(v_m_617_, v_query_boxed_619_);
lean_dec_ref(v_m_617_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23_spec__28___redArg(lean_object* v_b_621_, lean_object* v_acc_622_, lean_object* v_i_623_){
_start:
{
lean_object* v___y_625_; lean_object* v_keyArray_633_; lean_object* v_valueArray_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v_keyArray_633_ = lean_ctor_get(v_b_621_, 1);
v_valueArray_634_ = lean_ctor_get(v_b_621_, 2);
v___x_635_ = lean_array_get_size(v_keyArray_633_);
v___x_636_ = lean_nat_dec_lt(v_i_623_, v___x_635_);
if (v___x_636_ == 0)
{
lean_dec(v_i_623_);
return v_acc_622_;
}
else
{
lean_object* v___x_637_; uint8_t v_isSome_638_; 
v___x_637_ = lean_array_fget_borrowed(v_keyArray_633_, v_i_623_);
v_isSome_638_ = lean_noption_is_some(v___x_637_);
if (v_isSome_638_ == 0)
{
goto v___jp_629_;
}
else
{
lean_object* v___x_639_; uint8_t v_isSome_640_; 
v___x_639_ = lean_array_fget_borrowed(v_valueArray_634_, v_i_623_);
v_isSome_640_ = lean_noption_is_some(v___x_639_);
if (v_isSome_640_ == 0)
{
goto v___jp_629_;
}
else
{
lean_object* v_val_641_; lean_object* v_val_642_; lean_object* v_i_644_; uint32_t v___x_649_; lean_object* v___x_650_; 
lean_inc(v___x_637_);
v_val_641_ = lean_noption_get(v___x_637_);
lean_inc(v___x_639_);
v_val_642_ = lean_noption_get(v___x_639_);
v___x_649_ = lean_unbox_uint32(v_val_641_);
v___x_650_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11___redArg(v_acc_622_, v___x_649_);
switch(lean_obj_tag(v___x_650_))
{
case 0:
{
lean_object* v_index_651_; lean_object* v_size_652_; lean_object* v___x_653_; 
v_index_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_index_651_);
lean_dec_ref_known(v___x_650_, 3);
v_size_652_ = lean_ctor_get(v_acc_622_, 0);
lean_inc(v_size_652_);
v___x_653_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_622_, v_size_652_, v_index_651_, v_val_641_, v_val_642_);
lean_dec(v_index_651_);
v___y_625_ = v___x_653_;
goto v___jp_624_;
}
case 1:
{
lean_object* v_index_654_; 
v_index_654_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_index_654_);
lean_dec_ref_known(v___x_650_, 1);
v_i_644_ = v_index_654_;
goto v___jp_643_;
}
default: 
{
lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_655_ = lean_unsigned_to_nat(0u);
v___x_656_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_622_, v___x_655_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_index_657_; 
v_index_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_index_657_);
lean_dec_ref_known(v___x_656_, 1);
v_i_644_ = v_index_657_;
goto v___jp_643_;
}
else
{
lean_dec(v_val_642_);
lean_dec(v_val_641_);
v___y_625_ = v_acc_622_;
goto v___jp_624_;
}
}
}
v___jp_643_:
{
lean_object* v_size_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v_size_645_ = lean_ctor_get(v_acc_622_, 0);
v___x_646_ = lean_unsigned_to_nat(1u);
v___x_647_ = lean_nat_add(v_size_645_, v___x_646_);
v___x_648_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_622_, v___x_647_, v_i_644_, v_val_641_, v_val_642_);
lean_dec(v_i_644_);
v___y_625_ = v___x_648_;
goto v___jp_624_;
}
}
}
}
v___jp_624_:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = lean_nat_add(v_i_623_, v___x_626_);
lean_dec(v_i_623_);
v_acc_622_ = v___y_625_;
v_i_623_ = v___x_627_;
goto _start;
}
v___jp_629_:
{
lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_630_ = lean_unsigned_to_nat(1u);
v___x_631_ = lean_nat_add(v_i_623_, v___x_630_);
lean_dec(v_i_623_);
v_i_623_ = v___x_631_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23_spec__28___redArg___boxed(lean_object* v_b_658_, lean_object* v_acc_659_, lean_object* v_i_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23_spec__28___redArg(v_b_658_, v_acc_659_, v_i_660_);
lean_dec_ref(v_b_658_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23___redArg(lean_object* v_init_662_, lean_object* v_b_663_){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23_spec__28___redArg(v_b_663_, v_init_662_, v___x_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23___redArg___boxed(lean_object* v_init_666_, lean_object* v_b_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23___redArg(v_init_666_, v_b_667_);
lean_dec_ref(v_b_667_);
return v_res_668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12___redArg(lean_object* v_m_669_){
_start:
{
lean_object* v_keyArray_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v_cellCount_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v_target_677_; lean_object* v___x_678_; 
v_keyArray_670_ = lean_ctor_get(v_m_669_, 1);
v___x_671_ = lean_array_get_size(v_keyArray_670_);
v___x_672_ = lean_unsigned_to_nat(2u);
v_cellCount_673_ = lean_nat_mul(v___x_671_, v___x_672_);
v___x_674_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_673_);
v___x_675_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_673_);
v___x_676_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_673_);
v_target_677_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_677_, 0, v___x_674_);
lean_ctor_set(v_target_677_, 1, v___x_675_);
lean_ctor_set(v_target_677_, 2, v___x_676_);
v___x_678_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23___redArg(v_target_677_, v_m_669_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12___redArg___boxed(lean_object* v_m_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12___redArg(v_m_679_);
lean_dec_ref(v_m_679_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10_spec__19___redArg(lean_object* v_m_681_, uint32_t v_query_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11___redArg(v_m_681_, v_query_682_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_index_684_; lean_object* v_key_685_; lean_object* v_value_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_693_; 
v_index_684_ = lean_ctor_get(v___x_683_, 0);
v_key_685_ = lean_ctor_get(v___x_683_, 1);
v_value_686_ = lean_ctor_get(v___x_683_, 2);
v_isSharedCheck_693_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_693_ == 0)
{
v___x_688_ = v___x_683_;
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_value_686_);
lean_inc(v_key_685_);
lean_inc(v_index_684_);
lean_dec(v___x_683_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_693_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_689_ == 0)
{
v___x_691_ = v___x_688_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_index_684_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_key_685_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v_value_686_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
else
{
lean_object* v___x_694_; 
lean_dec(v___x_683_);
v___x_694_ = lean_box(1);
return v___x_694_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10_spec__19___redArg___boxed(lean_object* v_m_695_, lean_object* v_query_696_){
_start:
{
uint32_t v_query_boxed_697_; lean_object* v_res_698_; 
v_query_boxed_697_ = lean_unbox_uint32(v_query_696_);
lean_dec(v_query_696_);
v_res_698_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10_spec__19___redArg(v_m_695_, v_query_boxed_697_);
lean_dec_ref(v_m_695_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10___redArg(lean_object* v_m_699_, uint32_t v_a_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10_spec__19___redArg(v_m_699_, v_a_700_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_value_702_; lean_object* v___x_703_; 
v_value_702_ = lean_ctor_get(v___x_701_, 2);
lean_inc(v_value_702_);
lean_dec_ref_known(v___x_701_, 3);
v___x_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_703_, 0, v_value_702_);
return v___x_703_;
}
else
{
lean_object* v___x_704_; 
v___x_704_ = lean_box(0);
return v___x_704_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10___redArg___boxed(lean_object* v_m_705_, lean_object* v_a_706_){
_start:
{
uint32_t v_a_boxed_707_; lean_object* v_res_708_; 
v_a_boxed_707_ = lean_unbox_uint32(v_a_706_);
lean_dec(v_a_706_);
v_res_708_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10___redArg(v_m_705_, v_a_boxed_707_);
lean_dec_ref(v_m_705_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(lean_object* v_histogram_709_, lean_object* v_index_710_, uint32_t v_val_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10___redArg(v_histogram_709_, v_val_711_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___y_719_; lean_object* v_i_720_; lean_object* v___y_726_; lean_object* v___y_736_; lean_object* v_i_737_; lean_object* v___x_752_; 
v___x_713_ = lean_unsigned_to_nat(1u);
v___x_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_714_, 0, v_index_710_);
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = lean_box(0);
v___x_717_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_717_, 0, v___x_713_);
lean_ctor_set(v___x_717_, 1, v___x_714_);
lean_ctor_set(v___x_717_, 2, v___x_715_);
lean_ctor_set(v___x_717_, 3, v___x_716_);
v___x_752_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11___redArg(v_histogram_709_, v_val_711_);
switch(lean_obj_tag(v___x_752_))
{
case 0:
{
lean_object* v_index_753_; lean_object* v_size_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v_index_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_index_753_);
lean_dec_ref_known(v___x_752_, 3);
v_size_754_ = lean_ctor_get(v_histogram_709_, 0);
lean_inc(v_size_754_);
v___x_755_ = lean_box_uint32(v_val_711_);
v___x_756_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_709_, v_size_754_, v_index_753_, v___x_755_, v___x_717_);
lean_dec(v_index_753_);
return v___x_756_;
}
case 1:
{
lean_object* v_index_757_; lean_object* v_size_758_; lean_object* v_keyArray_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v_index_757_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_index_757_);
lean_dec_ref_known(v___x_752_, 1);
v_size_758_ = lean_ctor_get(v_histogram_709_, 0);
v_keyArray_759_ = lean_ctor_get(v_histogram_709_, 1);
v___x_760_ = lean_nat_add(v_size_758_, v___x_713_);
v___x_761_ = lean_array_get_size(v_keyArray_759_);
v___x_762_ = lean_nat_dec_lt(v___x_760_, v___x_761_);
if (v___x_762_ == 0)
{
lean_dec(v___x_760_);
lean_dec(v_index_757_);
goto v___jp_742_;
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
v___x_763_ = lean_unsigned_to_nat(4u);
v___x_764_ = lean_nat_mul(v___x_760_, v___x_763_);
v___x_765_ = lean_unsigned_to_nat(3u);
v___x_766_ = lean_nat_mul(v___x_761_, v___x_765_);
v___x_767_ = lean_nat_dec_le(v___x_764_, v___x_766_);
lean_dec(v___x_766_);
lean_dec(v___x_764_);
if (v___x_767_ == 0)
{
lean_dec(v___x_760_);
lean_dec(v_index_757_);
goto v___jp_742_;
}
else
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = lean_box_uint32(v_val_711_);
v___x_769_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_709_, v___x_760_, v_index_757_, v___x_768_, v___x_717_);
lean_dec(v_index_757_);
return v___x_769_;
}
}
}
default: 
{
lean_object* v_size_770_; lean_object* v_keyArray_771_; lean_object* v___x_772_; lean_object* v___x_773_; uint8_t v___x_774_; 
v_size_770_ = lean_ctor_get(v_histogram_709_, 0);
v_keyArray_771_ = lean_ctor_get(v_histogram_709_, 1);
v___x_772_ = lean_nat_add(v_size_770_, v___x_713_);
v___x_773_ = lean_array_get_size(v_keyArray_771_);
v___x_774_ = lean_nat_dec_lt(v___x_772_, v___x_773_);
if (v___x_774_ == 0)
{
lean_object* v___x_775_; 
lean_dec(v___x_772_);
v___x_775_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12___redArg(v_histogram_709_);
lean_dec_ref(v_histogram_709_);
v___y_726_ = v___x_775_;
goto v___jp_725_;
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_776_ = lean_unsigned_to_nat(4u);
v___x_777_ = lean_nat_mul(v___x_772_, v___x_776_);
lean_dec(v___x_772_);
v___x_778_ = lean_unsigned_to_nat(3u);
v___x_779_ = lean_nat_mul(v___x_773_, v___x_778_);
v___x_780_ = lean_nat_dec_le(v___x_777_, v___x_779_);
lean_dec(v___x_779_);
lean_dec(v___x_777_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; 
v___x_781_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12___redArg(v_histogram_709_);
lean_dec_ref(v_histogram_709_);
v___y_726_ = v___x_781_;
goto v___jp_725_;
}
else
{
v___y_726_ = v_histogram_709_;
goto v___jp_725_;
}
}
}
}
v___jp_718_:
{
lean_object* v_size_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v_size_721_ = lean_ctor_get(v___y_719_, 0);
v___x_722_ = lean_nat_add(v_size_721_, v___x_713_);
v___x_723_ = lean_box_uint32(v_val_711_);
v___x_724_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_719_, v___x_722_, v_i_720_, v___x_723_, v___x_717_);
lean_dec(v_i_720_);
return v___x_724_;
}
v___jp_725_:
{
lean_object* v___x_727_; 
v___x_727_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11___redArg(v___y_726_, v_val_711_);
switch(lean_obj_tag(v___x_727_))
{
case 0:
{
lean_object* v_index_728_; lean_object* v_size_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_index_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_index_728_);
lean_dec_ref_known(v___x_727_, 3);
v_size_729_ = lean_ctor_get(v___y_726_, 0);
lean_inc(v_size_729_);
v___x_730_ = lean_box_uint32(v_val_711_);
v___x_731_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_726_, v_size_729_, v_index_728_, v___x_730_, v___x_717_);
lean_dec(v_index_728_);
return v___x_731_;
}
case 1:
{
lean_object* v_index_732_; 
v_index_732_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_index_732_);
lean_dec_ref_known(v___x_727_, 1);
v___y_719_ = v___y_726_;
v_i_720_ = v_index_732_;
goto v___jp_718_;
}
default: 
{
lean_object* v___x_733_; 
v___x_733_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_726_, v___x_715_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_index_734_; 
v_index_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_index_734_);
lean_dec_ref_known(v___x_733_, 1);
v___y_719_ = v___y_726_;
v_i_720_ = v_index_734_;
goto v___jp_718_;
}
else
{
lean_dec_ref_known(v___x_717_, 4);
return v___y_726_;
}
}
}
}
v___jp_735_:
{
lean_object* v_size_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v_size_738_ = lean_ctor_get(v___y_736_, 0);
v___x_739_ = lean_nat_add(v_size_738_, v___x_713_);
v___x_740_ = lean_box_uint32(v_val_711_);
v___x_741_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_736_, v___x_739_, v_i_737_, v___x_740_, v___x_717_);
lean_dec(v_i_737_);
return v___x_741_;
}
v___jp_742_:
{
lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_743_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12___redArg(v_histogram_709_);
lean_dec_ref(v_histogram_709_);
v___x_744_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11___redArg(v___x_743_, v_val_711_);
switch(lean_obj_tag(v___x_744_))
{
case 0:
{
lean_object* v_index_745_; lean_object* v_size_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_index_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_index_745_);
lean_dec_ref_known(v___x_744_, 3);
v_size_746_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_size_746_);
v___x_747_ = lean_box_uint32(v_val_711_);
v___x_748_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_743_, v_size_746_, v_index_745_, v___x_747_, v___x_717_);
lean_dec(v_index_745_);
return v___x_748_;
}
case 1:
{
lean_object* v_index_749_; 
v_index_749_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_index_749_);
lean_dec_ref_known(v___x_744_, 1);
v___y_736_ = v___x_743_;
v_i_737_ = v_index_749_;
goto v___jp_735_;
}
default: 
{
lean_object* v___x_750_; 
v___x_750_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_743_, v___x_715_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_index_751_; 
v_index_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_index_751_);
lean_dec_ref_known(v___x_750_, 1);
v___y_736_ = v___x_743_;
v_i_737_ = v_index_751_;
goto v___jp_735_;
}
else
{
lean_dec_ref_known(v___x_717_, 4);
return v___x_743_;
}
}
}
}
}
else
{
lean_object* v_val_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_868_; 
v_val_782_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_868_ == 0)
{
v___x_784_ = v___x_712_;
v_isShared_785_ = v_isSharedCheck_868_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_val_782_);
lean_dec(v___x_712_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_868_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v_leftCount_786_; lean_object* v_rightCount_787_; lean_object* v_rightIndex_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_866_; 
v_leftCount_786_ = lean_ctor_get(v_val_782_, 0);
v_rightCount_787_ = lean_ctor_get(v_val_782_, 2);
v_rightIndex_788_ = lean_ctor_get(v_val_782_, 3);
v_isSharedCheck_866_ = !lean_is_exclusive(v_val_782_);
if (v_isSharedCheck_866_ == 0)
{
lean_object* v_unused_867_; 
v_unused_867_ = lean_ctor_get(v_val_782_, 1);
lean_dec(v_unused_867_);
v___x_790_ = v_val_782_;
v_isShared_791_ = v_isSharedCheck_866_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_rightIndex_788_);
lean_inc(v_rightCount_787_);
lean_inc(v_leftCount_786_);
lean_dec(v_val_782_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_866_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_795_; 
v___x_792_ = lean_unsigned_to_nat(1u);
v___x_793_ = lean_nat_add(v_leftCount_786_, v___x_792_);
lean_dec(v_leftCount_786_);
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 0, v_index_710_);
v___x_795_ = v___x_784_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_index_710_);
v___x_795_ = v_reuseFailAlloc_865_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
lean_object* v___x_797_; 
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 1, v___x_795_);
lean_ctor_set(v___x_790_, 0, v___x_793_);
v___x_797_ = v___x_790_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_793_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v___x_795_);
lean_ctor_set(v_reuseFailAlloc_864_, 2, v_rightCount_787_);
lean_ctor_set(v_reuseFailAlloc_864_, 3, v_rightIndex_788_);
v___x_797_ = v_reuseFailAlloc_864_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
lean_object* v___y_799_; lean_object* v_i_800_; lean_object* v___y_806_; lean_object* v___y_817_; lean_object* v_i_818_; lean_object* v___x_834_; 
v___x_834_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11___redArg(v_histogram_709_, v_val_711_);
switch(lean_obj_tag(v___x_834_))
{
case 0:
{
lean_object* v_index_835_; lean_object* v_size_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v_index_835_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_index_835_);
lean_dec_ref_known(v___x_834_, 3);
v_size_836_ = lean_ctor_get(v_histogram_709_, 0);
lean_inc(v_size_836_);
v___x_837_ = lean_box_uint32(v_val_711_);
v___x_838_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_709_, v_size_836_, v_index_835_, v___x_837_, v___x_797_);
lean_dec(v_index_835_);
return v___x_838_;
}
case 1:
{
lean_object* v_index_839_; lean_object* v_size_840_; lean_object* v_keyArray_841_; lean_object* v___x_842_; lean_object* v___x_843_; uint8_t v___x_844_; 
v_index_839_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_index_839_);
lean_dec_ref_known(v___x_834_, 1);
v_size_840_ = lean_ctor_get(v_histogram_709_, 0);
v_keyArray_841_ = lean_ctor_get(v_histogram_709_, 1);
v___x_842_ = lean_nat_add(v_size_840_, v___x_792_);
v___x_843_ = lean_array_get_size(v_keyArray_841_);
v___x_844_ = lean_nat_dec_lt(v___x_842_, v___x_843_);
if (v___x_844_ == 0)
{
lean_dec(v___x_842_);
lean_dec(v_index_839_);
goto v___jp_823_;
}
else
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_845_ = lean_unsigned_to_nat(4u);
v___x_846_ = lean_nat_mul(v___x_842_, v___x_845_);
v___x_847_ = lean_unsigned_to_nat(3u);
v___x_848_ = lean_nat_mul(v___x_843_, v___x_847_);
v___x_849_ = lean_nat_dec_le(v___x_846_, v___x_848_);
lean_dec(v___x_848_);
lean_dec(v___x_846_);
if (v___x_849_ == 0)
{
lean_dec(v___x_842_);
lean_dec(v_index_839_);
goto v___jp_823_;
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_box_uint32(v_val_711_);
v___x_851_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_709_, v___x_842_, v_index_839_, v___x_850_, v___x_797_);
lean_dec(v_index_839_);
return v___x_851_;
}
}
}
default: 
{
lean_object* v_size_852_; lean_object* v_keyArray_853_; lean_object* v___x_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v_size_852_ = lean_ctor_get(v_histogram_709_, 0);
v_keyArray_853_ = lean_ctor_get(v_histogram_709_, 1);
v___x_854_ = lean_nat_add(v_size_852_, v___x_792_);
v___x_855_ = lean_array_get_size(v_keyArray_853_);
v___x_856_ = lean_nat_dec_lt(v___x_854_, v___x_855_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; 
lean_dec(v___x_854_);
v___x_857_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12___redArg(v_histogram_709_);
lean_dec_ref(v_histogram_709_);
v___y_806_ = v___x_857_;
goto v___jp_805_;
}
else
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; uint8_t v___x_862_; 
v___x_858_ = lean_unsigned_to_nat(4u);
v___x_859_ = lean_nat_mul(v___x_854_, v___x_858_);
lean_dec(v___x_854_);
v___x_860_ = lean_unsigned_to_nat(3u);
v___x_861_ = lean_nat_mul(v___x_855_, v___x_860_);
v___x_862_ = lean_nat_dec_le(v___x_859_, v___x_861_);
lean_dec(v___x_861_);
lean_dec(v___x_859_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; 
v___x_863_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12___redArg(v_histogram_709_);
lean_dec_ref(v_histogram_709_);
v___y_806_ = v___x_863_;
goto v___jp_805_;
}
else
{
v___y_806_ = v_histogram_709_;
goto v___jp_805_;
}
}
}
}
v___jp_798_:
{
lean_object* v_size_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; 
v_size_801_ = lean_ctor_get(v___y_799_, 0);
v___x_802_ = lean_nat_add(v_size_801_, v___x_792_);
v___x_803_ = lean_box_uint32(v_val_711_);
v___x_804_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_799_, v___x_802_, v_i_800_, v___x_803_, v___x_797_);
lean_dec(v_i_800_);
return v___x_804_;
}
v___jp_805_:
{
lean_object* v___x_807_; 
v___x_807_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11___redArg(v___y_806_, v_val_711_);
switch(lean_obj_tag(v___x_807_))
{
case 0:
{
lean_object* v_index_808_; lean_object* v_size_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v_index_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_index_808_);
lean_dec_ref_known(v___x_807_, 3);
v_size_809_ = lean_ctor_get(v___y_806_, 0);
lean_inc(v_size_809_);
v___x_810_ = lean_box_uint32(v_val_711_);
v___x_811_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_806_, v_size_809_, v_index_808_, v___x_810_, v___x_797_);
lean_dec(v_index_808_);
return v___x_811_;
}
case 1:
{
lean_object* v_index_812_; 
v_index_812_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_index_812_);
lean_dec_ref_known(v___x_807_, 1);
v___y_799_ = v___y_806_;
v_i_800_ = v_index_812_;
goto v___jp_798_;
}
default: 
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_unsigned_to_nat(0u);
v___x_814_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_806_, v___x_813_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_index_815_; 
v_index_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_index_815_);
lean_dec_ref_known(v___x_814_, 1);
v___y_799_ = v___y_806_;
v_i_800_ = v_index_815_;
goto v___jp_798_;
}
else
{
lean_dec_ref(v___x_797_);
return v___y_806_;
}
}
}
}
v___jp_816_:
{
lean_object* v_size_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v_size_819_ = lean_ctor_get(v___y_817_, 0);
v___x_820_ = lean_nat_add(v_size_819_, v___x_792_);
v___x_821_ = lean_box_uint32(v_val_711_);
v___x_822_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_817_, v___x_820_, v_i_818_, v___x_821_, v___x_797_);
lean_dec(v_i_818_);
return v___x_822_;
}
v___jp_823_:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12___redArg(v_histogram_709_);
lean_dec_ref(v_histogram_709_);
v___x_825_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11___redArg(v___x_824_, v_val_711_);
switch(lean_obj_tag(v___x_825_))
{
case 0:
{
lean_object* v_index_826_; lean_object* v_size_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_index_826_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_index_826_);
lean_dec_ref_known(v___x_825_, 3);
v_size_827_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_size_827_);
v___x_828_ = lean_box_uint32(v_val_711_);
v___x_829_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_824_, v_size_827_, v_index_826_, v___x_828_, v___x_797_);
lean_dec(v_index_826_);
return v___x_829_;
}
case 1:
{
lean_object* v_index_830_; 
v_index_830_ = lean_ctor_get(v___x_825_, 0);
lean_inc(v_index_830_);
lean_dec_ref_known(v___x_825_, 1);
v___y_817_ = v___x_824_;
v_i_818_ = v_index_830_;
goto v___jp_816_;
}
default: 
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_unsigned_to_nat(0u);
v___x_832_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_824_, v___x_831_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_index_833_; 
v_index_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_index_833_);
lean_dec_ref_known(v___x_832_, 1);
v___y_817_ = v___x_824_;
v_i_818_ = v_index_833_;
goto v___jp_816_;
}
else
{
lean_dec_ref(v___x_797_);
return v___x_824_;
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
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg___boxed(lean_object* v_histogram_869_, lean_object* v_index_870_, lean_object* v_val_871_){
_start:
{
uint32_t v_val_boxed_872_; lean_object* v_res_873_; 
v_val_boxed_872_ = lean_unbox_uint32(v_val_871_);
lean_dec(v_val_871_);
v_res_873_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(v_histogram_869_, v_index_870_, v_val_boxed_872_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(lean_object* v_upperBound_874_, lean_object* v_fst_875_, lean_object* v___x_876_, lean_object* v_fst_877_, lean_object* v_a_878_, lean_object* v_b_879_){
_start:
{
uint8_t v___x_880_; 
v___x_880_ = lean_nat_dec_lt(v_a_878_, v_upperBound_874_);
if (v___x_880_ == 0)
{
lean_dec(v_a_878_);
return v_b_879_;
}
else
{
lean_object* v___x_881_; uint32_t v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_881_ = l_Subarray_get___redArg(v_fst_877_, v_a_878_);
v___x_882_ = lean_unbox_uint32(v___x_881_);
lean_dec(v___x_881_);
lean_inc(v_a_878_);
v___x_883_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(v_b_879_, v_a_878_, v___x_882_);
v___x_884_ = lean_unsigned_to_nat(1u);
v___x_885_ = lean_nat_add(v_a_878_, v___x_884_);
lean_dec(v_a_878_);
v_a_878_ = v___x_885_;
v_b_879_ = v___x_883_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg___boxed(lean_object* v_upperBound_887_, lean_object* v_fst_888_, lean_object* v___x_889_, lean_object* v_fst_890_, lean_object* v_a_891_, lean_object* v_b_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(v_upperBound_887_, v_fst_888_, v___x_889_, v_fst_890_, v_a_891_, v_b_892_);
lean_dec_ref(v_fst_890_);
lean_dec(v___x_889_);
lean_dec_ref(v_fst_888_);
lean_dec(v_upperBound_887_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5(lean_object* v_b_894_, lean_object* v_acc_895_, lean_object* v_i_896_){
_start:
{
lean_object* v_keyArray_901_; lean_object* v_valueArray_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v_keyArray_901_ = lean_ctor_get(v_b_894_, 1);
v_valueArray_902_ = lean_ctor_get(v_b_894_, 2);
v___x_903_ = lean_array_get_size(v_keyArray_901_);
v___x_904_ = lean_nat_dec_lt(v_i_896_, v___x_903_);
if (v___x_904_ == 0)
{
lean_dec(v_i_896_);
lean_inc(v_acc_895_);
return v_acc_895_;
}
else
{
lean_object* v___x_905_; uint8_t v_isSome_906_; 
v___x_905_ = lean_array_fget_borrowed(v_keyArray_901_, v_i_896_);
v_isSome_906_ = lean_noption_is_some(v___x_905_);
if (v_isSome_906_ == 0)
{
goto v___jp_897_;
}
else
{
lean_object* v___x_907_; uint8_t v_isSome_908_; 
v___x_907_ = lean_array_fget_borrowed(v_valueArray_902_, v_i_896_);
v_isSome_908_ = lean_noption_is_some(v___x_907_);
if (v_isSome_908_ == 0)
{
goto v___jp_897_;
}
else
{
lean_object* v_val_909_; lean_object* v_val_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
lean_inc(v___x_905_);
v_val_909_ = lean_noption_get(v___x_905_);
lean_inc(v___x_907_);
v_val_910_ = lean_noption_get(v___x_907_);
v___x_911_ = lean_unsigned_to_nat(1u);
v___x_912_ = lean_nat_add(v_i_896_, v___x_911_);
lean_dec(v_i_896_);
v___x_913_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5(v_b_894_, v_acc_895_, v___x_912_);
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v_val_909_);
lean_ctor_set(v___x_914_, 1, v_val_910_);
v___x_915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
lean_ctor_set(v___x_915_, 1, v___x_913_);
return v___x_915_;
}
}
}
v___jp_897_:
{
lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_898_ = lean_unsigned_to_nat(1u);
v___x_899_ = lean_nat_add(v_i_896_, v___x_898_);
lean_dec(v_i_896_);
v_i_896_ = v___x_899_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___boxed(lean_object* v_b_916_, lean_object* v_acc_917_, lean_object* v_i_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5(v_b_916_, v_acc_917_, v_i_918_);
lean_dec(v_acc_917_);
lean_dec_ref(v_b_916_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3_spec__4(lean_object* v_left_920_, lean_object* v_right_921_, lean_object* v_pref_922_){
_start:
{
lean_object* v_start_923_; lean_object* v_stop_924_; lean_object* v_i_925_; lean_object* v___x_931_; uint8_t v___x_932_; 
v_start_923_ = lean_ctor_get(v_left_920_, 1);
v_stop_924_ = lean_ctor_get(v_left_920_, 2);
v_i_925_ = lean_array_get_size(v_pref_922_);
v___x_931_ = lean_nat_sub(v_stop_924_, v_start_923_);
v___x_932_ = lean_nat_dec_lt(v_i_925_, v___x_931_);
lean_dec(v___x_931_);
if (v___x_932_ == 0)
{
goto v___jp_926_;
}
else
{
lean_object* v_start_933_; lean_object* v_stop_934_; lean_object* v___x_935_; uint8_t v___x_936_; 
v_start_933_ = lean_ctor_get(v_right_921_, 1);
v_stop_934_ = lean_ctor_get(v_right_921_, 2);
v___x_935_ = lean_nat_sub(v_stop_934_, v_start_933_);
v___x_936_ = lean_nat_dec_lt(v_i_925_, v___x_935_);
lean_dec(v___x_935_);
if (v___x_936_ == 0)
{
goto v___jp_926_;
}
else
{
lean_object* v___x_937_; lean_object* v___x_938_; uint32_t v___x_939_; uint32_t v___x_940_; uint8_t v___x_941_; 
v___x_937_ = l_Subarray_get___redArg(v_left_920_, v_i_925_);
v___x_938_ = l_Subarray_get___redArg(v_right_921_, v_i_925_);
v___x_939_ = lean_unbox_uint32(v___x_937_);
v___x_940_ = lean_unbox_uint32(v___x_938_);
lean_dec(v___x_938_);
v___x_941_ = lean_uint32_dec_eq(v___x_939_, v___x_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
lean_dec(v___x_937_);
v___x_942_ = l_Subarray_drop___redArg(v_left_920_, v_i_925_);
v___x_943_ = l_Subarray_drop___redArg(v_right_921_, v_i_925_);
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_942_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v_pref_922_);
lean_ctor_set(v___x_945_, 1, v___x_944_);
return v___x_945_;
}
else
{
lean_object* v___x_946_; 
v___x_946_ = lean_array_push(v_pref_922_, v___x_937_);
v_pref_922_ = v___x_946_;
goto _start;
}
}
}
v___jp_926_:
{
lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_927_ = l_Subarray_drop___redArg(v_left_920_, v_i_925_);
v___x_928_ = l_Subarray_drop___redArg(v_right_921_, v_i_925_);
v___x_929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_927_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_930_, 0, v_pref_922_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
return v___x_930_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3(lean_object* v_left_948_, lean_object* v_right_949_){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_951_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3_spec__4(v_left_948_, v_right_949_, v___x_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7___redArg(lean_object* v_histogram_952_, lean_object* v_index_953_, uint32_t v_val_954_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10___redArg(v_histogram_952_, v_val_954_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___y_962_; lean_object* v_i_963_; lean_object* v___y_969_; lean_object* v___y_979_; lean_object* v_i_980_; lean_object* v___x_995_; 
v___x_956_ = lean_unsigned_to_nat(0u);
v___x_957_ = lean_box(0);
v___x_958_ = lean_unsigned_to_nat(1u);
v___x_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_959_, 0, v_index_953_);
v___x_960_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_960_, 0, v___x_956_);
lean_ctor_set(v___x_960_, 1, v___x_957_);
lean_ctor_set(v___x_960_, 2, v___x_958_);
lean_ctor_set(v___x_960_, 3, v___x_959_);
v___x_995_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11___redArg(v_histogram_952_, v_val_954_);
switch(lean_obj_tag(v___x_995_))
{
case 0:
{
lean_object* v_index_996_; lean_object* v_size_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v_index_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_index_996_);
lean_dec_ref_known(v___x_995_, 3);
v_size_997_ = lean_ctor_get(v_histogram_952_, 0);
lean_inc(v_size_997_);
v___x_998_ = lean_box_uint32(v_val_954_);
v___x_999_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_952_, v_size_997_, v_index_996_, v___x_998_, v___x_960_);
lean_dec(v_index_996_);
return v___x_999_;
}
case 1:
{
lean_object* v_index_1000_; lean_object* v_size_1001_; lean_object* v_keyArray_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v_index_1000_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_index_1000_);
lean_dec_ref_known(v___x_995_, 1);
v_size_1001_ = lean_ctor_get(v_histogram_952_, 0);
v_keyArray_1002_ = lean_ctor_get(v_histogram_952_, 1);
v___x_1003_ = lean_nat_add(v_size_1001_, v___x_958_);
v___x_1004_ = lean_array_get_size(v_keyArray_1002_);
v___x_1005_ = lean_nat_dec_lt(v___x_1003_, v___x_1004_);
if (v___x_1005_ == 0)
{
lean_dec(v___x_1003_);
lean_dec(v_index_1000_);
goto v___jp_985_;
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; 
v___x_1006_ = lean_unsigned_to_nat(4u);
v___x_1007_ = lean_nat_mul(v___x_1003_, v___x_1006_);
v___x_1008_ = lean_unsigned_to_nat(3u);
v___x_1009_ = lean_nat_mul(v___x_1004_, v___x_1008_);
v___x_1010_ = lean_nat_dec_le(v___x_1007_, v___x_1009_);
lean_dec(v___x_1009_);
lean_dec(v___x_1007_);
if (v___x_1010_ == 0)
{
lean_dec(v___x_1003_);
lean_dec(v_index_1000_);
goto v___jp_985_;
}
else
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = lean_box_uint32(v_val_954_);
v___x_1012_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_952_, v___x_1003_, v_index_1000_, v___x_1011_, v___x_960_);
lean_dec(v_index_1000_);
return v___x_1012_;
}
}
}
default: 
{
lean_object* v_size_1013_; lean_object* v_keyArray_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v_size_1013_ = lean_ctor_get(v_histogram_952_, 0);
v_keyArray_1014_ = lean_ctor_get(v_histogram_952_, 1);
v___x_1015_ = lean_nat_add(v_size_1013_, v___x_958_);
v___x_1016_ = lean_array_get_size(v_keyArray_1014_);
v___x_1017_ = lean_nat_dec_lt(v___x_1015_, v___x_1016_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; 
lean_dec(v___x_1015_);
v___x_1018_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12___redArg(v_histogram_952_);
lean_dec_ref(v_histogram_952_);
v___y_969_ = v___x_1018_;
goto v___jp_968_;
}
else
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; uint8_t v___x_1023_; 
v___x_1019_ = lean_unsigned_to_nat(4u);
v___x_1020_ = lean_nat_mul(v___x_1015_, v___x_1019_);
lean_dec(v___x_1015_);
v___x_1021_ = lean_unsigned_to_nat(3u);
v___x_1022_ = lean_nat_mul(v___x_1016_, v___x_1021_);
v___x_1023_ = lean_nat_dec_le(v___x_1020_, v___x_1022_);
lean_dec(v___x_1022_);
lean_dec(v___x_1020_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; 
v___x_1024_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12___redArg(v_histogram_952_);
lean_dec_ref(v_histogram_952_);
v___y_969_ = v___x_1024_;
goto v___jp_968_;
}
else
{
v___y_969_ = v_histogram_952_;
goto v___jp_968_;
}
}
}
}
v___jp_961_:
{
lean_object* v_size_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v_size_964_ = lean_ctor_get(v___y_962_, 0);
v___x_965_ = lean_nat_add(v_size_964_, v___x_958_);
v___x_966_ = lean_box_uint32(v_val_954_);
v___x_967_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_962_, v___x_965_, v_i_963_, v___x_966_, v___x_960_);
lean_dec(v_i_963_);
return v___x_967_;
}
v___jp_968_:
{
lean_object* v___x_970_; 
v___x_970_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11___redArg(v___y_969_, v_val_954_);
switch(lean_obj_tag(v___x_970_))
{
case 0:
{
lean_object* v_index_971_; lean_object* v_size_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v_index_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_index_971_);
lean_dec_ref_known(v___x_970_, 3);
v_size_972_ = lean_ctor_get(v___y_969_, 0);
lean_inc(v_size_972_);
v___x_973_ = lean_box_uint32(v_val_954_);
v___x_974_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_969_, v_size_972_, v_index_971_, v___x_973_, v___x_960_);
lean_dec(v_index_971_);
return v___x_974_;
}
case 1:
{
lean_object* v_index_975_; 
v_index_975_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_index_975_);
lean_dec_ref_known(v___x_970_, 1);
v___y_962_ = v___y_969_;
v_i_963_ = v_index_975_;
goto v___jp_961_;
}
default: 
{
lean_object* v___x_976_; 
v___x_976_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_969_, v___x_956_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_index_977_; 
v_index_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_index_977_);
lean_dec_ref_known(v___x_976_, 1);
v___y_962_ = v___y_969_;
v_i_963_ = v_index_977_;
goto v___jp_961_;
}
else
{
lean_dec_ref_known(v___x_960_, 4);
return v___y_969_;
}
}
}
}
v___jp_978_:
{
lean_object* v_size_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_size_981_ = lean_ctor_get(v___y_979_, 0);
v___x_982_ = lean_nat_add(v_size_981_, v___x_958_);
v___x_983_ = lean_box_uint32(v_val_954_);
v___x_984_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_979_, v___x_982_, v_i_980_, v___x_983_, v___x_960_);
lean_dec(v_i_980_);
return v___x_984_;
}
v___jp_985_:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12___redArg(v_histogram_952_);
lean_dec_ref(v_histogram_952_);
v___x_987_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11___redArg(v___x_986_, v_val_954_);
switch(lean_obj_tag(v___x_987_))
{
case 0:
{
lean_object* v_index_988_; lean_object* v_size_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v_index_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_index_988_);
lean_dec_ref_known(v___x_987_, 3);
v_size_989_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_size_989_);
v___x_990_ = lean_box_uint32(v_val_954_);
v___x_991_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_986_, v_size_989_, v_index_988_, v___x_990_, v___x_960_);
lean_dec(v_index_988_);
return v___x_991_;
}
case 1:
{
lean_object* v_index_992_; 
v_index_992_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_index_992_);
lean_dec_ref_known(v___x_987_, 1);
v___y_979_ = v___x_986_;
v_i_980_ = v_index_992_;
goto v___jp_978_;
}
default: 
{
lean_object* v___x_993_; 
v___x_993_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_986_, v___x_956_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_index_994_; 
v_index_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_index_994_);
lean_dec_ref_known(v___x_993_, 1);
v___y_979_ = v___x_986_;
v_i_980_ = v_index_994_;
goto v___jp_978_;
}
else
{
lean_dec_ref_known(v___x_960_, 4);
return v___x_986_;
}
}
}
}
}
else
{
lean_object* v_val_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1111_; 
v_val_1025_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1027_ = v___x_955_;
v_isShared_1028_ = v_isSharedCheck_1111_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_val_1025_);
lean_dec(v___x_955_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1111_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v_leftCount_1029_; lean_object* v_leftIndex_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1108_; 
v_leftCount_1029_ = lean_ctor_get(v_val_1025_, 0);
v_leftIndex_1030_ = lean_ctor_get(v_val_1025_, 1);
v_isSharedCheck_1108_ = !lean_is_exclusive(v_val_1025_);
if (v_isSharedCheck_1108_ == 0)
{
lean_object* v_unused_1109_; lean_object* v_unused_1110_; 
v_unused_1109_ = lean_ctor_get(v_val_1025_, 3);
lean_dec(v_unused_1109_);
v_unused_1110_ = lean_ctor_get(v_val_1025_, 2);
lean_dec(v_unused_1110_);
v___x_1032_ = v_val_1025_;
v_isShared_1033_ = v_isSharedCheck_1108_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_leftIndex_1030_);
lean_inc(v_leftCount_1029_);
lean_dec(v_val_1025_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1108_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1034_ = lean_unsigned_to_nat(1u);
v___x_1035_ = lean_nat_add(v_leftCount_1029_, v___x_1034_);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v_index_953_);
v___x_1037_ = v___x_1027_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_index_953_);
v___x_1037_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
lean_object* v___x_1039_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 3, v___x_1037_);
lean_ctor_set(v___x_1032_, 2, v___x_1035_);
v___x_1039_ = v___x_1032_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_leftCount_1029_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_leftIndex_1030_);
lean_ctor_set(v_reuseFailAlloc_1106_, 2, v___x_1035_);
lean_ctor_set(v_reuseFailAlloc_1106_, 3, v___x_1037_);
v___x_1039_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
lean_object* v___y_1041_; lean_object* v_i_1042_; lean_object* v___y_1048_; lean_object* v___y_1059_; lean_object* v_i_1060_; lean_object* v___x_1076_; 
v___x_1076_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11___redArg(v_histogram_952_, v_val_954_);
switch(lean_obj_tag(v___x_1076_))
{
case 0:
{
lean_object* v_index_1077_; lean_object* v_size_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v_index_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_index_1077_);
lean_dec_ref_known(v___x_1076_, 3);
v_size_1078_ = lean_ctor_get(v_histogram_952_, 0);
lean_inc(v_size_1078_);
v___x_1079_ = lean_box_uint32(v_val_954_);
v___x_1080_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_952_, v_size_1078_, v_index_1077_, v___x_1079_, v___x_1039_);
lean_dec(v_index_1077_);
return v___x_1080_;
}
case 1:
{
lean_object* v_index_1081_; lean_object* v_size_1082_; lean_object* v_keyArray_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v_index_1081_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_index_1081_);
lean_dec_ref_known(v___x_1076_, 1);
v_size_1082_ = lean_ctor_get(v_histogram_952_, 0);
v_keyArray_1083_ = lean_ctor_get(v_histogram_952_, 1);
v___x_1084_ = lean_nat_add(v_size_1082_, v___x_1034_);
v___x_1085_ = lean_array_get_size(v_keyArray_1083_);
v___x_1086_ = lean_nat_dec_lt(v___x_1084_, v___x_1085_);
if (v___x_1086_ == 0)
{
lean_dec(v___x_1084_);
lean_dec(v_index_1081_);
goto v___jp_1065_;
}
else
{
lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; uint8_t v___x_1091_; 
v___x_1087_ = lean_unsigned_to_nat(4u);
v___x_1088_ = lean_nat_mul(v___x_1084_, v___x_1087_);
v___x_1089_ = lean_unsigned_to_nat(3u);
v___x_1090_ = lean_nat_mul(v___x_1085_, v___x_1089_);
v___x_1091_ = lean_nat_dec_le(v___x_1088_, v___x_1090_);
lean_dec(v___x_1090_);
lean_dec(v___x_1088_);
if (v___x_1091_ == 0)
{
lean_dec(v___x_1084_);
lean_dec(v_index_1081_);
goto v___jp_1065_;
}
else
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = lean_box_uint32(v_val_954_);
v___x_1093_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_952_, v___x_1084_, v_index_1081_, v___x_1092_, v___x_1039_);
lean_dec(v_index_1081_);
return v___x_1093_;
}
}
}
default: 
{
lean_object* v_size_1094_; lean_object* v_keyArray_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; uint8_t v___x_1098_; 
v_size_1094_ = lean_ctor_get(v_histogram_952_, 0);
v_keyArray_1095_ = lean_ctor_get(v_histogram_952_, 1);
v___x_1096_ = lean_nat_add(v_size_1094_, v___x_1034_);
v___x_1097_ = lean_array_get_size(v_keyArray_1095_);
v___x_1098_ = lean_nat_dec_lt(v___x_1096_, v___x_1097_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; 
lean_dec(v___x_1096_);
v___x_1099_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12___redArg(v_histogram_952_);
lean_dec_ref(v_histogram_952_);
v___y_1048_ = v___x_1099_;
goto v___jp_1047_;
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v___x_1100_ = lean_unsigned_to_nat(4u);
v___x_1101_ = lean_nat_mul(v___x_1096_, v___x_1100_);
lean_dec(v___x_1096_);
v___x_1102_ = lean_unsigned_to_nat(3u);
v___x_1103_ = lean_nat_mul(v___x_1097_, v___x_1102_);
v___x_1104_ = lean_nat_dec_le(v___x_1101_, v___x_1103_);
lean_dec(v___x_1103_);
lean_dec(v___x_1101_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12___redArg(v_histogram_952_);
lean_dec_ref(v_histogram_952_);
v___y_1048_ = v___x_1105_;
goto v___jp_1047_;
}
else
{
v___y_1048_ = v_histogram_952_;
goto v___jp_1047_;
}
}
}
}
v___jp_1040_:
{
lean_object* v_size_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v_size_1043_ = lean_ctor_get(v___y_1041_, 0);
v___x_1044_ = lean_nat_add(v_size_1043_, v___x_1034_);
v___x_1045_ = lean_box_uint32(v_val_954_);
v___x_1046_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1041_, v___x_1044_, v_i_1042_, v___x_1045_, v___x_1039_);
lean_dec(v_i_1042_);
return v___x_1046_;
}
v___jp_1047_:
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11___redArg(v___y_1048_, v_val_954_);
switch(lean_obj_tag(v___x_1049_))
{
case 0:
{
lean_object* v_index_1050_; lean_object* v_size_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; 
v_index_1050_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_index_1050_);
lean_dec_ref_known(v___x_1049_, 3);
v_size_1051_ = lean_ctor_get(v___y_1048_, 0);
lean_inc(v_size_1051_);
v___x_1052_ = lean_box_uint32(v_val_954_);
v___x_1053_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1048_, v_size_1051_, v_index_1050_, v___x_1052_, v___x_1039_);
lean_dec(v_index_1050_);
return v___x_1053_;
}
case 1:
{
lean_object* v_index_1054_; 
v_index_1054_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_index_1054_);
lean_dec_ref_known(v___x_1049_, 1);
v___y_1041_ = v___y_1048_;
v_i_1042_ = v_index_1054_;
goto v___jp_1040_;
}
default: 
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = lean_unsigned_to_nat(0u);
v___x_1056_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1048_, v___x_1055_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v_index_1057_; 
v_index_1057_ = lean_ctor_get(v___x_1056_, 0);
lean_inc(v_index_1057_);
lean_dec_ref_known(v___x_1056_, 1);
v___y_1041_ = v___y_1048_;
v_i_1042_ = v_index_1057_;
goto v___jp_1040_;
}
else
{
lean_dec_ref(v___x_1039_);
return v___y_1048_;
}
}
}
}
v___jp_1058_:
{
lean_object* v_size_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v_size_1061_ = lean_ctor_get(v___y_1059_, 0);
v___x_1062_ = lean_nat_add(v_size_1061_, v___x_1034_);
v___x_1063_ = lean_box_uint32(v_val_954_);
v___x_1064_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1059_, v___x_1062_, v_i_1060_, v___x_1063_, v___x_1039_);
lean_dec(v_i_1060_);
return v___x_1064_;
}
v___jp_1065_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12___redArg(v_histogram_952_);
lean_dec_ref(v_histogram_952_);
v___x_1067_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11___redArg(v___x_1066_, v_val_954_);
switch(lean_obj_tag(v___x_1067_))
{
case 0:
{
lean_object* v_index_1068_; lean_object* v_size_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_index_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_index_1068_);
lean_dec_ref_known(v___x_1067_, 3);
v_size_1069_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_size_1069_);
v___x_1070_ = lean_box_uint32(v_val_954_);
v___x_1071_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1066_, v_size_1069_, v_index_1068_, v___x_1070_, v___x_1039_);
lean_dec(v_index_1068_);
return v___x_1071_;
}
case 1:
{
lean_object* v_index_1072_; 
v_index_1072_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_index_1072_);
lean_dec_ref_known(v___x_1067_, 1);
v___y_1059_ = v___x_1066_;
v_i_1060_ = v_index_1072_;
goto v___jp_1058_;
}
default: 
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_unsigned_to_nat(0u);
v___x_1074_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1066_, v___x_1073_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_index_1075_; 
v_index_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_index_1075_);
lean_dec_ref_known(v___x_1074_, 1);
v___y_1059_ = v___x_1066_;
v_i_1060_ = v_index_1075_;
goto v___jp_1058_;
}
else
{
lean_dec_ref(v___x_1039_);
return v___x_1066_;
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
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7___redArg___boxed(lean_object* v_histogram_1112_, lean_object* v_index_1113_, lean_object* v_val_1114_){
_start:
{
uint32_t v_val_boxed_1115_; lean_object* v_res_1116_; 
v_val_boxed_1115_ = lean_unbox_uint32(v_val_1114_);
lean_dec(v_val_1114_);
v_res_1116_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7___redArg(v_histogram_1112_, v_index_1113_, v_val_boxed_1115_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(lean_object* v_upperBound_1117_, lean_object* v___x_1118_, lean_object* v_fst_1119_, lean_object* v___x_1120_, lean_object* v_a_1121_, lean_object* v_b_1122_){
_start:
{
uint8_t v___x_1123_; 
v___x_1123_ = lean_nat_dec_lt(v_a_1121_, v_upperBound_1117_);
if (v___x_1123_ == 0)
{
lean_dec(v_a_1121_);
return v_b_1122_;
}
else
{
lean_object* v___x_1124_; uint32_t v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1124_ = l_Subarray_get___redArg(v_fst_1119_, v_a_1121_);
v___x_1125_ = lean_unbox_uint32(v___x_1124_);
lean_dec(v___x_1124_);
lean_inc(v_a_1121_);
v___x_1126_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7___redArg(v_b_1122_, v_a_1121_, v___x_1125_);
v___x_1127_ = lean_unsigned_to_nat(1u);
v___x_1128_ = lean_nat_add(v_a_1121_, v___x_1127_);
lean_dec(v_a_1121_);
v_a_1121_ = v___x_1128_;
v_b_1122_ = v___x_1126_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg___boxed(lean_object* v_upperBound_1130_, lean_object* v___x_1131_, lean_object* v_fst_1132_, lean_object* v___x_1133_, lean_object* v_a_1134_, lean_object* v_b_1135_){
_start:
{
lean_object* v_res_1136_; 
v_res_1136_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(v_upperBound_1130_, v___x_1131_, v_fst_1132_, v___x_1133_, v_a_1134_, v_b_1135_);
lean_dec(v___x_1133_);
lean_dec_ref(v_fst_1132_);
lean_dec(v___x_1131_);
lean_dec(v_upperBound_1130_);
return v_res_1136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(lean_object* v_a_1137_, lean_object* v_b_1138_){
_start:
{
lean_object* v_array_1139_; lean_object* v_start_1140_; lean_object* v_stop_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1154_; 
v_array_1139_ = lean_ctor_get(v_a_1137_, 0);
v_start_1140_ = lean_ctor_get(v_a_1137_, 1);
v_stop_1141_ = lean_ctor_get(v_a_1137_, 2);
v_isSharedCheck_1154_ = !lean_is_exclusive(v_a_1137_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1143_ = v_a_1137_;
v_isShared_1144_ = v_isSharedCheck_1154_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_stop_1141_);
lean_inc(v_start_1140_);
lean_inc(v_array_1139_);
lean_dec(v_a_1137_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1154_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
uint8_t v___x_1145_; 
v___x_1145_ = lean_nat_dec_lt(v_start_1140_, v_stop_1141_);
if (v___x_1145_ == 0)
{
lean_del_object(v___x_1143_);
lean_dec(v_stop_1141_);
lean_dec(v_start_1140_);
lean_dec_ref(v_array_1139_);
return v_b_1138_;
}
else
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1146_ = lean_unsigned_to_nat(1u);
v___x_1147_ = lean_nat_add(v_start_1140_, v___x_1146_);
lean_inc_ref(v_array_1139_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v___x_1147_);
v___x_1149_ = v___x_1143_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_array_1139_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v_stop_1141_);
v___x_1149_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1150_ = lean_array_fget(v_array_1139_, v_start_1140_);
lean_dec(v_start_1140_);
lean_dec_ref(v_array_1139_);
v___x_1151_ = lean_array_push(v_b_1138_, v___x_1150_);
v_a_1137_ = v___x_1149_;
v_b_1138_ = v___x_1151_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6(lean_object* v_left_1155_, lean_object* v_right_1156_, lean_object* v_i_1157_){
_start:
{
lean_object* v_start_1158_; lean_object* v_stop_1159_; lean_object* v___x_1160_; uint8_t v___x_1174_; 
v_start_1158_ = lean_ctor_get(v_left_1155_, 1);
v_stop_1159_ = lean_ctor_get(v_left_1155_, 2);
v___x_1160_ = lean_nat_sub(v_stop_1159_, v_start_1158_);
v___x_1174_ = lean_nat_dec_lt(v_i_1157_, v___x_1160_);
if (v___x_1174_ == 0)
{
goto v___jp_1161_;
}
else
{
lean_object* v_start_1175_; lean_object* v_stop_1176_; lean_object* v___x_1177_; uint8_t v___x_1178_; 
v_start_1175_ = lean_ctor_get(v_right_1156_, 1);
v_stop_1176_ = lean_ctor_get(v_right_1156_, 2);
v___x_1177_ = lean_nat_sub(v_stop_1176_, v_start_1175_);
v___x_1178_ = lean_nat_dec_lt(v_i_1157_, v___x_1177_);
if (v___x_1178_ == 0)
{
lean_dec(v___x_1177_);
goto v___jp_1161_;
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; uint32_t v___x_1186_; uint32_t v___x_1187_; uint8_t v___x_1188_; 
v___x_1179_ = lean_nat_sub(v___x_1160_, v_i_1157_);
lean_dec(v___x_1160_);
v___x_1180_ = lean_unsigned_to_nat(1u);
v___x_1181_ = lean_nat_sub(v___x_1179_, v___x_1180_);
v___x_1182_ = l_Subarray_get___redArg(v_left_1155_, v___x_1181_);
lean_dec(v___x_1181_);
v___x_1183_ = lean_nat_sub(v___x_1177_, v_i_1157_);
lean_dec(v___x_1177_);
v___x_1184_ = lean_nat_sub(v___x_1183_, v___x_1180_);
v___x_1185_ = l_Subarray_get___redArg(v_right_1156_, v___x_1184_);
lean_dec(v___x_1184_);
v___x_1186_ = lean_unbox_uint32(v___x_1182_);
lean_dec(v___x_1182_);
v___x_1187_ = lean_unbox_uint32(v___x_1185_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_uint32_dec_eq(v___x_1186_, v___x_1187_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_dec(v_i_1157_);
lean_inc_ref(v_left_1155_);
v___x_1189_ = l_Subarray_take___redArg(v_left_1155_, v___x_1179_);
v___x_1190_ = l_Subarray_take___redArg(v_right_1156_, v___x_1183_);
lean_dec(v___x_1183_);
v___x_1191_ = l_Subarray_drop___redArg(v_left_1155_, v___x_1179_);
lean_dec(v___x_1179_);
v___x_1192_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_1193_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(v___x_1191_, v___x_1192_);
v___x_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1190_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1189_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
return v___x_1195_;
}
else
{
lean_object* v___x_1196_; 
lean_dec(v___x_1183_);
lean_dec(v___x_1179_);
v___x_1196_ = lean_nat_add(v_i_1157_, v___x_1180_);
lean_dec(v_i_1157_);
v_i_1157_ = v___x_1196_;
goto _start;
}
}
}
v___jp_1161_:
{
lean_object* v_start_1162_; lean_object* v_stop_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v_start_1162_ = lean_ctor_get(v_right_1156_, 1);
v_stop_1163_ = lean_ctor_get(v_right_1156_, 2);
v___x_1164_ = lean_nat_sub(v___x_1160_, v_i_1157_);
lean_dec(v___x_1160_);
lean_inc_ref(v_left_1155_);
v___x_1165_ = l_Subarray_take___redArg(v_left_1155_, v___x_1164_);
v___x_1166_ = lean_nat_sub(v_stop_1163_, v_start_1162_);
v___x_1167_ = lean_nat_sub(v___x_1166_, v_i_1157_);
lean_dec(v_i_1157_);
lean_dec(v___x_1166_);
v___x_1168_ = l_Subarray_take___redArg(v_right_1156_, v___x_1167_);
lean_dec(v___x_1167_);
v___x_1169_ = l_Subarray_drop___redArg(v_left_1155_, v___x_1164_);
lean_dec(v___x_1164_);
v___x_1170_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_1171_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(v___x_1169_, v___x_1170_);
v___x_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1168_);
lean_ctor_set(v___x_1172_, 1, v___x_1171_);
v___x_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1165_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
return v___x_1173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4(lean_object* v_left_1198_, lean_object* v_right_1199_){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_unsigned_to_nat(0u);
v___x_1201_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6(v_left_1198_, v_right_1199_, v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6___redArg(lean_object* v_as_x27_1202_, lean_object* v_b_1203_){
_start:
{
if (lean_obj_tag(v_as_x27_1202_) == 0)
{
return v_b_1203_;
}
else
{
lean_object* v_head_1204_; lean_object* v_snd_1205_; lean_object* v_leftIndex_1206_; 
v_head_1204_ = lean_ctor_get(v_as_x27_1202_, 0);
v_snd_1205_ = lean_ctor_get(v_head_1204_, 1);
v_leftIndex_1206_ = lean_ctor_get(v_snd_1205_, 1);
if (lean_obj_tag(v_leftIndex_1206_) == 1)
{
lean_object* v_rightIndex_1207_; 
v_rightIndex_1207_ = lean_ctor_get(v_snd_1205_, 3);
if (lean_obj_tag(v_rightIndex_1207_) == 1)
{
if (lean_obj_tag(v_b_1203_) == 0)
{
lean_object* v_tail_1208_; lean_object* v_fst_1209_; lean_object* v_leftCount_1210_; lean_object* v_rightCount_1211_; lean_object* v_val_1212_; lean_object* v_val_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v_tail_1208_ = lean_ctor_get(v_as_x27_1202_, 1);
v_fst_1209_ = lean_ctor_get(v_head_1204_, 0);
v_leftCount_1210_ = lean_ctor_get(v_snd_1205_, 0);
v_rightCount_1211_ = lean_ctor_get(v_snd_1205_, 2);
v_val_1212_ = lean_ctor_get(v_leftIndex_1206_, 0);
v_val_1213_ = lean_ctor_get(v_rightIndex_1207_, 0);
v___x_1214_ = lean_nat_add(v_leftCount_1210_, v_rightCount_1211_);
lean_inc(v_val_1213_);
lean_inc(v_val_1212_);
v___x_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1215_, 0, v_val_1212_);
lean_ctor_set(v___x_1215_, 1, v_val_1213_);
lean_inc(v_fst_1209_);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v_fst_1209_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1214_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
v___x_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1217_);
v_as_x27_1202_ = v_tail_1208_;
v_b_1203_ = v___x_1218_;
goto _start;
}
else
{
lean_object* v_val_1220_; lean_object* v_tail_1221_; lean_object* v_fst_1222_; lean_object* v_leftCount_1223_; lean_object* v_rightCount_1224_; lean_object* v_val_1225_; lean_object* v_val_1226_; lean_object* v_fst_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1248_; 
v_val_1220_ = lean_ctor_get(v_b_1203_, 0);
lean_inc(v_val_1220_);
v_tail_1221_ = lean_ctor_get(v_as_x27_1202_, 1);
v_fst_1222_ = lean_ctor_get(v_head_1204_, 0);
v_leftCount_1223_ = lean_ctor_get(v_snd_1205_, 0);
v_rightCount_1224_ = lean_ctor_get(v_snd_1205_, 2);
v_val_1225_ = lean_ctor_get(v_leftIndex_1206_, 0);
v_val_1226_ = lean_ctor_get(v_rightIndex_1207_, 0);
v_fst_1227_ = lean_ctor_get(v_val_1220_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_val_1220_);
if (v_isSharedCheck_1248_ == 0)
{
lean_object* v_unused_1249_; 
v_unused_1249_ = lean_ctor_get(v_val_1220_, 1);
lean_dec(v_unused_1249_);
v___x_1229_ = v_val_1220_;
v_isShared_1230_ = v_isSharedCheck_1248_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_fst_1227_);
lean_dec(v_val_1220_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1248_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1231_ = lean_nat_add(v_leftCount_1223_, v_rightCount_1224_);
v___x_1232_ = lean_nat_dec_lt(v___x_1231_, v_fst_1227_);
lean_dec(v_fst_1227_);
if (v___x_1232_ == 0)
{
lean_dec(v___x_1231_);
lean_del_object(v___x_1229_);
v_as_x27_1202_ = v_tail_1221_;
goto _start;
}
else
{
lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1246_; 
v_isSharedCheck_1246_ = !lean_is_exclusive(v_b_1203_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; 
v_unused_1247_ = lean_ctor_get(v_b_1203_, 0);
lean_dec(v_unused_1247_);
v___x_1235_ = v_b_1203_;
v_isShared_1236_ = v_isSharedCheck_1246_;
goto v_resetjp_1234_;
}
else
{
lean_dec(v_b_1203_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1246_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
lean_inc(v_val_1226_);
lean_inc(v_val_1225_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 1, v_val_1226_);
lean_ctor_set(v___x_1229_, 0, v_val_1225_);
v___x_1238_ = v___x_1229_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_val_1225_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_val_1226_);
v___x_1238_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1242_; 
lean_inc(v_fst_1222_);
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v_fst_1222_);
lean_ctor_set(v___x_1239_, 1, v___x_1238_);
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1231_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v___x_1240_);
v___x_1242_ = v___x_1235_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1240_);
v___x_1242_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
v_as_x27_1202_ = v_tail_1221_;
v_b_1203_ = v___x_1242_;
goto _start;
}
}
}
}
}
}
}
else
{
lean_object* v_tail_1250_; 
v_tail_1250_ = lean_ctor_get(v_as_x27_1202_, 1);
v_as_x27_1202_ = v_tail_1250_;
goto _start;
}
}
else
{
lean_object* v_tail_1252_; 
v_tail_1252_ = lean_ctor_get(v_as_x27_1202_, 1);
v_as_x27_1202_ = v_tail_1252_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_as_x27_1254_, lean_object* v_b_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6___redArg(v_as_x27_1254_, v_b_1255_);
lean_dec(v_as_x27_1254_);
return v_res_1256_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v_cellCount_1257_; lean_object* v___x_1258_; 
v_cellCount_1257_ = lean_unsigned_to_nat(16u);
v___x_1258_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_1257_);
return v___x_1258_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v_cellCount_1259_; lean_object* v___x_1260_; 
v_cellCount_1259_ = lean_unsigned_to_nat(16u);
v___x_1260_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1259_);
return v___x_1260_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v_hist_1264_; 
v___x_1261_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1);
v___x_1262_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0);
v___x_1263_ = lean_unsigned_to_nat(0u);
v_hist_1264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_hist_1264_, 0, v___x_1263_);
lean_ctor_set(v_hist_1264_, 1, v___x_1262_);
lean_ctor_set(v_hist_1264_, 2, v___x_1261_);
return v_hist_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(lean_object* v_left_1265_, lean_object* v_right_1266_){
_start:
{
lean_object* v___x_1267_; lean_object* v_snd_1268_; lean_object* v_fst_1269_; lean_object* v_fst_1270_; lean_object* v_snd_1271_; lean_object* v___x_1272_; lean_object* v_snd_1273_; lean_object* v_fst_1274_; lean_object* v_fst_1275_; lean_object* v_snd_1276_; lean_object* v_start_1277_; lean_object* v_stop_1278_; lean_object* v___x_1279_; lean_object* v_hist_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v_start_1283_; lean_object* v_stop_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1267_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3(v_left_1265_, v_right_1266_);
v_snd_1268_ = lean_ctor_get(v___x_1267_, 1);
lean_inc(v_snd_1268_);
v_fst_1269_ = lean_ctor_get(v___x_1267_, 0);
lean_inc(v_fst_1269_);
lean_dec_ref(v___x_1267_);
v_fst_1270_ = lean_ctor_get(v_snd_1268_, 0);
lean_inc(v_fst_1270_);
v_snd_1271_ = lean_ctor_get(v_snd_1268_, 1);
lean_inc(v_snd_1271_);
lean_dec(v_snd_1268_);
v___x_1272_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4(v_fst_1270_, v_snd_1271_);
v_snd_1273_ = lean_ctor_get(v___x_1272_, 1);
lean_inc(v_snd_1273_);
v_fst_1274_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_fst_1274_);
lean_dec_ref(v___x_1272_);
v_fst_1275_ = lean_ctor_get(v_snd_1273_, 0);
lean_inc(v_fst_1275_);
v_snd_1276_ = lean_ctor_get(v_snd_1273_, 1);
lean_inc(v_snd_1276_);
lean_dec(v_snd_1273_);
v_start_1277_ = lean_ctor_get(v_fst_1274_, 1);
v_stop_1278_ = lean_ctor_get(v_fst_1274_, 2);
v___x_1279_ = lean_unsigned_to_nat(0u);
v_hist_1280_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__2, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__2_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__2);
v___x_1281_ = lean_nat_sub(v_stop_1278_, v_start_1277_);
v___x_1282_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(v___x_1281_, v_fst_1275_, v___x_1281_, v_fst_1274_, v___x_1279_, v_hist_1280_);
v_start_1283_ = lean_ctor_get(v_fst_1275_, 1);
v_stop_1284_ = lean_ctor_get(v_fst_1275_, 2);
v___x_1285_ = lean_nat_sub(v_stop_1284_, v_start_1283_);
v___x_1286_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(v___x_1285_, v___x_1285_, v_fst_1275_, v___x_1281_, v___x_1279_, v___x_1282_);
lean_dec(v___x_1281_);
lean_dec(v___x_1285_);
v___x_1287_ = lean_box(0);
v___x_1288_ = lean_box(0);
v___x_1289_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5(v___x_1286_, v___x_1288_, v___x_1279_);
lean_dec_ref(v___x_1286_);
v___x_1290_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6___redArg(v___x_1289_, v___x_1287_);
lean_dec(v___x_1289_);
if (lean_obj_tag(v___x_1290_) == 1)
{
lean_object* v_val_1291_; lean_object* v_snd_1292_; lean_object* v_snd_1293_; lean_object* v_fst_1294_; lean_object* v_fst_1295_; lean_object* v_snd_1296_; lean_object* v___x_1297_; lean_object* v_fst_1298_; lean_object* v_snd_1299_; lean_object* v___x_1300_; lean_object* v_fst_1301_; lean_object* v_snd_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v_val_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_val_1291_);
lean_dec_ref_known(v___x_1290_, 1);
v_snd_1292_ = lean_ctor_get(v_val_1291_, 1);
lean_inc(v_snd_1292_);
lean_dec(v_val_1291_);
v_snd_1293_ = lean_ctor_get(v_snd_1292_, 1);
lean_inc(v_snd_1293_);
v_fst_1294_ = lean_ctor_get(v_snd_1292_, 0);
lean_inc(v_fst_1294_);
lean_dec(v_snd_1292_);
v_fst_1295_ = lean_ctor_get(v_snd_1293_, 0);
lean_inc(v_fst_1295_);
v_snd_1296_ = lean_ctor_get(v_snd_1293_, 1);
lean_inc(v_snd_1296_);
lean_dec(v_snd_1293_);
v___x_1297_ = l_Subarray_split___redArg(v_fst_1274_, v_fst_1295_);
lean_dec(v_fst_1295_);
v_fst_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_fst_1298_);
v_snd_1299_ = lean_ctor_get(v___x_1297_, 1);
lean_inc(v_snd_1299_);
lean_dec_ref(v___x_1297_);
v___x_1300_ = l_Subarray_split___redArg(v_fst_1275_, v_snd_1296_);
lean_dec(v_snd_1296_);
v_fst_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_fst_1301_);
v_snd_1302_ = lean_ctor_get(v___x_1300_, 1);
lean_inc(v_snd_1302_);
lean_dec_ref(v___x_1300_);
v___x_1303_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v_fst_1298_, v_fst_1301_);
v___x_1304_ = l_Array_append___redArg(v_fst_1269_, v___x_1303_);
lean_dec_ref(v___x_1303_);
v___x_1305_ = lean_unsigned_to_nat(1u);
v___x_1306_ = lean_mk_empty_array_with_capacity(v___x_1305_);
v___x_1307_ = lean_array_push(v___x_1306_, v_fst_1294_);
v___x_1308_ = l_Array_append___redArg(v___x_1304_, v___x_1307_);
lean_dec_ref(v___x_1307_);
v___x_1309_ = l_Subarray_drop___redArg(v_snd_1299_, v___x_1305_);
v___x_1310_ = l_Subarray_drop___redArg(v_snd_1302_, v___x_1305_);
v___x_1311_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v___x_1309_, v___x_1310_);
v___x_1312_ = l_Array_append___redArg(v___x_1308_, v___x_1311_);
lean_dec_ref(v___x_1311_);
v___x_1313_ = l_Array_append___redArg(v___x_1312_, v_snd_1276_);
lean_dec(v_snd_1276_);
return v___x_1313_;
}
else
{
lean_object* v___x_1314_; 
lean_dec(v___x_1290_);
lean_dec(v_fst_1275_);
lean_dec(v_fst_1274_);
v___x_1314_ = l_Array_append___redArg(v_fst_1269_, v_snd_1276_);
lean_dec(v_snd_1276_);
return v___x_1314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(size_t v_sz_1315_, size_t v_i_1316_, lean_object* v_bs_1317_){
_start:
{
uint8_t v___x_1318_; 
v___x_1318_ = lean_usize_dec_lt(v_i_1316_, v_sz_1315_);
if (v___x_1318_ == 0)
{
return v_bs_1317_;
}
else
{
lean_object* v_v_1319_; lean_object* v___x_1320_; lean_object* v_bs_x27_1321_; uint8_t v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; size_t v___x_1325_; size_t v___x_1326_; lean_object* v___x_1327_; 
v_v_1319_ = lean_array_uget(v_bs_1317_, v_i_1316_);
v___x_1320_ = lean_unsigned_to_nat(0u);
v_bs_x27_1321_ = lean_array_uset(v_bs_1317_, v_i_1316_, v___x_1320_);
v___x_1322_ = 1;
v___x_1323_ = lean_box(v___x_1322_);
v___x_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
lean_ctor_set(v___x_1324_, 1, v_v_1319_);
v___x_1325_ = ((size_t)1ULL);
v___x_1326_ = lean_usize_add(v_i_1316_, v___x_1325_);
v___x_1327_ = lean_array_uset(v_bs_x27_1321_, v_i_1316_, v___x_1324_);
v_i_1316_ = v___x_1326_;
v_bs_1317_ = v___x_1327_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8___boxed(lean_object* v_sz_1329_, lean_object* v_i_1330_, lean_object* v_bs_1331_){
_start:
{
size_t v_sz_boxed_1332_; size_t v_i_boxed_1333_; lean_object* v_res_1334_; 
v_sz_boxed_1332_ = lean_unbox_usize(v_sz_1329_);
lean_dec(v_sz_1329_);
v_i_boxed_1333_ = lean_unbox_usize(v_i_1330_);
lean_dec(v_i_1330_);
v_res_1334_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(v_sz_boxed_1332_, v_i_boxed_1333_, v_bs_1331_);
return v_res_1334_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = 65;
v___x_1336_ = lean_box_uint32(v___x_1335_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg(lean_object* v_edited_1337_, lean_object* v___x_1338_, uint32_t v_a_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_fst_1341_; lean_object* v_snd_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1369_; 
v_fst_1341_ = lean_ctor_get(v_a_1340_, 0);
v_snd_1342_ = lean_ctor_get(v_a_1340_, 1);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_a_1340_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1344_ = v_a_1340_;
v_isShared_1345_ = v_isSharedCheck_1369_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_snd_1342_);
lean_inc(v_fst_1341_);
lean_dec(v_a_1340_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1369_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
uint8_t v___y_1347_; uint8_t v___x_1363_; 
v___x_1363_ = lean_nat_dec_lt(v_snd_1342_, v___x_1338_);
if (v___x_1363_ == 0)
{
v___y_1347_ = v___x_1363_;
goto v___jp_1346_;
}
else
{
lean_object* v___x_1364_; lean_object* v___x_1365_; uint32_t v___x_1366_; uint8_t v___x_1367_; 
v___x_1364_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1;
v___x_1365_ = lean_array_get_borrowed(v___x_1364_, v_edited_1337_, v_snd_1342_);
v___x_1366_ = lean_unbox_uint32(v___x_1365_);
v___x_1367_ = lean_uint32_dec_eq(v___x_1366_, v_a_1339_);
if (v___x_1367_ == 0)
{
v___y_1347_ = v___x_1363_;
goto v___jp_1346_;
}
else
{
lean_object* v___x_1368_; 
lean_del_object(v___x_1344_);
v___x_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1368_, 0, v_fst_1341_);
lean_ctor_set(v___x_1368_, 1, v_snd_1342_);
return v___x_1368_;
}
}
v___jp_1346_:
{
if (v___y_1347_ == 0)
{
lean_object* v___x_1349_; 
if (v_isShared_1345_ == 0)
{
v___x_1349_ = v___x_1344_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_fst_1341_);
lean_ctor_set(v_reuseFailAlloc_1350_, 1, v_snd_1342_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
else
{
uint8_t v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1351_ = 0;
v___x_1352_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1;
v___x_1353_ = lean_array_get_borrowed(v___x_1352_, v_edited_1337_, v_snd_1342_);
v___x_1354_ = lean_box(v___x_1351_);
lean_inc(v___x_1353_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 1, v___x_1353_);
lean_ctor_set(v___x_1344_, 0, v___x_1354_);
v___x_1356_ = v___x_1344_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v___x_1353_);
v___x_1356_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1357_ = lean_array_push(v_fst_1341_, v___x_1356_);
v___x_1358_ = lean_unsigned_to_nat(1u);
v___x_1359_ = lean_nat_add(v_snd_1342_, v___x_1358_);
lean_dec(v_snd_1342_);
v___x_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1357_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
v_a_1340_ = v___x_1360_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed(lean_object* v_edited_1370_, lean_object* v___x_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
uint32_t v_a_boxed_1374_; lean_object* v_res_1375_; 
v_a_boxed_1374_ = lean_unbox_uint32(v_a_1372_);
lean_dec(v_a_1372_);
v_res_1375_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg(v_edited_1370_, v___x_1371_, v_a_boxed_1374_, v_a_1373_);
lean_dec(v___x_1371_);
lean_dec_ref(v_edited_1370_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(lean_object* v_original_1376_, lean_object* v___x_1377_, uint32_t v_a_1378_, lean_object* v_a_1379_){
_start:
{
lean_object* v_fst_1380_; lean_object* v_snd_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1408_; 
v_fst_1380_ = lean_ctor_get(v_a_1379_, 0);
v_snd_1381_ = lean_ctor_get(v_a_1379_, 1);
v_isSharedCheck_1408_ = !lean_is_exclusive(v_a_1379_);
if (v_isSharedCheck_1408_ == 0)
{
v___x_1383_ = v_a_1379_;
v_isShared_1384_ = v_isSharedCheck_1408_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_snd_1381_);
lean_inc(v_fst_1380_);
lean_dec(v_a_1379_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1408_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
uint8_t v___y_1386_; uint8_t v___x_1402_; 
v___x_1402_ = lean_nat_dec_lt(v_snd_1381_, v___x_1377_);
if (v___x_1402_ == 0)
{
v___y_1386_ = v___x_1402_;
goto v___jp_1385_;
}
else
{
lean_object* v___x_1403_; lean_object* v___x_1404_; uint32_t v___x_1405_; uint8_t v___x_1406_; 
v___x_1403_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1;
v___x_1404_ = lean_array_get_borrowed(v___x_1403_, v_original_1376_, v_snd_1381_);
v___x_1405_ = lean_unbox_uint32(v___x_1404_);
v___x_1406_ = lean_uint32_dec_eq(v___x_1405_, v_a_1378_);
if (v___x_1406_ == 0)
{
v___y_1386_ = v___x_1402_;
goto v___jp_1385_;
}
else
{
lean_object* v___x_1407_; 
lean_del_object(v___x_1383_);
v___x_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1407_, 0, v_fst_1380_);
lean_ctor_set(v___x_1407_, 1, v_snd_1381_);
return v___x_1407_;
}
}
v___jp_1385_:
{
if (v___y_1386_ == 0)
{
lean_object* v___x_1388_; 
if (v_isShared_1384_ == 0)
{
v___x_1388_ = v___x_1383_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_fst_1380_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_snd_1381_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
else
{
uint8_t v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1395_; 
v___x_1390_ = 1;
v___x_1391_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1;
v___x_1392_ = lean_array_get_borrowed(v___x_1391_, v_original_1376_, v_snd_1381_);
v___x_1393_ = lean_box(v___x_1390_);
lean_inc(v___x_1392_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 1, v___x_1392_);
lean_ctor_set(v___x_1383_, 0, v___x_1393_);
v___x_1395_ = v___x_1383_;
goto v_reusejp_1394_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v___x_1392_);
v___x_1395_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1394_;
}
v_reusejp_1394_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1396_ = lean_array_push(v_fst_1380_, v___x_1395_);
v___x_1397_ = lean_unsigned_to_nat(1u);
v___x_1398_ = lean_nat_add(v_snd_1381_, v___x_1397_);
lean_dec(v_snd_1381_);
v___x_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1396_);
lean_ctor_set(v___x_1399_, 1, v___x_1398_);
v_a_1379_ = v___x_1399_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg___boxed(lean_object* v_original_1409_, lean_object* v___x_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
uint32_t v_a_boxed_1413_; lean_object* v_res_1414_; 
v_a_boxed_1413_ = lean_unbox_uint32(v_a_1411_);
lean_dec(v_a_1411_);
v_res_1414_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v_original_1409_, v___x_1410_, v_a_boxed_1413_, v_a_1412_);
lean_dec(v___x_1410_);
lean_dec_ref(v_original_1409_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__14(lean_object* v_original_1415_, lean_object* v___x_1416_, lean_object* v_edited_1417_, lean_object* v___x_1418_, lean_object* v_as_1419_, size_t v_sz_1420_, size_t v_i_1421_, lean_object* v_b_1422_){
_start:
{
uint8_t v___x_1423_; 
v___x_1423_ = lean_usize_dec_lt(v_i_1421_, v_sz_1420_);
if (v___x_1423_ == 0)
{
return v_b_1422_;
}
else
{
lean_object* v_snd_1424_; lean_object* v_fst_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1474_; 
v_snd_1424_ = lean_ctor_get(v_b_1422_, 1);
v_fst_1425_ = lean_ctor_get(v_b_1422_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_b_1422_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1427_ = v_b_1422_;
v_isShared_1428_ = v_isSharedCheck_1474_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_snd_1424_);
lean_inc(v_fst_1425_);
lean_dec(v_b_1422_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1474_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v_fst_1429_; lean_object* v_snd_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1473_; 
v_fst_1429_ = lean_ctor_get(v_snd_1424_, 0);
v_snd_1430_ = lean_ctor_get(v_snd_1424_, 1);
v_isSharedCheck_1473_ = !lean_is_exclusive(v_snd_1424_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1432_ = v_snd_1424_;
v_isShared_1433_ = v_isSharedCheck_1473_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_snd_1430_);
lean_inc(v_fst_1429_);
lean_dec(v_snd_1424_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1473_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v_a_1434_; lean_object* v___x_1436_; 
v_a_1434_ = lean_array_uget_borrowed(v_as_1419_, v_i_1421_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 1, v_fst_1429_);
lean_ctor_set(v___x_1432_, 0, v_fst_1425_);
v___x_1436_ = v___x_1432_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_fst_1425_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_fst_1429_);
v___x_1436_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
uint32_t v___x_1437_; lean_object* v___x_1438_; lean_object* v_fst_1439_; lean_object* v_snd_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1471_; 
v___x_1437_ = lean_unbox_uint32(v_a_1434_);
v___x_1438_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v_original_1415_, v___x_1416_, v___x_1437_, v___x_1436_);
v_fst_1439_ = lean_ctor_get(v___x_1438_, 0);
v_snd_1440_ = lean_ctor_get(v___x_1438_, 1);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1442_ = v___x_1438_;
v_isShared_1443_ = v_isSharedCheck_1471_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_snd_1440_);
lean_inc(v_fst_1439_);
lean_dec(v___x_1438_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1471_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 1, v_snd_1430_);
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_fst_1439_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_snd_1430_);
v___x_1445_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
uint32_t v___x_1446_; lean_object* v___x_1447_; lean_object* v_fst_1448_; lean_object* v_snd_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1469_; 
v___x_1446_ = lean_unbox_uint32(v_a_1434_);
v___x_1447_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg(v_edited_1417_, v___x_1418_, v___x_1446_, v___x_1445_);
v_fst_1448_ = lean_ctor_get(v___x_1447_, 0);
v_snd_1449_ = lean_ctor_get(v___x_1447_, 1);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1447_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1451_ = v___x_1447_;
v_isShared_1452_ = v_isSharedCheck_1469_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_snd_1449_);
lean_inc(v_fst_1448_);
lean_dec(v___x_1447_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1469_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
uint8_t v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1453_ = 2;
v___x_1454_ = lean_box(v___x_1453_);
lean_inc(v_a_1434_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 1, v_a_1434_);
lean_ctor_set(v___x_1451_, 0, v___x_1454_);
v___x_1456_ = v___x_1451_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1454_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_a_1434_);
v___x_1456_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1457_ = lean_array_push(v_fst_1448_, v___x_1456_);
v___x_1458_ = lean_unsigned_to_nat(1u);
v___x_1459_ = lean_nat_add(v_snd_1440_, v___x_1458_);
lean_dec(v_snd_1440_);
v___x_1460_ = lean_nat_add(v_snd_1449_, v___x_1458_);
lean_dec(v_snd_1449_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 1, v___x_1460_);
lean_ctor_set(v___x_1427_, 0, v___x_1459_);
v___x_1462_ = v___x_1427_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1467_, 1, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1463_; size_t v___x_1464_; size_t v___x_1465_; 
v___x_1463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1457_);
lean_ctor_set(v___x_1463_, 1, v___x_1462_);
v___x_1464_ = ((size_t)1ULL);
v___x_1465_ = lean_usize_add(v_i_1421_, v___x_1464_);
v_i_1421_ = v___x_1465_;
v_b_1422_ = v___x_1463_;
goto _start;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__14___boxed(lean_object* v_original_1475_, lean_object* v___x_1476_, lean_object* v_edited_1477_, lean_object* v___x_1478_, lean_object* v_as_1479_, lean_object* v_sz_1480_, lean_object* v_i_1481_, lean_object* v_b_1482_){
_start:
{
size_t v_sz_boxed_1483_; size_t v_i_boxed_1484_; lean_object* v_res_1485_; 
v_sz_boxed_1483_ = lean_unbox_usize(v_sz_1480_);
lean_dec(v_sz_1480_);
v_i_boxed_1484_ = lean_unbox_usize(v_i_1481_);
lean_dec(v_i_1481_);
v_res_1485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__14(v_original_1475_, v___x_1476_, v_edited_1477_, v___x_1478_, v_as_1479_, v_sz_boxed_1483_, v_i_boxed_1484_, v_b_1482_);
lean_dec_ref(v_as_1479_);
lean_dec(v___x_1478_);
lean_dec_ref(v_edited_1477_);
lean_dec(v___x_1476_);
lean_dec_ref(v_original_1475_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(lean_object* v_edited_1486_, lean_object* v___x_1487_, lean_object* v_original_1488_, lean_object* v___x_1489_, lean_object* v_as_1490_, size_t v_sz_1491_, size_t v_i_1492_, lean_object* v_b_1493_){
_start:
{
uint8_t v___x_1494_; 
v___x_1494_ = lean_usize_dec_lt(v_i_1492_, v_sz_1491_);
if (v___x_1494_ == 0)
{
return v_b_1493_;
}
else
{
lean_object* v_snd_1495_; lean_object* v_fst_1496_; lean_object* v___x_1498_; uint8_t v_isShared_1499_; uint8_t v_isSharedCheck_1545_; 
v_snd_1495_ = lean_ctor_get(v_b_1493_, 1);
v_fst_1496_ = lean_ctor_get(v_b_1493_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v_b_1493_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1498_ = v_b_1493_;
v_isShared_1499_ = v_isSharedCheck_1545_;
goto v_resetjp_1497_;
}
else
{
lean_inc(v_snd_1495_);
lean_inc(v_fst_1496_);
lean_dec(v_b_1493_);
v___x_1498_ = lean_box(0);
v_isShared_1499_ = v_isSharedCheck_1545_;
goto v_resetjp_1497_;
}
v_resetjp_1497_:
{
lean_object* v_fst_1500_; lean_object* v_snd_1501_; lean_object* v___x_1503_; uint8_t v_isShared_1504_; uint8_t v_isSharedCheck_1544_; 
v_fst_1500_ = lean_ctor_get(v_snd_1495_, 0);
v_snd_1501_ = lean_ctor_get(v_snd_1495_, 1);
v_isSharedCheck_1544_ = !lean_is_exclusive(v_snd_1495_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1503_ = v_snd_1495_;
v_isShared_1504_ = v_isSharedCheck_1544_;
goto v_resetjp_1502_;
}
else
{
lean_inc(v_snd_1501_);
lean_inc(v_fst_1500_);
lean_dec(v_snd_1495_);
v___x_1503_ = lean_box(0);
v_isShared_1504_ = v_isSharedCheck_1544_;
goto v_resetjp_1502_;
}
v_resetjp_1502_:
{
lean_object* v_a_1505_; lean_object* v___x_1507_; 
v_a_1505_ = lean_array_uget_borrowed(v_as_1490_, v_i_1492_);
if (v_isShared_1504_ == 0)
{
lean_ctor_set(v___x_1503_, 1, v_fst_1500_);
lean_ctor_set(v___x_1503_, 0, v_fst_1496_);
v___x_1507_ = v___x_1503_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_fst_1496_);
lean_ctor_set(v_reuseFailAlloc_1543_, 1, v_fst_1500_);
v___x_1507_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
uint32_t v___x_1508_; lean_object* v___x_1509_; lean_object* v_fst_1510_; lean_object* v_snd_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1542_; 
v___x_1508_ = lean_unbox_uint32(v_a_1505_);
v___x_1509_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v_original_1488_, v___x_1489_, v___x_1508_, v___x_1507_);
v_fst_1510_ = lean_ctor_get(v___x_1509_, 0);
v_snd_1511_ = lean_ctor_get(v___x_1509_, 1);
v_isSharedCheck_1542_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1513_ = v___x_1509_;
v_isShared_1514_ = v_isSharedCheck_1542_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_snd_1511_);
lean_inc(v_fst_1510_);
lean_dec(v___x_1509_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1542_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
lean_ctor_set(v___x_1513_, 1, v_snd_1501_);
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_fst_1510_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v_snd_1501_);
v___x_1516_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
uint32_t v___x_1517_; lean_object* v___x_1518_; lean_object* v_fst_1519_; lean_object* v_snd_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1540_; 
v___x_1517_ = lean_unbox_uint32(v_a_1505_);
v___x_1518_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg(v_edited_1486_, v___x_1487_, v___x_1517_, v___x_1516_);
v_fst_1519_ = lean_ctor_get(v___x_1518_, 0);
v_snd_1520_ = lean_ctor_get(v___x_1518_, 1);
v_isSharedCheck_1540_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1522_ = v___x_1518_;
v_isShared_1523_ = v_isSharedCheck_1540_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_snd_1520_);
lean_inc(v_fst_1519_);
lean_dec(v___x_1518_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1540_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
uint8_t v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1527_; 
v___x_1524_ = 2;
v___x_1525_ = lean_box(v___x_1524_);
lean_inc(v_a_1505_);
if (v_isShared_1523_ == 0)
{
lean_ctor_set(v___x_1522_, 1, v_a_1505_);
lean_ctor_set(v___x_1522_, 0, v___x_1525_);
v___x_1527_ = v___x_1522_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1539_, 1, v_a_1505_);
v___x_1527_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1533_; 
v___x_1528_ = lean_array_push(v_fst_1519_, v___x_1527_);
v___x_1529_ = lean_unsigned_to_nat(1u);
v___x_1530_ = lean_nat_add(v_snd_1511_, v___x_1529_);
lean_dec(v_snd_1511_);
v___x_1531_ = lean_nat_add(v_snd_1520_, v___x_1529_);
lean_dec(v_snd_1520_);
if (v_isShared_1499_ == 0)
{
lean_ctor_set(v___x_1498_, 1, v___x_1531_);
lean_ctor_set(v___x_1498_, 0, v___x_1530_);
v___x_1533_ = v___x_1498_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1530_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v___x_1531_);
v___x_1533_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1534_; size_t v___x_1535_; size_t v___x_1536_; lean_object* v___x_1537_; 
v___x_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1528_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
v___x_1535_ = ((size_t)1ULL);
v___x_1536_ = lean_usize_add(v_i_1492_, v___x_1535_);
v___x_1537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__14(v_original_1488_, v___x_1489_, v_edited_1486_, v___x_1487_, v_as_1490_, v_sz_1491_, v___x_1536_, v___x_1534_);
return v___x_1537_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5___boxed(lean_object* v_edited_1546_, lean_object* v___x_1547_, lean_object* v_original_1548_, lean_object* v___x_1549_, lean_object* v_as_1550_, lean_object* v_sz_1551_, lean_object* v_i_1552_, lean_object* v_b_1553_){
_start:
{
size_t v_sz_boxed_1554_; size_t v_i_boxed_1555_; lean_object* v_res_1556_; 
v_sz_boxed_1554_ = lean_unbox_usize(v_sz_1551_);
lean_dec(v_sz_1551_);
v_i_boxed_1555_ = lean_unbox_usize(v_i_1552_);
lean_dec(v_i_1552_);
v_res_1556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v_edited_1546_, v___x_1547_, v_original_1548_, v___x_1549_, v_as_1550_, v_sz_boxed_1554_, v_i_boxed_1555_, v_b_1553_);
lean_dec_ref(v_as_1550_);
lean_dec(v___x_1549_);
lean_dec_ref(v_original_1548_);
lean_dec(v___x_1547_);
lean_dec_ref(v_edited_1546_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(lean_object* v_original_1564_, lean_object* v_edited_1565_){
_start:
{
lean_object* v_i_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; 
v_i_1566_ = lean_unsigned_to_nat(0u);
v___x_1567_ = lean_array_get_size(v_original_1564_);
v___x_1568_ = lean_nat_dec_lt(v_i_1566_, v___x_1567_);
if (v___x_1568_ == 0)
{
size_t v_sz_1569_; size_t v___x_1570_; lean_object* v___x_1571_; 
lean_dec_ref(v_original_1564_);
v_sz_1569_ = lean_array_size(v_edited_1565_);
v___x_1570_ = ((size_t)0ULL);
v___x_1571_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(v_sz_1569_, v___x_1570_, v_edited_1565_);
return v___x_1571_;
}
else
{
lean_object* v___x_1572_; uint8_t v___x_1573_; 
v___x_1572_ = lean_array_get_size(v_edited_1565_);
v___x_1573_ = lean_nat_dec_lt(v_i_1566_, v___x_1572_);
if (v___x_1573_ == 0)
{
size_t v_sz_1574_; size_t v___x_1575_; lean_object* v___x_1576_; 
lean_dec_ref(v_edited_1565_);
v_sz_1574_ = lean_array_size(v_original_1564_);
v___x_1575_ = ((size_t)0ULL);
v___x_1576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(v_sz_1574_, v___x_1575_, v_original_1564_);
return v___x_1576_;
}
else
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v_ds_1579_; lean_object* v___x_1580_; size_t v_sz_1581_; size_t v___x_1582_; lean_object* v___x_1583_; lean_object* v_snd_1584_; lean_object* v_fst_1585_; lean_object* v_fst_1586_; lean_object* v_snd_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1606_; 
lean_inc_ref(v_original_1564_);
v___x_1577_ = l_Array_toSubarray___redArg(v_original_1564_, v_i_1566_, v___x_1567_);
lean_inc_ref(v_edited_1565_);
v___x_1578_ = l_Array_toSubarray___redArg(v_edited_1565_, v_i_1566_, v___x_1572_);
v_ds_1579_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v___x_1577_, v___x_1578_);
v___x_1580_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__2));
v_sz_1581_ = lean_array_size(v_ds_1579_);
v___x_1582_ = ((size_t)0ULL);
v___x_1583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v_edited_1565_, v___x_1572_, v_original_1564_, v___x_1567_, v_ds_1579_, v_sz_1581_, v___x_1582_, v___x_1580_);
lean_dec_ref(v_ds_1579_);
v_snd_1584_ = lean_ctor_get(v___x_1583_, 1);
lean_inc(v_snd_1584_);
v_fst_1585_ = lean_ctor_get(v___x_1583_, 0);
lean_inc(v_fst_1585_);
lean_dec_ref(v___x_1583_);
v_fst_1586_ = lean_ctor_get(v_snd_1584_, 0);
v_snd_1587_ = lean_ctor_get(v_snd_1584_, 1);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_snd_1584_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1589_ = v_snd_1584_;
v_isShared_1590_ = v_isSharedCheck_1606_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_snd_1587_);
lean_inc(v_fst_1586_);
lean_dec(v_snd_1584_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1606_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 1, v_fst_1586_);
lean_ctor_set(v___x_1589_, 0, v_fst_1585_);
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_fst_1585_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_fst_1586_);
v___x_1592_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
lean_object* v___x_1593_; lean_object* v_fst_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1603_; 
v___x_1593_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_1567_, v_original_1564_, v___x_1592_);
lean_dec_ref(v_original_1564_);
v_fst_1594_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1603_ == 0)
{
lean_object* v_unused_1604_; 
v_unused_1604_ = lean_ctor_get(v___x_1593_, 1);
lean_dec(v_unused_1604_);
v___x_1596_ = v___x_1593_;
v_isShared_1597_ = v_isSharedCheck_1603_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_fst_1594_);
lean_dec(v___x_1593_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1603_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 1, v_snd_1587_);
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_fst_1594_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_snd_1587_);
v___x_1599_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v___x_1600_; lean_object* v_fst_1601_; 
v___x_1600_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1572_, v_edited_1565_, v___x_1599_);
lean_dec_ref(v_edited_1565_);
v_fst_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_fst_1601_);
lean_dec_ref(v___x_1600_);
return v_fst_1601_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(lean_object* v_s_1607_, lean_object* v_a_1608_, uint8_t v_b_1609_){
_start:
{
lean_object* v_str_1610_; lean_object* v_startInclusive_1611_; lean_object* v_endExclusive_1612_; lean_object* v___x_1613_; uint8_t v___x_1614_; 
v_str_1610_ = lean_ctor_get(v_s_1607_, 0);
v_startInclusive_1611_ = lean_ctor_get(v_s_1607_, 1);
v_endExclusive_1612_ = lean_ctor_get(v_s_1607_, 2);
v___x_1613_ = lean_nat_sub(v_endExclusive_1612_, v_startInclusive_1611_);
v___x_1614_ = lean_nat_dec_eq(v_a_1608_, v___x_1613_);
lean_dec(v___x_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; uint32_t v___x_1616_; uint32_t v___x_1617_; uint8_t v___x_1618_; 
v___x_1615_ = lean_nat_add(v_startInclusive_1611_, v_a_1608_);
lean_dec(v_a_1608_);
v___x_1616_ = lean_string_utf8_get_fast(v_str_1610_, v___x_1615_);
v___x_1617_ = 10;
v___x_1618_ = lean_uint32_dec_eq(v___x_1616_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = lean_string_utf8_next_fast(v_str_1610_, v___x_1615_);
lean_dec(v___x_1615_);
v___x_1620_ = lean_nat_sub(v___x_1619_, v_startInclusive_1611_);
v_a_1608_ = v___x_1620_;
v_b_1609_ = v___x_1618_;
goto _start;
}
else
{
lean_dec(v___x_1615_);
return v___x_1618_;
}
}
else
{
lean_dec(v_a_1608_);
return v_b_1609_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg___boxed(lean_object* v_s_1622_, lean_object* v_a_1623_, lean_object* v_b_1624_){
_start:
{
uint8_t v_b_boxed_1625_; uint8_t v_res_1626_; lean_object* v_r_1627_; 
v_b_boxed_1625_ = lean_unbox(v_b_1624_);
v_res_1626_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1622_, v_a_1623_, v_b_boxed_1625_);
lean_dec_ref(v_s_1622_);
v_r_1627_ = lean_box(v_res_1626_);
return v_r_1627_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(lean_object* v_s_1628_){
_start:
{
lean_object* v_searcher_1629_; uint8_t v___x_1630_; uint8_t v___x_1631_; 
v_searcher_1629_ = lean_unsigned_to_nat(0u);
v___x_1630_ = 0;
v___x_1631_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1628_, v_searcher_1629_, v___x_1630_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0___boxed(lean_object* v_s_1632_){
_start:
{
uint8_t v_res_1633_; lean_object* v_r_1634_; 
v_res_1633_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v_s_1632_);
lean_dec_ref(v_s_1632_);
v_r_1634_ = lean_box(v_res_1633_);
return v_r_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(lean_object* v_oldWs_1635_, lean_object* v_newWs_1636_){
_start:
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; 
v___x_1637_ = lean_unsigned_to_nat(0u);
v___x_1638_ = lean_string_utf8_byte_size(v_oldWs_1635_);
lean_inc_ref(v_oldWs_1635_);
v___x_1639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1639_, 0, v_oldWs_1635_);
lean_ctor_set(v___x_1639_, 1, v___x_1637_);
lean_ctor_set(v___x_1639_, 2, v___x_1638_);
v___x_1640_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_1639_);
lean_dec_ref_known(v___x_1639_, 3);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1641_ = lean_string_data(v_oldWs_1635_);
v___x_1642_ = lean_array_mk(v___x_1641_);
v___x_1643_ = lean_string_data(v_newWs_1636_);
v___x_1644_ = lean_array_mk(v___x_1643_);
v___x_1645_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_1642_, v___x_1644_);
v___x_1646_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_1645_);
lean_dec_ref(v___x_1645_);
return v___x_1646_;
}
else
{
uint8_t v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
lean_dec_ref(v_oldWs_1635_);
v___x_1647_ = 2;
v___x_1648_ = lean_box(v___x_1647_);
v___x_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1649_, 0, v___x_1648_);
lean_ctor_set(v___x_1649_, 1, v_newWs_1636_);
v___x_1650_ = lean_unsigned_to_nat(1u);
v___x_1651_ = lean_mk_empty_array_with_capacity(v___x_1650_);
v___x_1652_ = lean_array_push(v___x_1651_, v___x_1649_);
return v___x_1652_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(lean_object* v_s_1653_, lean_object* v_inst_1654_, lean_object* v_R_1655_, lean_object* v_a_1656_, uint8_t v_b_1657_, lean_object* v_c_1658_){
_start:
{
uint8_t v___x_1659_; 
v___x_1659_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1653_, v_a_1656_, v_b_1657_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___boxed(lean_object* v_s_1660_, lean_object* v_inst_1661_, lean_object* v_R_1662_, lean_object* v_a_1663_, lean_object* v_b_1664_, lean_object* v_c_1665_){
_start:
{
uint8_t v_b_boxed_1666_; uint8_t v_res_1667_; lean_object* v_r_1668_; 
v_b_boxed_1666_ = lean_unbox(v_b_1664_);
v_res_1667_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(v_s_1660_, v_inst_1661_, v_R_1662_, v_a_1663_, v_b_boxed_1666_, v_c_1665_);
lean_dec_ref(v_s_1660_);
v_r_1668_ = lean_box(v_res_1667_);
return v_r_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(lean_object* v_original_1669_, lean_object* v___x_1670_, uint32_t v_a_1671_, lean_object* v_inst_1672_, lean_object* v_a_1673_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v_original_1669_, v___x_1670_, v_a_1671_, v_a_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___boxed(lean_object* v_original_1675_, lean_object* v___x_1676_, lean_object* v_a_1677_, lean_object* v_inst_1678_, lean_object* v_a_1679_){
_start:
{
uint32_t v_a_boxed_1680_; lean_object* v_res_1681_; 
v_a_boxed_1680_ = lean_unbox_uint32(v_a_1677_);
lean_dec(v_a_1677_);
v_res_1681_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(v_original_1675_, v___x_1676_, v_a_boxed_1680_, v_inst_1678_, v_a_1679_);
lean_dec(v___x_1676_);
lean_dec_ref(v_original_1675_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(lean_object* v_edited_1682_, lean_object* v___x_1683_, uint32_t v_a_1684_, lean_object* v_inst_1685_, lean_object* v_a_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg(v_edited_1682_, v___x_1683_, v_a_1684_, v_a_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed(lean_object* v_edited_1688_, lean_object* v___x_1689_, lean_object* v_a_1690_, lean_object* v_inst_1691_, lean_object* v_a_1692_){
_start:
{
uint32_t v_a_boxed_1693_; lean_object* v_res_1694_; 
v_a_boxed_1693_ = lean_unbox_uint32(v_a_1690_);
lean_dec(v_a_1690_);
v_res_1694_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v_edited_1688_, v___x_1689_, v_a_boxed_1693_, v_inst_1691_, v_a_1692_);
lean_dec(v___x_1689_);
lean_dec_ref(v_edited_1688_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(lean_object* v___x_1695_, lean_object* v_original_1696_, lean_object* v_inst_1697_, lean_object* v_a_1698_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_1695_, v_original_1696_, v_a_1698_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___boxed(lean_object* v___x_1700_, lean_object* v_original_1701_, lean_object* v_inst_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(v___x_1700_, v_original_1701_, v_inst_1702_, v_a_1703_);
lean_dec_ref(v_original_1701_);
lean_dec(v___x_1700_);
return v_res_1704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(lean_object* v___x_1705_, lean_object* v_edited_1706_, lean_object* v_inst_1707_, lean_object* v_a_1708_){
_start:
{
lean_object* v___x_1709_; 
v___x_1709_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1705_, v_edited_1706_, v_a_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___boxed(lean_object* v___x_1710_, lean_object* v_edited_1711_, lean_object* v_inst_1712_, lean_object* v_a_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(v___x_1710_, v_edited_1711_, v_inst_1712_, v_a_1713_);
lean_dec_ref(v_edited_1711_);
lean_dec(v___x_1710_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(lean_object* v_as_1715_, lean_object* v_as_x27_1716_, lean_object* v_b_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6___redArg(v_as_x27_1716_, v_b_1717_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6___boxed(lean_object* v_as_1720_, lean_object* v_as_x27_1721_, lean_object* v_b_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(v_as_1720_, v_as_x27_1721_, v_b_1722_, v_a_1723_);
lean_dec(v_as_x27_1721_);
lean_dec(v_as_1720_);
return v_res_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7(lean_object* v_lsize_1725_, lean_object* v_rsize_1726_, lean_object* v_histogram_1727_, lean_object* v_index_1728_, uint32_t v_val_1729_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7___redArg(v_histogram_1727_, v_index_1728_, v_val_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7___boxed(lean_object* v_lsize_1731_, lean_object* v_rsize_1732_, lean_object* v_histogram_1733_, lean_object* v_index_1734_, lean_object* v_val_1735_){
_start:
{
uint32_t v_val_boxed_1736_; lean_object* v_res_1737_; 
v_val_boxed_1736_ = lean_unbox_uint32(v_val_1735_);
lean_dec(v_val_1735_);
v_res_1737_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7(v_lsize_1731_, v_rsize_1732_, v_histogram_1733_, v_index_1734_, v_val_boxed_1736_);
lean_dec(v_rsize_1732_);
lean_dec(v_lsize_1731_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8(lean_object* v_upperBound_1738_, lean_object* v___x_1739_, lean_object* v_fst_1740_, lean_object* v___x_1741_, lean_object* v_inst_1742_, lean_object* v_R_1743_, lean_object* v_a_1744_, lean_object* v_b_1745_, lean_object* v_c_1746_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(v_upperBound_1738_, v___x_1739_, v_fst_1740_, v___x_1741_, v_a_1744_, v_b_1745_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___boxed(lean_object* v_upperBound_1748_, lean_object* v___x_1749_, lean_object* v_fst_1750_, lean_object* v___x_1751_, lean_object* v_inst_1752_, lean_object* v_R_1753_, lean_object* v_a_1754_, lean_object* v_b_1755_, lean_object* v_c_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8(v_upperBound_1748_, v___x_1749_, v_fst_1750_, v___x_1751_, v_inst_1752_, v_R_1753_, v_a_1754_, v_b_1755_, v_c_1756_);
lean_dec(v___x_1751_);
lean_dec_ref(v_fst_1750_);
lean_dec(v___x_1749_);
lean_dec(v_upperBound_1748_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9(lean_object* v_lsize_1758_, lean_object* v_rsize_1759_, lean_object* v_histogram_1760_, lean_object* v_index_1761_, uint32_t v_val_1762_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(v_histogram_1760_, v_index_1761_, v_val_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___boxed(lean_object* v_lsize_1764_, lean_object* v_rsize_1765_, lean_object* v_histogram_1766_, lean_object* v_index_1767_, lean_object* v_val_1768_){
_start:
{
uint32_t v_val_boxed_1769_; lean_object* v_res_1770_; 
v_val_boxed_1769_ = lean_unbox_uint32(v_val_1768_);
lean_dec(v_val_1768_);
v_res_1770_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9(v_lsize_1764_, v_rsize_1765_, v_histogram_1766_, v_index_1767_, v_val_boxed_1769_);
lean_dec(v_rsize_1765_);
lean_dec(v_lsize_1764_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10(lean_object* v_upperBound_1771_, lean_object* v_fst_1772_, lean_object* v___x_1773_, lean_object* v_fst_1774_, lean_object* v_inst_1775_, lean_object* v_R_1776_, lean_object* v_a_1777_, lean_object* v_b_1778_, lean_object* v_c_1779_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(v_upperBound_1771_, v_fst_1772_, v___x_1773_, v_fst_1774_, v_a_1777_, v_b_1778_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___boxed(lean_object* v_upperBound_1781_, lean_object* v_fst_1782_, lean_object* v___x_1783_, lean_object* v_fst_1784_, lean_object* v_inst_1785_, lean_object* v_R_1786_, lean_object* v_a_1787_, lean_object* v_b_1788_, lean_object* v_c_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10(v_upperBound_1781_, v_fst_1782_, v___x_1783_, v_fst_1784_, v_inst_1785_, v_R_1786_, v_a_1787_, v_b_1788_, v_c_1789_);
lean_dec_ref(v_fst_1784_);
lean_dec(v___x_1783_);
lean_dec_ref(v_fst_1782_);
lean_dec(v_upperBound_1781_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10(lean_object* v_00_u03b2_1791_, lean_object* v_m_1792_, uint32_t v_a_1793_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10___redArg(v_m_1792_, v_a_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10___boxed(lean_object* v_00_u03b2_1795_, lean_object* v_m_1796_, lean_object* v_a_1797_){
_start:
{
uint32_t v_a_boxed_1798_; lean_object* v_res_1799_; 
v_a_boxed_1798_ = lean_unbox_uint32(v_a_1797_);
lean_dec(v_a_1797_);
v_res_1799_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10(v_00_u03b2_1795_, v_m_1796_, v_a_boxed_1798_);
lean_dec_ref(v_m_1796_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11(lean_object* v_00_u03b2_1800_, lean_object* v_m_1801_, uint32_t v_query_1802_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11___redArg(v_m_1801_, v_query_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11___boxed(lean_object* v_00_u03b2_1804_, lean_object* v_m_1805_, lean_object* v_query_1806_){
_start:
{
uint32_t v_query_boxed_1807_; lean_object* v_res_1808_; 
v_query_boxed_1807_ = lean_unbox_uint32(v_query_1806_);
lean_dec(v_query_1806_);
v_res_1808_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11(v_00_u03b2_1804_, v_m_1805_, v_query_boxed_1807_);
lean_dec_ref(v_m_1805_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12(lean_object* v_00_u03b2_1809_, lean_object* v_m_1810_){
_start:
{
lean_object* v___x_1811_; 
v___x_1811_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12___redArg(v_m_1810_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12___boxed(lean_object* v_00_u03b2_1812_, lean_object* v_m_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12(v_00_u03b2_1812_, v_m_1813_);
lean_dec_ref(v_m_1813_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14(lean_object* v_inst_1815_, lean_object* v_R_1816_, lean_object* v_a_1817_, lean_object* v_b_1818_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(v_a_1817_, v_b_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10_spec__19(lean_object* v_00_u03b2_1820_, lean_object* v_m_1821_, uint32_t v_query_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10_spec__19___redArg(v_m_1821_, v_query_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10_spec__19___boxed(lean_object* v_00_u03b2_1824_, lean_object* v_m_1825_, lean_object* v_query_1826_){
_start:
{
uint32_t v_query_boxed_1827_; lean_object* v_res_1828_; 
v_query_boxed_1827_ = lean_unbox_uint32(v_query_1826_);
lean_dec(v_query_1826_);
v_res_1828_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__10_spec__19(v_00_u03b2_1824_, v_m_1825_, v_query_boxed_1827_);
lean_dec_ref(v_m_1825_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11_spec__21(lean_object* v_00_u03b2_1829_, lean_object* v_m_1830_, uint32_t v_query_1831_, lean_object* v_x_1832_, lean_object* v_x_1833_, lean_object* v_x_1834_, lean_object* v_x_1835_){
_start:
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11_spec__21___redArg(v_m_1830_, v_query_1831_, v_x_1832_, v_x_1833_, v_x_1834_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11_spec__21___boxed(lean_object* v_00_u03b2_1837_, lean_object* v_m_1838_, lean_object* v_query_1839_, lean_object* v_x_1840_, lean_object* v_x_1841_, lean_object* v_x_1842_, lean_object* v_x_1843_){
_start:
{
uint32_t v_query_boxed_1844_; lean_object* v_res_1845_; 
v_query_boxed_1844_ = lean_unbox_uint32(v_query_1839_);
lean_dec(v_query_1839_);
v_res_1845_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__11_spec__21(v_00_u03b2_1837_, v_m_1838_, v_query_boxed_1844_, v_x_1840_, v_x_1841_, v_x_1842_, v_x_1843_);
lean_dec_ref(v_m_1838_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23(lean_object* v_00_u03b2_1846_, lean_object* v_init_1847_, lean_object* v_b_1848_){
_start:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23___redArg(v_init_1847_, v_b_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23___boxed(lean_object* v_00_u03b2_1850_, lean_object* v_init_1851_, lean_object* v_b_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23(v_00_u03b2_1850_, v_init_1851_, v_b_1852_);
lean_dec_ref(v_b_1852_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23_spec__28(lean_object* v_00_u03b2_1854_, lean_object* v_b_1855_, lean_object* v_acc_1856_, lean_object* v_i_1857_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23_spec__28___redArg(v_b_1855_, v_acc_1856_, v_i_1857_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23_spec__28___boxed(lean_object* v_00_u03b2_1859_, lean_object* v_b_1860_, lean_object* v_acc_1861_, lean_object* v_i_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7_spec__12_spec__23_spec__28(v_00_u03b2_1859_, v_b_1860_, v_acc_1861_, v_i_1862_);
lean_dec_ref(v_b_1860_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(lean_object* v_s_1864_, lean_object* v_stopPos_1865_, lean_object* v_i_1866_){
_start:
{
uint8_t v___y_1871_; uint8_t v___x_1872_; 
v___x_1872_ = lean_nat_dec_lt(v_i_1866_, v_stopPos_1865_);
if (v___x_1872_ == 0)
{
return v_i_1866_;
}
else
{
uint32_t v___x_1873_; uint8_t v___y_1875_; uint32_t v___x_1880_; uint8_t v___x_1881_; 
v___x_1873_ = lean_string_utf8_get(v_s_1864_, v_i_1866_);
v___x_1880_ = 32;
v___x_1881_ = lean_uint32_dec_eq(v___x_1873_, v___x_1880_);
if (v___x_1881_ == 0)
{
uint32_t v___x_1882_; uint8_t v___x_1883_; 
v___x_1882_ = 9;
v___x_1883_ = lean_uint32_dec_eq(v___x_1873_, v___x_1882_);
v___y_1875_ = v___x_1883_;
goto v___jp_1874_;
}
else
{
v___y_1875_ = v___x_1881_;
goto v___jp_1874_;
}
v___jp_1874_:
{
if (v___y_1875_ == 0)
{
uint32_t v___x_1876_; uint8_t v___x_1877_; 
v___x_1876_ = 13;
v___x_1877_ = lean_uint32_dec_eq(v___x_1873_, v___x_1876_);
if (v___x_1877_ == 0)
{
uint32_t v___x_1878_; uint8_t v___x_1879_; 
v___x_1878_ = 10;
v___x_1879_ = lean_uint32_dec_eq(v___x_1873_, v___x_1878_);
v___y_1871_ = v___x_1879_;
goto v___jp_1870_;
}
else
{
v___y_1871_ = v___x_1877_;
goto v___jp_1870_;
}
}
else
{
goto v___jp_1867_;
}
}
}
v___jp_1867_:
{
lean_object* v___x_1868_; 
v___x_1868_ = lean_string_utf8_next(v_s_1864_, v_i_1866_);
lean_dec(v_i_1866_);
v_i_1866_ = v___x_1868_;
goto _start;
}
v___jp_1870_:
{
if (v___y_1871_ == 0)
{
return v_i_1866_;
}
else
{
goto v___jp_1867_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0___boxed(lean_object* v_s_1884_, lean_object* v_stopPos_1885_, lean_object* v_i_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1884_, v_stopPos_1885_, v_i_1886_);
lean_dec(v_stopPos_1885_);
lean_dec_ref(v_s_1884_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(lean_object* v_s_1888_, lean_object* v_b_1889_, lean_object* v_i_1890_, lean_object* v_r_1891_, lean_object* v_ws_1892_){
_start:
{
uint8_t v___y_1902_; uint8_t v___x_1905_; 
v___x_1905_ = lean_string_utf8_at_end(v_s_1888_, v_i_1890_);
if (v___x_1905_ == 0)
{
uint32_t v___x_1906_; uint8_t v___y_1908_; uint32_t v___x_1913_; uint8_t v___x_1914_; 
v___x_1906_ = lean_string_utf8_get(v_s_1888_, v_i_1890_);
v___x_1913_ = 32;
v___x_1914_ = lean_uint32_dec_eq(v___x_1906_, v___x_1913_);
if (v___x_1914_ == 0)
{
uint32_t v___x_1915_; uint8_t v___x_1916_; 
v___x_1915_ = 9;
v___x_1916_ = lean_uint32_dec_eq(v___x_1906_, v___x_1915_);
v___y_1908_ = v___x_1916_;
goto v___jp_1907_;
}
else
{
v___y_1908_ = v___x_1914_;
goto v___jp_1907_;
}
v___jp_1907_:
{
if (v___y_1908_ == 0)
{
uint32_t v___x_1909_; uint8_t v___x_1910_; 
v___x_1909_ = 13;
v___x_1910_ = lean_uint32_dec_eq(v___x_1906_, v___x_1909_);
if (v___x_1910_ == 0)
{
uint32_t v___x_1911_; uint8_t v___x_1912_; 
v___x_1911_ = 10;
v___x_1912_ = lean_uint32_dec_eq(v___x_1906_, v___x_1911_);
v___y_1902_ = v___x_1912_;
goto v___jp_1901_;
}
else
{
v___y_1902_ = v___x_1910_;
goto v___jp_1901_;
}
}
else
{
goto v___jp_1893_;
}
}
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = lean_string_utf8_extract(v_s_1888_, v_b_1889_, v_i_1890_);
lean_dec(v_i_1890_);
lean_dec(v_b_1889_);
v___x_1918_ = lean_array_push(v_r_1891_, v___x_1917_);
v___x_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
lean_ctor_set(v___x_1919_, 1, v_ws_1892_);
return v___x_1919_;
}
v___jp_1893_:
{
lean_object* v___x_1894_; lean_object* v_e_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1894_ = lean_string_utf8_byte_size(v_s_1888_);
lean_inc(v_i_1890_);
v_e_1895_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1888_, v___x_1894_, v_i_1890_);
v___x_1896_ = lean_string_utf8_extract(v_s_1888_, v_b_1889_, v_i_1890_);
lean_dec(v_b_1889_);
v___x_1897_ = lean_array_push(v_r_1891_, v___x_1896_);
v___x_1898_ = lean_string_utf8_extract(v_s_1888_, v_i_1890_, v_e_1895_);
lean_dec(v_i_1890_);
v___x_1899_ = lean_array_push(v_ws_1892_, v___x_1898_);
lean_inc(v_e_1895_);
v_b_1889_ = v_e_1895_;
v_i_1890_ = v_e_1895_;
v_r_1891_ = v___x_1897_;
v_ws_1892_ = v___x_1899_;
goto _start;
}
v___jp_1901_:
{
if (v___y_1902_ == 0)
{
lean_object* v___x_1903_; 
v___x_1903_ = lean_string_utf8_next(v_s_1888_, v_i_1890_);
lean_dec(v_i_1890_);
v_i_1890_ = v___x_1903_;
goto _start;
}
else
{
goto v___jp_1893_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux___boxed(lean_object* v_s_1920_, lean_object* v_b_1921_, lean_object* v_i_1922_, lean_object* v_r_1923_, lean_object* v_ws_1924_){
_start:
{
lean_object* v_res_1925_; 
v_res_1925_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1920_, v_b_1921_, v_i_1922_, v_r_1923_, v_ws_1924_);
lean_dec_ref(v_s_1920_);
return v_res_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(lean_object* v_s_1928_){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1929_ = lean_unsigned_to_nat(0u);
v___x_1930_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_1931_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1928_, v___x_1929_, v___x_1929_, v___x_1930_, v___x_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___boxed(lean_object* v_s_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_1932_);
lean_dec_ref(v_s_1932_);
return v_res_1933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(size_t v_sz_1934_, size_t v_i_1935_, lean_object* v_bs_1936_){
_start:
{
uint8_t v___x_1937_; 
v___x_1937_ = lean_usize_dec_lt(v_i_1935_, v_sz_1934_);
if (v___x_1937_ == 0)
{
return v_bs_1936_;
}
else
{
lean_object* v_v_1938_; lean_object* v___x_1939_; lean_object* v_bs_x27_1940_; uint8_t v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; size_t v___x_1944_; size_t v___x_1945_; lean_object* v___x_1946_; 
v_v_1938_ = lean_array_uget(v_bs_1936_, v_i_1935_);
v___x_1939_ = lean_unsigned_to_nat(0u);
v_bs_x27_1940_ = lean_array_uset(v_bs_1936_, v_i_1935_, v___x_1939_);
v___x_1941_ = 0;
v___x_1942_ = lean_box(v___x_1941_);
v___x_1943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
lean_ctor_set(v___x_1943_, 1, v_v_1938_);
v___x_1944_ = ((size_t)1ULL);
v___x_1945_ = lean_usize_add(v_i_1935_, v___x_1944_);
v___x_1946_ = lean_array_uset(v_bs_x27_1940_, v_i_1935_, v___x_1943_);
v_i_1935_ = v___x_1945_;
v_bs_1936_ = v___x_1946_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8___boxed(lean_object* v_sz_1948_, lean_object* v_i_1949_, lean_object* v_bs_1950_){
_start:
{
size_t v_sz_boxed_1951_; size_t v_i_boxed_1952_; lean_object* v_res_1953_; 
v_sz_boxed_1951_ = lean_unbox_usize(v_sz_1948_);
lean_dec(v_sz_1948_);
v_i_boxed_1952_ = lean_unbox_usize(v_i_1949_);
lean_dec(v_i_1949_);
v_res_1953_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_boxed_1951_, v_i_boxed_1952_, v_bs_1950_);
return v_res_1953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(lean_object* v___x_1954_, lean_object* v_original_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v_fst_1957_; lean_object* v_snd_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1977_; 
v_fst_1957_ = lean_ctor_get(v_a_1956_, 0);
v_snd_1958_ = lean_ctor_get(v_a_1956_, 1);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_a_1956_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1960_ = v_a_1956_;
v_isShared_1961_ = v_isSharedCheck_1977_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_snd_1958_);
lean_inc(v_fst_1957_);
lean_dec(v_a_1956_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1977_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
uint8_t v___x_1962_; 
v___x_1962_ = lean_nat_dec_lt(v_snd_1958_, v___x_1954_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1964_; 
if (v_isShared_1961_ == 0)
{
v___x_1964_ = v___x_1960_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_fst_1957_);
lean_ctor_set(v_reuseFailAlloc_1965_, 1, v_snd_1958_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
else
{
uint8_t v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1966_ = 1;
v___x_1967_ = lean_array_fget_borrowed(v_original_1955_, v_snd_1958_);
v___x_1968_ = lean_box(v___x_1966_);
lean_inc(v___x_1967_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 1, v___x_1967_);
lean_ctor_set(v___x_1960_, 0, v___x_1968_);
v___x_1970_ = v___x_1960_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v___x_1968_);
lean_ctor_set(v_reuseFailAlloc_1976_, 1, v___x_1967_);
v___x_1970_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1971_ = lean_array_push(v_fst_1957_, v___x_1970_);
v___x_1972_ = lean_unsigned_to_nat(1u);
v___x_1973_ = lean_nat_add(v_snd_1958_, v___x_1972_);
lean_dec(v_snd_1958_);
v___x_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1971_);
lean_ctor_set(v___x_1974_, 1, v___x_1973_);
v_a_1956_ = v___x_1974_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg___boxed(lean_object* v___x_1978_, lean_object* v_original_1979_, lean_object* v_a_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_1978_, v_original_1979_, v_a_1980_);
lean_dec_ref(v_original_1979_);
lean_dec(v___x_1978_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(lean_object* v___x_1982_, lean_object* v_edited_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v_fst_1985_; lean_object* v_snd_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2005_; 
v_fst_1985_ = lean_ctor_get(v_a_1984_, 0);
v_snd_1986_ = lean_ctor_get(v_a_1984_, 1);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_a_1984_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1988_ = v_a_1984_;
v_isShared_1989_ = v_isSharedCheck_2005_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_snd_1986_);
lean_inc(v_fst_1985_);
lean_dec(v_a_1984_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2005_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
uint8_t v___x_1990_; 
v___x_1990_ = lean_nat_dec_lt(v_snd_1986_, v___x_1982_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1992_; 
if (v_isShared_1989_ == 0)
{
v___x_1992_ = v___x_1988_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_fst_1985_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_snd_1986_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
else
{
uint8_t v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1998_; 
v___x_1994_ = 0;
v___x_1995_ = lean_array_fget_borrowed(v_edited_1983_, v_snd_1986_);
v___x_1996_ = lean_box(v___x_1994_);
lean_inc(v___x_1995_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 1, v___x_1995_);
lean_ctor_set(v___x_1988_, 0, v___x_1996_);
v___x_1998_ = v___x_1988_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_1996_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v___x_1995_);
v___x_1998_ = v_reuseFailAlloc_2004_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_1999_ = lean_array_push(v_fst_1985_, v___x_1998_);
v___x_2000_ = lean_unsigned_to_nat(1u);
v___x_2001_ = lean_nat_add(v_snd_1986_, v___x_2000_);
lean_dec(v_snd_1986_);
v___x_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_1999_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
v_a_1984_ = v___x_2002_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg___boxed(lean_object* v___x_2006_, lean_object* v_edited_2007_, lean_object* v_a_2008_){
_start:
{
lean_object* v_res_2009_; 
v_res_2009_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2006_, v_edited_2007_, v_a_2008_);
lean_dec_ref(v_edited_2007_);
lean_dec(v___x_2006_);
return v_res_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(lean_object* v_original_2010_, lean_object* v___x_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_){
_start:
{
lean_object* v_fst_2014_; lean_object* v_snd_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2040_; 
v_fst_2014_ = lean_ctor_get(v_a_2013_, 0);
v_snd_2015_ = lean_ctor_get(v_a_2013_, 1);
v_isSharedCheck_2040_ = !lean_is_exclusive(v_a_2013_);
if (v_isSharedCheck_2040_ == 0)
{
v___x_2017_ = v_a_2013_;
v_isShared_2018_ = v_isSharedCheck_2040_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_snd_2015_);
lean_inc(v_fst_2014_);
lean_dec(v_a_2013_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2040_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v___x_2019_; uint8_t v___y_2021_; uint8_t v___x_2036_; 
v___x_2019_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2036_ = lean_nat_dec_lt(v_snd_2015_, v___x_2011_);
if (v___x_2036_ == 0)
{
v___y_2021_ = v___x_2036_;
goto v___jp_2020_;
}
else
{
lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2037_ = lean_array_get_borrowed(v___x_2019_, v_original_2010_, v_snd_2015_);
v___x_2038_ = lean_string_dec_eq(v___x_2037_, v_a_2012_);
if (v___x_2038_ == 0)
{
v___y_2021_ = v___x_2036_;
goto v___jp_2020_;
}
else
{
lean_object* v___x_2039_; 
lean_del_object(v___x_2017_);
v___x_2039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2039_, 0, v_fst_2014_);
lean_ctor_set(v___x_2039_, 1, v_snd_2015_);
return v___x_2039_;
}
}
v___jp_2020_:
{
if (v___y_2021_ == 0)
{
lean_object* v___x_2023_; 
if (v_isShared_2018_ == 0)
{
v___x_2023_ = v___x_2017_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_fst_2014_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v_snd_2015_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
else
{
uint8_t v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2029_; 
v___x_2025_ = 1;
v___x_2026_ = lean_array_get_borrowed(v___x_2019_, v_original_2010_, v_snd_2015_);
v___x_2027_ = lean_box(v___x_2025_);
lean_inc(v___x_2026_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 1, v___x_2026_);
lean_ctor_set(v___x_2017_, 0, v___x_2027_);
v___x_2029_ = v___x_2017_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2027_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___x_2026_);
v___x_2029_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2030_ = lean_array_push(v_fst_2014_, v___x_2029_);
v___x_2031_ = lean_unsigned_to_nat(1u);
v___x_2032_ = lean_nat_add(v_snd_2015_, v___x_2031_);
lean_dec(v_snd_2015_);
v___x_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2030_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v_a_2013_ = v___x_2033_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg___boxed(lean_object* v_original_2041_, lean_object* v___x_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v_original_2041_, v___x_2042_, v_a_2043_, v_a_2044_);
lean_dec_ref(v_a_2043_);
lean_dec(v___x_2042_);
lean_dec_ref(v_original_2041_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(lean_object* v_edited_2046_, lean_object* v___x_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_){
_start:
{
lean_object* v_fst_2050_; lean_object* v_snd_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2076_; 
v_fst_2050_ = lean_ctor_get(v_a_2049_, 0);
v_snd_2051_ = lean_ctor_get(v_a_2049_, 1);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_a_2049_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2053_ = v_a_2049_;
v_isShared_2054_ = v_isSharedCheck_2076_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_snd_2051_);
lean_inc(v_fst_2050_);
lean_dec(v_a_2049_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2076_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; uint8_t v___y_2057_; uint8_t v___x_2072_; 
v___x_2055_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2072_ = lean_nat_dec_lt(v_snd_2051_, v___x_2047_);
if (v___x_2072_ == 0)
{
v___y_2057_ = v___x_2072_;
goto v___jp_2056_;
}
else
{
lean_object* v___x_2073_; uint8_t v___x_2074_; 
v___x_2073_ = lean_array_get_borrowed(v___x_2055_, v_edited_2046_, v_snd_2051_);
v___x_2074_ = lean_string_dec_eq(v___x_2073_, v_a_2048_);
if (v___x_2074_ == 0)
{
v___y_2057_ = v___x_2072_;
goto v___jp_2056_;
}
else
{
lean_object* v___x_2075_; 
lean_del_object(v___x_2053_);
v___x_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2075_, 0, v_fst_2050_);
lean_ctor_set(v___x_2075_, 1, v_snd_2051_);
return v___x_2075_;
}
}
v___jp_2056_:
{
if (v___y_2057_ == 0)
{
lean_object* v___x_2059_; 
if (v_isShared_2054_ == 0)
{
v___x_2059_ = v___x_2053_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_fst_2050_);
lean_ctor_set(v_reuseFailAlloc_2060_, 1, v_snd_2051_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
else
{
uint8_t v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2061_ = 0;
v___x_2062_ = lean_array_get_borrowed(v___x_2055_, v_edited_2046_, v_snd_2051_);
v___x_2063_ = lean_box(v___x_2061_);
lean_inc(v___x_2062_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 1, v___x_2062_);
lean_ctor_set(v___x_2053_, 0, v___x_2063_);
v___x_2065_ = v___x_2053_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v___x_2062_);
v___x_2065_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2066_ = lean_array_push(v_fst_2050_, v___x_2065_);
v___x_2067_ = lean_unsigned_to_nat(1u);
v___x_2068_ = lean_nat_add(v_snd_2051_, v___x_2067_);
lean_dec(v_snd_2051_);
v___x_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2066_);
lean_ctor_set(v___x_2069_, 1, v___x_2068_);
v_a_2049_ = v___x_2069_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg___boxed(lean_object* v_edited_2077_, lean_object* v___x_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(v_edited_2077_, v___x_2078_, v_a_2079_, v_a_2080_);
lean_dec_ref(v_a_2079_);
lean_dec(v___x_2078_);
lean_dec_ref(v_edited_2077_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__13(lean_object* v_original_2082_, lean_object* v___x_2083_, lean_object* v_edited_2084_, lean_object* v___x_2085_, lean_object* v_as_2086_, size_t v_sz_2087_, size_t v_i_2088_, lean_object* v_b_2089_){
_start:
{
uint8_t v___x_2090_; 
v___x_2090_ = lean_usize_dec_lt(v_i_2088_, v_sz_2087_);
if (v___x_2090_ == 0)
{
return v_b_2089_;
}
else
{
lean_object* v_snd_2091_; lean_object* v_fst_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2139_; 
v_snd_2091_ = lean_ctor_get(v_b_2089_, 1);
v_fst_2092_ = lean_ctor_get(v_b_2089_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v_b_2089_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2094_ = v_b_2089_;
v_isShared_2095_ = v_isSharedCheck_2139_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_snd_2091_);
lean_inc(v_fst_2092_);
lean_dec(v_b_2089_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2139_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v_fst_2096_; lean_object* v_snd_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2138_; 
v_fst_2096_ = lean_ctor_get(v_snd_2091_, 0);
v_snd_2097_ = lean_ctor_get(v_snd_2091_, 1);
v_isSharedCheck_2138_ = !lean_is_exclusive(v_snd_2091_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2099_ = v_snd_2091_;
v_isShared_2100_ = v_isSharedCheck_2138_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_snd_2097_);
lean_inc(v_fst_2096_);
lean_dec(v_snd_2091_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2138_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v_a_2101_; lean_object* v___x_2103_; 
v_a_2101_ = lean_array_uget_borrowed(v_as_2086_, v_i_2088_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 1, v_fst_2096_);
lean_ctor_set(v___x_2099_, 0, v_fst_2092_);
v___x_2103_ = v___x_2099_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_fst_2092_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v_fst_2096_);
v___x_2103_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
lean_object* v___x_2104_; lean_object* v_fst_2105_; lean_object* v_snd_2106_; lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2136_; 
v___x_2104_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v_original_2082_, v___x_2083_, v_a_2101_, v___x_2103_);
v_fst_2105_ = lean_ctor_get(v___x_2104_, 0);
v_snd_2106_ = lean_ctor_get(v___x_2104_, 1);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2108_ = v___x_2104_;
v_isShared_2109_ = v_isSharedCheck_2136_;
goto v_resetjp_2107_;
}
else
{
lean_inc(v_snd_2106_);
lean_inc(v_fst_2105_);
lean_dec(v___x_2104_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2136_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2111_; 
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 1, v_snd_2097_);
v___x_2111_ = v___x_2108_;
goto v_reusejp_2110_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_fst_2105_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v_snd_2097_);
v___x_2111_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2110_;
}
v_reusejp_2110_:
{
lean_object* v___x_2112_; lean_object* v_fst_2113_; lean_object* v_snd_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2134_; 
v___x_2112_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(v_edited_2084_, v___x_2085_, v_a_2101_, v___x_2111_);
v_fst_2113_ = lean_ctor_get(v___x_2112_, 0);
v_snd_2114_ = lean_ctor_get(v___x_2112_, 1);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2116_ = v___x_2112_;
v_isShared_2117_ = v_isSharedCheck_2134_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_snd_2114_);
lean_inc(v_fst_2113_);
lean_dec(v___x_2112_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2134_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
uint8_t v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2121_; 
v___x_2118_ = 2;
v___x_2119_ = lean_box(v___x_2118_);
lean_inc(v_a_2101_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 1, v_a_2101_);
lean_ctor_set(v___x_2116_, 0, v___x_2119_);
v___x_2121_ = v___x_2116_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2119_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_a_2101_);
v___x_2121_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2127_; 
v___x_2122_ = lean_array_push(v_fst_2113_, v___x_2121_);
v___x_2123_ = lean_unsigned_to_nat(1u);
v___x_2124_ = lean_nat_add(v_snd_2106_, v___x_2123_);
lean_dec(v_snd_2106_);
v___x_2125_ = lean_nat_add(v_snd_2114_, v___x_2123_);
lean_dec(v_snd_2114_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 1, v___x_2125_);
lean_ctor_set(v___x_2094_, 0, v___x_2124_);
v___x_2127_ = v___x_2094_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2124_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
lean_object* v___x_2128_; size_t v___x_2129_; size_t v___x_2130_; 
v___x_2128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2122_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
v___x_2129_ = ((size_t)1ULL);
v___x_2130_ = lean_usize_add(v_i_2088_, v___x_2129_);
v_i_2088_ = v___x_2130_;
v_b_2089_ = v___x_2128_;
goto _start;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__13___boxed(lean_object* v_original_2140_, lean_object* v___x_2141_, lean_object* v_edited_2142_, lean_object* v___x_2143_, lean_object* v_as_2144_, lean_object* v_sz_2145_, lean_object* v_i_2146_, lean_object* v_b_2147_){
_start:
{
size_t v_sz_boxed_2148_; size_t v_i_boxed_2149_; lean_object* v_res_2150_; 
v_sz_boxed_2148_ = lean_unbox_usize(v_sz_2145_);
lean_dec(v_sz_2145_);
v_i_boxed_2149_ = lean_unbox_usize(v_i_2146_);
lean_dec(v_i_2146_);
v_res_2150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__13(v_original_2140_, v___x_2141_, v_edited_2142_, v___x_2143_, v_as_2144_, v_sz_boxed_2148_, v_i_boxed_2149_, v_b_2147_);
lean_dec_ref(v_as_2144_);
lean_dec(v___x_2143_);
lean_dec_ref(v_edited_2142_);
lean_dec(v___x_2141_);
lean_dec_ref(v_original_2140_);
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(lean_object* v_edited_2151_, lean_object* v___x_2152_, lean_object* v_original_2153_, lean_object* v___x_2154_, lean_object* v_as_2155_, size_t v_sz_2156_, size_t v_i_2157_, lean_object* v_b_2158_){
_start:
{
uint8_t v___x_2159_; 
v___x_2159_ = lean_usize_dec_lt(v_i_2157_, v_sz_2156_);
if (v___x_2159_ == 0)
{
return v_b_2158_;
}
else
{
lean_object* v_snd_2160_; lean_object* v_fst_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2208_; 
v_snd_2160_ = lean_ctor_get(v_b_2158_, 1);
v_fst_2161_ = lean_ctor_get(v_b_2158_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_b_2158_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2163_ = v_b_2158_;
v_isShared_2164_ = v_isSharedCheck_2208_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_snd_2160_);
lean_inc(v_fst_2161_);
lean_dec(v_b_2158_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2208_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v_fst_2165_; lean_object* v_snd_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2207_; 
v_fst_2165_ = lean_ctor_get(v_snd_2160_, 0);
v_snd_2166_ = lean_ctor_get(v_snd_2160_, 1);
v_isSharedCheck_2207_ = !lean_is_exclusive(v_snd_2160_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2168_ = v_snd_2160_;
v_isShared_2169_ = v_isSharedCheck_2207_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_snd_2166_);
lean_inc(v_fst_2165_);
lean_dec(v_snd_2160_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2207_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v_a_2170_; lean_object* v___x_2172_; 
v_a_2170_ = lean_array_uget_borrowed(v_as_2155_, v_i_2157_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 1, v_fst_2165_);
lean_ctor_set(v___x_2168_, 0, v_fst_2161_);
v___x_2172_ = v___x_2168_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_fst_2161_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v_fst_2165_);
v___x_2172_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
lean_object* v___x_2173_; lean_object* v_fst_2174_; lean_object* v_snd_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2205_; 
v___x_2173_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v_original_2153_, v___x_2154_, v_a_2170_, v___x_2172_);
v_fst_2174_ = lean_ctor_get(v___x_2173_, 0);
v_snd_2175_ = lean_ctor_get(v___x_2173_, 1);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2177_ = v___x_2173_;
v_isShared_2178_ = v_isSharedCheck_2205_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_snd_2175_);
lean_inc(v_fst_2174_);
lean_dec(v___x_2173_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2205_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 1, v_snd_2166_);
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v_fst_2174_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v_snd_2166_);
v___x_2180_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
lean_object* v___x_2181_; lean_object* v_fst_2182_; lean_object* v_snd_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2203_; 
v___x_2181_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(v_edited_2151_, v___x_2152_, v_a_2170_, v___x_2180_);
v_fst_2182_ = lean_ctor_get(v___x_2181_, 0);
v_snd_2183_ = lean_ctor_get(v___x_2181_, 1);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2181_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2185_ = v___x_2181_;
v_isShared_2186_ = v_isSharedCheck_2203_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_snd_2183_);
lean_inc(v_fst_2182_);
lean_dec(v___x_2181_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2203_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
uint8_t v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2190_; 
v___x_2187_ = 2;
v___x_2188_ = lean_box(v___x_2187_);
lean_inc(v_a_2170_);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 1, v_a_2170_);
lean_ctor_set(v___x_2185_, 0, v___x_2188_);
v___x_2190_ = v___x_2185_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2188_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_a_2170_);
v___x_2190_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2196_; 
v___x_2191_ = lean_array_push(v_fst_2182_, v___x_2190_);
v___x_2192_ = lean_unsigned_to_nat(1u);
v___x_2193_ = lean_nat_add(v_snd_2175_, v___x_2192_);
lean_dec(v_snd_2175_);
v___x_2194_ = lean_nat_add(v_snd_2183_, v___x_2192_);
lean_dec(v_snd_2183_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 1, v___x_2194_);
lean_ctor_set(v___x_2163_, 0, v___x_2193_);
v___x_2196_ = v___x_2163_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2193_);
lean_ctor_set(v_reuseFailAlloc_2201_, 1, v___x_2194_);
v___x_2196_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2197_; size_t v___x_2198_; size_t v___x_2199_; lean_object* v___x_2200_; 
v___x_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2191_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___x_2198_ = ((size_t)1ULL);
v___x_2199_ = lean_usize_add(v_i_2157_, v___x_2198_);
v___x_2200_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__13(v_original_2153_, v___x_2154_, v_edited_2151_, v___x_2152_, v_as_2155_, v_sz_2156_, v___x_2199_, v___x_2197_);
return v___x_2200_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4___boxed(lean_object* v_edited_2209_, lean_object* v___x_2210_, lean_object* v_original_2211_, lean_object* v___x_2212_, lean_object* v_as_2213_, lean_object* v_sz_2214_, lean_object* v_i_2215_, lean_object* v_b_2216_){
_start:
{
size_t v_sz_boxed_2217_; size_t v_i_boxed_2218_; lean_object* v_res_2219_; 
v_sz_boxed_2217_ = lean_unbox_usize(v_sz_2214_);
lean_dec(v_sz_2214_);
v_i_boxed_2218_ = lean_unbox_usize(v_i_2215_);
lean_dec(v_i_2215_);
v_res_2219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v_edited_2209_, v___x_2210_, v_original_2211_, v___x_2212_, v_as_2213_, v_sz_boxed_2217_, v_i_boxed_2218_, v_b_2216_);
lean_dec_ref(v_as_2213_);
lean_dec(v___x_2212_);
lean_dec_ref(v_original_2211_);
lean_dec(v___x_2210_);
lean_dec_ref(v_edited_2209_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2_spec__4(lean_object* v_left_2220_, lean_object* v_right_2221_, lean_object* v_pref_2222_){
_start:
{
lean_object* v_start_2223_; lean_object* v_stop_2224_; lean_object* v_i_2225_; lean_object* v___x_2231_; uint8_t v___x_2232_; 
v_start_2223_ = lean_ctor_get(v_left_2220_, 1);
v_stop_2224_ = lean_ctor_get(v_left_2220_, 2);
v_i_2225_ = lean_array_get_size(v_pref_2222_);
v___x_2231_ = lean_nat_sub(v_stop_2224_, v_start_2223_);
v___x_2232_ = lean_nat_dec_lt(v_i_2225_, v___x_2231_);
lean_dec(v___x_2231_);
if (v___x_2232_ == 0)
{
goto v___jp_2226_;
}
else
{
lean_object* v_start_2233_; lean_object* v_stop_2234_; lean_object* v___x_2235_; uint8_t v___x_2236_; 
v_start_2233_ = lean_ctor_get(v_right_2221_, 1);
v_stop_2234_ = lean_ctor_get(v_right_2221_, 2);
v___x_2235_ = lean_nat_sub(v_stop_2234_, v_start_2233_);
v___x_2236_ = lean_nat_dec_lt(v_i_2225_, v___x_2235_);
lean_dec(v___x_2235_);
if (v___x_2236_ == 0)
{
goto v___jp_2226_;
}
else
{
lean_object* v___x_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; 
v___x_2237_ = l_Subarray_get___redArg(v_left_2220_, v_i_2225_);
v___x_2238_ = l_Subarray_get___redArg(v_right_2221_, v_i_2225_);
v___x_2239_ = lean_string_dec_eq(v___x_2237_, v___x_2238_);
lean_dec(v___x_2238_);
if (v___x_2239_ == 0)
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
lean_dec(v___x_2237_);
v___x_2240_ = l_Subarray_drop___redArg(v_left_2220_, v_i_2225_);
v___x_2241_ = l_Subarray_drop___redArg(v_right_2221_, v_i_2225_);
v___x_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2240_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
v___x_2243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2243_, 0, v_pref_2222_);
lean_ctor_set(v___x_2243_, 1, v___x_2242_);
return v___x_2243_;
}
else
{
lean_object* v___x_2244_; 
v___x_2244_ = lean_array_push(v_pref_2222_, v___x_2237_);
v_pref_2222_ = v___x_2244_;
goto _start;
}
}
}
v___jp_2226_:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2227_ = l_Subarray_drop___redArg(v_left_2220_, v_i_2225_);
v___x_2228_ = l_Subarray_drop___redArg(v_right_2221_, v_i_2225_);
v___x_2229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2227_);
lean_ctor_set(v___x_2229_, 1, v___x_2228_);
v___x_2230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2230_, 0, v_pref_2222_);
lean_ctor_set(v___x_2230_, 1, v___x_2229_);
return v___x_2230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2(lean_object* v_left_2246_, lean_object* v_right_2247_){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2249_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2_spec__4(v_left_2246_, v_right_2247_, v___x_2248_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(lean_object* v_a_2250_, lean_object* v_b_2251_){
_start:
{
lean_object* v_array_2252_; lean_object* v_start_2253_; lean_object* v_stop_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2267_; 
v_array_2252_ = lean_ctor_get(v_a_2250_, 0);
v_start_2253_ = lean_ctor_get(v_a_2250_, 1);
v_stop_2254_ = lean_ctor_get(v_a_2250_, 2);
v_isSharedCheck_2267_ = !lean_is_exclusive(v_a_2250_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2256_ = v_a_2250_;
v_isShared_2257_ = v_isSharedCheck_2267_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_stop_2254_);
lean_inc(v_start_2253_);
lean_inc(v_array_2252_);
lean_dec(v_a_2250_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2267_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
uint8_t v___x_2258_; 
v___x_2258_ = lean_nat_dec_lt(v_start_2253_, v_stop_2254_);
if (v___x_2258_ == 0)
{
lean_del_object(v___x_2256_);
lean_dec(v_stop_2254_);
lean_dec(v_start_2253_);
lean_dec_ref(v_array_2252_);
return v_b_2251_;
}
else
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2262_; 
v___x_2259_ = lean_unsigned_to_nat(1u);
v___x_2260_ = lean_nat_add(v_start_2253_, v___x_2259_);
lean_inc_ref(v_array_2252_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 1, v___x_2260_);
v___x_2262_ = v___x_2256_;
goto v_reusejp_2261_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_array_2252_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v___x_2260_);
lean_ctor_set(v_reuseFailAlloc_2266_, 2, v_stop_2254_);
v___x_2262_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2261_;
}
v_reusejp_2261_:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = lean_array_fget(v_array_2252_, v_start_2253_);
lean_dec(v_start_2253_);
lean_dec_ref(v_array_2252_);
v___x_2264_ = lean_array_push(v_b_2251_, v___x_2263_);
v_a_2250_ = v___x_2262_;
v_b_2251_ = v___x_2264_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6(lean_object* v_left_2268_, lean_object* v_right_2269_, lean_object* v_i_2270_){
_start:
{
lean_object* v_start_2271_; lean_object* v_stop_2272_; lean_object* v___x_2273_; uint8_t v___x_2287_; 
v_start_2271_ = lean_ctor_get(v_left_2268_, 1);
v_stop_2272_ = lean_ctor_get(v_left_2268_, 2);
v___x_2273_ = lean_nat_sub(v_stop_2272_, v_start_2271_);
v___x_2287_ = lean_nat_dec_lt(v_i_2270_, v___x_2273_);
if (v___x_2287_ == 0)
{
goto v___jp_2274_;
}
else
{
lean_object* v_start_2288_; lean_object* v_stop_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
v_start_2288_ = lean_ctor_get(v_right_2269_, 1);
v_stop_2289_ = lean_ctor_get(v_right_2269_, 2);
v___x_2290_ = lean_nat_sub(v_stop_2289_, v_start_2288_);
v___x_2291_ = lean_nat_dec_lt(v_i_2270_, v___x_2290_);
if (v___x_2291_ == 0)
{
lean_dec(v___x_2290_);
goto v___jp_2274_;
}
else
{
lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; 
v___x_2292_ = lean_nat_sub(v___x_2273_, v_i_2270_);
lean_dec(v___x_2273_);
v___x_2293_ = lean_unsigned_to_nat(1u);
v___x_2294_ = lean_nat_sub(v___x_2292_, v___x_2293_);
v___x_2295_ = l_Subarray_get___redArg(v_left_2268_, v___x_2294_);
lean_dec(v___x_2294_);
v___x_2296_ = lean_nat_sub(v___x_2290_, v_i_2270_);
lean_dec(v___x_2290_);
v___x_2297_ = lean_nat_sub(v___x_2296_, v___x_2293_);
v___x_2298_ = l_Subarray_get___redArg(v_right_2269_, v___x_2297_);
lean_dec(v___x_2297_);
v___x_2299_ = lean_string_dec_eq(v___x_2295_, v___x_2298_);
lean_dec(v___x_2298_);
lean_dec(v___x_2295_);
if (v___x_2299_ == 0)
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
lean_dec(v_i_2270_);
lean_inc_ref(v_left_2268_);
v___x_2300_ = l_Subarray_take___redArg(v_left_2268_, v___x_2292_);
v___x_2301_ = l_Subarray_take___redArg(v_right_2269_, v___x_2296_);
lean_dec(v___x_2296_);
v___x_2302_ = l_Subarray_drop___redArg(v_left_2268_, v___x_2292_);
lean_dec(v___x_2292_);
v___x_2303_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2304_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v___x_2302_, v___x_2303_);
v___x_2305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2301_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
v___x_2306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2300_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
return v___x_2306_;
}
else
{
lean_object* v___x_2307_; 
lean_dec(v___x_2296_);
lean_dec(v___x_2292_);
v___x_2307_ = lean_nat_add(v_i_2270_, v___x_2293_);
lean_dec(v_i_2270_);
v_i_2270_ = v___x_2307_;
goto _start;
}
}
}
v___jp_2274_:
{
lean_object* v_start_2275_; lean_object* v_stop_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v_start_2275_ = lean_ctor_get(v_right_2269_, 1);
v_stop_2276_ = lean_ctor_get(v_right_2269_, 2);
v___x_2277_ = lean_nat_sub(v___x_2273_, v_i_2270_);
lean_dec(v___x_2273_);
lean_inc_ref(v_left_2268_);
v___x_2278_ = l_Subarray_take___redArg(v_left_2268_, v___x_2277_);
v___x_2279_ = lean_nat_sub(v_stop_2276_, v_start_2275_);
v___x_2280_ = lean_nat_sub(v___x_2279_, v_i_2270_);
lean_dec(v_i_2270_);
lean_dec(v___x_2279_);
v___x_2281_ = l_Subarray_take___redArg(v_right_2269_, v___x_2280_);
lean_dec(v___x_2280_);
v___x_2282_ = l_Subarray_drop___redArg(v_left_2268_, v___x_2277_);
lean_dec(v___x_2277_);
v___x_2283_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2284_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v___x_2282_, v___x_2283_);
v___x_2285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2281_);
lean_ctor_set(v___x_2285_, 1, v___x_2284_);
v___x_2286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2278_);
lean_ctor_set(v___x_2286_, 1, v___x_2285_);
return v___x_2286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3(lean_object* v_left_2309_, lean_object* v_right_2310_){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = lean_unsigned_to_nat(0u);
v___x_2312_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6(v_left_2309_, v_right_2310_, v___x_2311_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11_spec__21___redArg(lean_object* v_m_2313_, lean_object* v_query_2314_, lean_object* v_x_2315_, lean_object* v_x_2316_, lean_object* v_x_2317_){
_start:
{
lean_object* v_zero_2318_; uint8_t v_isZero_2319_; 
v_zero_2318_ = lean_unsigned_to_nat(0u);
v_isZero_2319_ = lean_nat_dec_eq(v_x_2316_, v_zero_2318_);
if (v_isZero_2319_ == 1)
{
lean_dec(v_x_2317_);
lean_dec(v_x_2316_);
if (lean_obj_tag(v_x_2315_) == 0)
{
lean_object* v___x_2320_; 
v___x_2320_ = lean_box(2);
return v___x_2320_;
}
else
{
lean_object* v_val_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
v_val_2321_ = lean_ctor_get(v_x_2315_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v_x_2315_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v_x_2315_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_val_2321_);
lean_dec(v_x_2315_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_val_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
else
{
lean_object* v_keyArray_2329_; lean_object* v_valueArray_2330_; lean_object* v___x_2331_; uint8_t v_isSome_2332_; 
v_keyArray_2329_ = lean_ctor_get(v_m_2313_, 1);
v_valueArray_2330_ = lean_ctor_get(v_m_2313_, 2);
v___x_2331_ = lean_array_fget_borrowed(v_keyArray_2329_, v_x_2317_);
v_isSome_2332_ = lean_noption_is_some(v___x_2331_);
if (v_isSome_2332_ == 0)
{
lean_dec(v_x_2316_);
if (lean_obj_tag(v_x_2315_) == 0)
{
lean_object* v___x_2333_; 
v___x_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2333_, 0, v_x_2317_);
return v___x_2333_;
}
else
{
lean_object* v_val_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec(v_x_2317_);
v_val_2334_ = lean_ctor_get(v_x_2315_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v_x_2315_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v_x_2315_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_val_2334_);
lean_dec(v_x_2315_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_val_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
else
{
lean_object* v_one_2342_; lean_object* v_n_2343_; lean_object* v___y_2345_; 
v_one_2342_ = lean_unsigned_to_nat(1u);
v_n_2343_ = lean_nat_sub(v_x_2316_, v_one_2342_);
lean_dec(v_x_2316_);
if (v_isSome_2332_ == 0)
{
goto v___jp_2351_;
}
else
{
lean_object* v___x_2353_; uint8_t v_isSome_2354_; 
v___x_2353_ = lean_array_fget_borrowed(v_valueArray_2330_, v_x_2317_);
v_isSome_2354_ = lean_noption_is_some(v___x_2353_);
if (v_isSome_2354_ == 0)
{
goto v___jp_2351_;
}
else
{
lean_object* v_val_2355_; uint8_t v___x_2356_; 
lean_inc(v___x_2331_);
v_val_2355_ = lean_noption_get(v___x_2331_);
v___x_2356_ = lean_string_dec_eq(v_val_2355_, v_query_2314_);
if (v___x_2356_ == 0)
{
lean_object* v___x_2357_; lean_object* v___x_2358_; uint8_t v___x_2359_; 
lean_dec(v_val_2355_);
v___x_2357_ = lean_array_get_size(v_keyArray_2329_);
v___x_2358_ = lean_nat_add(v_x_2317_, v_one_2342_);
lean_dec(v_x_2317_);
v___x_2359_ = lean_nat_dec_lt(v___x_2358_, v___x_2357_);
if (v___x_2359_ == 0)
{
lean_dec(v___x_2358_);
v_x_2316_ = v_n_2343_;
v_x_2317_ = v_zero_2318_;
goto _start;
}
else
{
v_x_2316_ = v_n_2343_;
v_x_2317_ = v___x_2358_;
goto _start;
}
}
else
{
lean_object* v_val_2362_; lean_object* v___x_2363_; 
lean_dec(v_n_2343_);
lean_dec(v_x_2315_);
lean_inc(v___x_2353_);
v_val_2362_ = lean_noption_get(v___x_2353_);
v___x_2363_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2363_, 0, v_x_2317_);
lean_ctor_set(v___x_2363_, 1, v_val_2355_);
lean_ctor_set(v___x_2363_, 2, v_val_2362_);
return v___x_2363_;
}
}
}
v___jp_2344_:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; uint8_t v___x_2348_; 
v___x_2346_ = lean_array_get_size(v_keyArray_2329_);
v___x_2347_ = lean_nat_add(v_x_2317_, v_one_2342_);
lean_dec(v_x_2317_);
v___x_2348_ = lean_nat_dec_lt(v___x_2347_, v___x_2346_);
if (v___x_2348_ == 0)
{
lean_dec(v___x_2347_);
v_x_2315_ = v___y_2345_;
v_x_2316_ = v_n_2343_;
v_x_2317_ = v_zero_2318_;
goto _start;
}
else
{
v_x_2315_ = v___y_2345_;
v_x_2316_ = v_n_2343_;
v_x_2317_ = v___x_2347_;
goto _start;
}
}
v___jp_2351_:
{
if (lean_obj_tag(v_x_2315_) == 0)
{
lean_object* v___x_2352_; 
lean_inc(v_x_2317_);
v___x_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2352_, 0, v_x_2317_);
v___y_2345_ = v___x_2352_;
goto v___jp_2344_;
}
else
{
v___y_2345_ = v_x_2315_;
goto v___jp_2344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11_spec__21___redArg___boxed(lean_object* v_m_2364_, lean_object* v_query_2365_, lean_object* v_x_2366_, lean_object* v_x_2367_, lean_object* v_x_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11_spec__21___redArg(v_m_2364_, v_query_2365_, v_x_2366_, v_x_2367_, v_x_2368_);
lean_dec_ref(v_query_2365_);
lean_dec_ref(v_m_2364_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11___redArg(lean_object* v_m_2370_, lean_object* v_query_2371_){
_start:
{
lean_object* v_keyArray_2372_; lean_object* v___x_2373_; uint64_t v___x_2374_; uint64_t v___x_2375_; uint64_t v___x_2376_; uint64_t v_fold_2377_; uint64_t v___x_2378_; uint64_t v___x_2379_; uint64_t v___x_2380_; size_t v___x_2381_; size_t v___x_2382_; size_t v___x_2383_; size_t v___x_2384_; size_t v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v_keyArray_2372_ = lean_ctor_get(v_m_2370_, 1);
v___x_2373_ = lean_array_get_size(v_keyArray_2372_);
v___x_2374_ = lean_string_hash(v_query_2371_);
v___x_2375_ = 32ULL;
v___x_2376_ = lean_uint64_shift_right(v___x_2374_, v___x_2375_);
v_fold_2377_ = lean_uint64_xor(v___x_2374_, v___x_2376_);
v___x_2378_ = 16ULL;
v___x_2379_ = lean_uint64_shift_right(v_fold_2377_, v___x_2378_);
v___x_2380_ = lean_uint64_xor(v_fold_2377_, v___x_2379_);
v___x_2381_ = lean_uint64_to_usize(v___x_2380_);
v___x_2382_ = lean_usize_of_nat(v___x_2373_);
v___x_2383_ = ((size_t)1ULL);
v___x_2384_ = lean_usize_sub(v___x_2382_, v___x_2383_);
v___x_2385_ = lean_usize_land(v___x_2381_, v___x_2384_);
v___x_2386_ = lean_usize_to_nat(v___x_2385_);
v___x_2387_ = lean_box(0);
v___x_2388_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11_spec__21___redArg(v_m_2370_, v_query_2371_, v___x_2387_, v___x_2373_, v___x_2386_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11___redArg___boxed(lean_object* v_m_2389_, lean_object* v_query_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11___redArg(v_m_2389_, v_query_2390_);
lean_dec_ref(v_query_2390_);
lean_dec_ref(v_m_2389_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23_spec__28___redArg(lean_object* v_b_2392_, lean_object* v_acc_2393_, lean_object* v_i_2394_){
_start:
{
lean_object* v___y_2396_; lean_object* v_keyArray_2404_; lean_object* v_valueArray_2405_; lean_object* v___x_2406_; uint8_t v___x_2407_; 
v_keyArray_2404_ = lean_ctor_get(v_b_2392_, 1);
v_valueArray_2405_ = lean_ctor_get(v_b_2392_, 2);
v___x_2406_ = lean_array_get_size(v_keyArray_2404_);
v___x_2407_ = lean_nat_dec_lt(v_i_2394_, v___x_2406_);
if (v___x_2407_ == 0)
{
lean_dec(v_i_2394_);
return v_acc_2393_;
}
else
{
lean_object* v___x_2408_; uint8_t v_isSome_2409_; 
v___x_2408_ = lean_array_fget_borrowed(v_keyArray_2404_, v_i_2394_);
v_isSome_2409_ = lean_noption_is_some(v___x_2408_);
if (v_isSome_2409_ == 0)
{
goto v___jp_2400_;
}
else
{
lean_object* v___x_2410_; uint8_t v_isSome_2411_; 
v___x_2410_ = lean_array_fget_borrowed(v_valueArray_2405_, v_i_2394_);
v_isSome_2411_ = lean_noption_is_some(v___x_2410_);
if (v_isSome_2411_ == 0)
{
goto v___jp_2400_;
}
else
{
lean_object* v_val_2412_; lean_object* v_val_2413_; lean_object* v_i_2415_; lean_object* v___x_2420_; 
lean_inc(v___x_2408_);
v_val_2412_ = lean_noption_get(v___x_2408_);
lean_inc(v___x_2410_);
v_val_2413_ = lean_noption_get(v___x_2410_);
v___x_2420_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11___redArg(v_acc_2393_, v_val_2412_);
switch(lean_obj_tag(v___x_2420_))
{
case 0:
{
lean_object* v_index_2421_; lean_object* v_size_2422_; lean_object* v___x_2423_; 
v_index_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_index_2421_);
lean_dec_ref_known(v___x_2420_, 3);
v_size_2422_ = lean_ctor_get(v_acc_2393_, 0);
lean_inc(v_size_2422_);
v___x_2423_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2393_, v_size_2422_, v_index_2421_, v_val_2412_, v_val_2413_);
lean_dec(v_index_2421_);
v___y_2396_ = v___x_2423_;
goto v___jp_2395_;
}
case 1:
{
lean_object* v_index_2424_; 
v_index_2424_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_index_2424_);
lean_dec_ref_known(v___x_2420_, 1);
v_i_2415_ = v_index_2424_;
goto v___jp_2414_;
}
default: 
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = lean_unsigned_to_nat(0u);
v___x_2426_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_2393_, v___x_2425_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_index_2427_; 
v_index_2427_ = lean_ctor_get(v___x_2426_, 0);
lean_inc(v_index_2427_);
lean_dec_ref_known(v___x_2426_, 1);
v_i_2415_ = v_index_2427_;
goto v___jp_2414_;
}
else
{
lean_dec(v_val_2413_);
lean_dec(v_val_2412_);
v___y_2396_ = v_acc_2393_;
goto v___jp_2395_;
}
}
}
v___jp_2414_:
{
lean_object* v_size_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v_size_2416_ = lean_ctor_get(v_acc_2393_, 0);
v___x_2417_ = lean_unsigned_to_nat(1u);
v___x_2418_ = lean_nat_add(v_size_2416_, v___x_2417_);
v___x_2419_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2393_, v___x_2418_, v_i_2415_, v_val_2412_, v_val_2413_);
lean_dec(v_i_2415_);
v___y_2396_ = v___x_2419_;
goto v___jp_2395_;
}
}
}
}
v___jp_2395_:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = lean_unsigned_to_nat(1u);
v___x_2398_ = lean_nat_add(v_i_2394_, v___x_2397_);
lean_dec(v_i_2394_);
v_acc_2393_ = v___y_2396_;
v_i_2394_ = v___x_2398_;
goto _start;
}
v___jp_2400_:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2401_ = lean_unsigned_to_nat(1u);
v___x_2402_ = lean_nat_add(v_i_2394_, v___x_2401_);
lean_dec(v_i_2394_);
v_i_2394_ = v___x_2402_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23_spec__28___redArg___boxed(lean_object* v_b_2428_, lean_object* v_acc_2429_, lean_object* v_i_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23_spec__28___redArg(v_b_2428_, v_acc_2429_, v_i_2430_);
lean_dec_ref(v_b_2428_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23___redArg(lean_object* v_init_2432_, lean_object* v_b_2433_){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2434_ = lean_unsigned_to_nat(0u);
v___x_2435_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23_spec__28___redArg(v_b_2433_, v_init_2432_, v___x_2434_);
return v___x_2435_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23___redArg___boxed(lean_object* v_init_2436_, lean_object* v_b_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23___redArg(v_init_2436_, v_b_2437_);
lean_dec_ref(v_b_2437_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12___redArg(lean_object* v_m_2439_){
_start:
{
lean_object* v_keyArray_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v_cellCount_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v_target_2447_; lean_object* v___x_2448_; 
v_keyArray_2440_ = lean_ctor_get(v_m_2439_, 1);
v___x_2441_ = lean_array_get_size(v_keyArray_2440_);
v___x_2442_ = lean_unsigned_to_nat(2u);
v_cellCount_2443_ = lean_nat_mul(v___x_2441_, v___x_2442_);
v___x_2444_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_2443_);
v___x_2445_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2443_);
v___x_2446_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2443_);
v_target_2447_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_2447_, 0, v___x_2444_);
lean_ctor_set(v_target_2447_, 1, v___x_2445_);
lean_ctor_set(v_target_2447_, 2, v___x_2446_);
v___x_2448_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23___redArg(v_target_2447_, v_m_2439_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12___redArg___boxed(lean_object* v_m_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12___redArg(v_m_2449_);
lean_dec_ref(v_m_2449_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10_spec__19___redArg(lean_object* v_m_2451_, lean_object* v_query_2452_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11___redArg(v_m_2451_, v_query_2452_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_index_2454_; lean_object* v_key_2455_; lean_object* v_value_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
v_index_2454_ = lean_ctor_get(v___x_2453_, 0);
v_key_2455_ = lean_ctor_get(v___x_2453_, 1);
v_value_2456_ = lean_ctor_get(v___x_2453_, 2);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2453_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_value_2456_);
lean_inc(v_key_2455_);
lean_inc(v_index_2454_);
lean_dec(v___x_2453_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_index_2454_);
lean_ctor_set(v_reuseFailAlloc_2462_, 1, v_key_2455_);
lean_ctor_set(v_reuseFailAlloc_2462_, 2, v_value_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
else
{
lean_object* v___x_2464_; 
lean_dec(v___x_2453_);
v___x_2464_ = lean_box(1);
return v___x_2464_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10_spec__19___redArg___boxed(lean_object* v_m_2465_, lean_object* v_query_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10_spec__19___redArg(v_m_2465_, v_query_2466_);
lean_dec_ref(v_query_2466_);
lean_dec_ref(v_m_2465_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10___redArg(lean_object* v_m_2468_, lean_object* v_a_2469_){
_start:
{
lean_object* v___x_2470_; 
v___x_2470_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10_spec__19___redArg(v_m_2468_, v_a_2469_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v_value_2471_; lean_object* v___x_2472_; 
v_value_2471_ = lean_ctor_get(v___x_2470_, 2);
lean_inc(v_value_2471_);
lean_dec_ref_known(v___x_2470_, 3);
v___x_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2472_, 0, v_value_2471_);
return v___x_2472_;
}
else
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_box(0);
return v___x_2473_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10___redArg___boxed(lean_object* v_m_2474_, lean_object* v_a_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10___redArg(v_m_2474_, v_a_2475_);
lean_dec_ref(v_a_2475_);
lean_dec_ref(v_m_2474_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(lean_object* v_histogram_2477_, lean_object* v_index_2478_, lean_object* v_val_2479_){
_start:
{
lean_object* v___x_2480_; 
v___x_2480_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10___redArg(v_histogram_2477_, v_val_2479_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___y_2487_; lean_object* v_i_2488_; lean_object* v___y_2493_; lean_object* v___y_2502_; lean_object* v_i_2503_; lean_object* v___x_2516_; 
v___x_2481_ = lean_unsigned_to_nat(1u);
v___x_2482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2482_, 0, v_index_2478_);
v___x_2483_ = lean_unsigned_to_nat(0u);
v___x_2484_ = lean_box(0);
v___x_2485_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2481_);
lean_ctor_set(v___x_2485_, 1, v___x_2482_);
lean_ctor_set(v___x_2485_, 2, v___x_2483_);
lean_ctor_set(v___x_2485_, 3, v___x_2484_);
v___x_2516_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11___redArg(v_histogram_2477_, v_val_2479_);
switch(lean_obj_tag(v___x_2516_))
{
case 0:
{
lean_object* v_index_2517_; lean_object* v_size_2518_; lean_object* v___x_2519_; 
v_index_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_index_2517_);
lean_dec_ref_known(v___x_2516_, 3);
v_size_2518_ = lean_ctor_get(v_histogram_2477_, 0);
lean_inc(v_size_2518_);
v___x_2519_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_2477_, v_size_2518_, v_index_2517_, v_val_2479_, v___x_2485_);
lean_dec(v_index_2517_);
return v___x_2519_;
}
case 1:
{
lean_object* v_index_2520_; lean_object* v_size_2521_; lean_object* v_keyArray_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; uint8_t v___x_2525_; 
v_index_2520_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_index_2520_);
lean_dec_ref_known(v___x_2516_, 1);
v_size_2521_ = lean_ctor_get(v_histogram_2477_, 0);
v_keyArray_2522_ = lean_ctor_get(v_histogram_2477_, 1);
v___x_2523_ = lean_nat_add(v_size_2521_, v___x_2481_);
v___x_2524_ = lean_array_get_size(v_keyArray_2522_);
v___x_2525_ = lean_nat_dec_lt(v___x_2523_, v___x_2524_);
if (v___x_2525_ == 0)
{
lean_dec(v___x_2523_);
lean_dec(v_index_2520_);
goto v___jp_2507_;
}
else
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; 
v___x_2526_ = lean_unsigned_to_nat(4u);
v___x_2527_ = lean_nat_mul(v___x_2523_, v___x_2526_);
v___x_2528_ = lean_unsigned_to_nat(3u);
v___x_2529_ = lean_nat_mul(v___x_2524_, v___x_2528_);
v___x_2530_ = lean_nat_dec_le(v___x_2527_, v___x_2529_);
lean_dec(v___x_2529_);
lean_dec(v___x_2527_);
if (v___x_2530_ == 0)
{
lean_dec(v___x_2523_);
lean_dec(v_index_2520_);
goto v___jp_2507_;
}
else
{
lean_object* v___x_2531_; 
v___x_2531_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_2477_, v___x_2523_, v_index_2520_, v_val_2479_, v___x_2485_);
lean_dec(v_index_2520_);
return v___x_2531_;
}
}
}
default: 
{
lean_object* v_size_2532_; lean_object* v_keyArray_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; uint8_t v___x_2536_; 
v_size_2532_ = lean_ctor_get(v_histogram_2477_, 0);
v_keyArray_2533_ = lean_ctor_get(v_histogram_2477_, 1);
v___x_2534_ = lean_nat_add(v_size_2532_, v___x_2481_);
v___x_2535_ = lean_array_get_size(v_keyArray_2533_);
v___x_2536_ = lean_nat_dec_lt(v___x_2534_, v___x_2535_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; 
lean_dec(v___x_2534_);
v___x_2537_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12___redArg(v_histogram_2477_);
lean_dec_ref(v_histogram_2477_);
v___y_2493_ = v___x_2537_;
goto v___jp_2492_;
}
else
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; uint8_t v___x_2542_; 
v___x_2538_ = lean_unsigned_to_nat(4u);
v___x_2539_ = lean_nat_mul(v___x_2534_, v___x_2538_);
lean_dec(v___x_2534_);
v___x_2540_ = lean_unsigned_to_nat(3u);
v___x_2541_ = lean_nat_mul(v___x_2535_, v___x_2540_);
v___x_2542_ = lean_nat_dec_le(v___x_2539_, v___x_2541_);
lean_dec(v___x_2541_);
lean_dec(v___x_2539_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; 
v___x_2543_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12___redArg(v_histogram_2477_);
lean_dec_ref(v_histogram_2477_);
v___y_2493_ = v___x_2543_;
goto v___jp_2492_;
}
else
{
v___y_2493_ = v_histogram_2477_;
goto v___jp_2492_;
}
}
}
}
v___jp_2486_:
{
lean_object* v_size_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; 
v_size_2489_ = lean_ctor_get(v___y_2487_, 0);
v___x_2490_ = lean_nat_add(v_size_2489_, v___x_2481_);
v___x_2491_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2487_, v___x_2490_, v_i_2488_, v_val_2479_, v___x_2485_);
lean_dec(v_i_2488_);
return v___x_2491_;
}
v___jp_2492_:
{
lean_object* v___x_2494_; 
v___x_2494_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11___redArg(v___y_2493_, v_val_2479_);
switch(lean_obj_tag(v___x_2494_))
{
case 0:
{
lean_object* v_index_2495_; lean_object* v_size_2496_; lean_object* v___x_2497_; 
v_index_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_index_2495_);
lean_dec_ref_known(v___x_2494_, 3);
v_size_2496_ = lean_ctor_get(v___y_2493_, 0);
lean_inc(v_size_2496_);
v___x_2497_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2493_, v_size_2496_, v_index_2495_, v_val_2479_, v___x_2485_);
lean_dec(v_index_2495_);
return v___x_2497_;
}
case 1:
{
lean_object* v_index_2498_; 
v_index_2498_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_index_2498_);
lean_dec_ref_known(v___x_2494_, 1);
v___y_2487_ = v___y_2493_;
v_i_2488_ = v_index_2498_;
goto v___jp_2486_;
}
default: 
{
lean_object* v___x_2499_; 
v___x_2499_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2493_, v___x_2483_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v_index_2500_; 
v_index_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_index_2500_);
lean_dec_ref_known(v___x_2499_, 1);
v___y_2487_ = v___y_2493_;
v_i_2488_ = v_index_2500_;
goto v___jp_2486_;
}
else
{
lean_dec_ref_known(v___x_2485_, 4);
lean_dec_ref(v_val_2479_);
return v___y_2493_;
}
}
}
}
v___jp_2501_:
{
lean_object* v_size_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; 
v_size_2504_ = lean_ctor_get(v___y_2502_, 0);
v___x_2505_ = lean_nat_add(v_size_2504_, v___x_2481_);
v___x_2506_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2502_, v___x_2505_, v_i_2503_, v_val_2479_, v___x_2485_);
lean_dec(v_i_2503_);
return v___x_2506_;
}
v___jp_2507_:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12___redArg(v_histogram_2477_);
lean_dec_ref(v_histogram_2477_);
v___x_2509_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11___redArg(v___x_2508_, v_val_2479_);
switch(lean_obj_tag(v___x_2509_))
{
case 0:
{
lean_object* v_index_2510_; lean_object* v_size_2511_; lean_object* v___x_2512_; 
v_index_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_index_2510_);
lean_dec_ref_known(v___x_2509_, 3);
v_size_2511_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_size_2511_);
v___x_2512_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2508_, v_size_2511_, v_index_2510_, v_val_2479_, v___x_2485_);
lean_dec(v_index_2510_);
return v___x_2512_;
}
case 1:
{
lean_object* v_index_2513_; 
v_index_2513_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_index_2513_);
lean_dec_ref_known(v___x_2509_, 1);
v___y_2502_ = v___x_2508_;
v_i_2503_ = v_index_2513_;
goto v___jp_2501_;
}
default: 
{
lean_object* v___x_2514_; 
v___x_2514_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2508_, v___x_2483_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_index_2515_; 
v_index_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_index_2515_);
lean_dec_ref_known(v___x_2514_, 1);
v___y_2502_ = v___x_2508_;
v_i_2503_ = v_index_2515_;
goto v___jp_2501_;
}
else
{
lean_dec_ref_known(v___x_2485_, 4);
lean_dec_ref(v_val_2479_);
return v___x_2508_;
}
}
}
}
}
else
{
lean_object* v_val_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2624_; 
v_val_2544_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2546_ = v___x_2480_;
v_isShared_2547_ = v_isSharedCheck_2624_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_val_2544_);
lean_dec(v___x_2480_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2624_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v_leftCount_2548_; lean_object* v_rightCount_2549_; lean_object* v_rightIndex_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2622_; 
v_leftCount_2548_ = lean_ctor_get(v_val_2544_, 0);
v_rightCount_2549_ = lean_ctor_get(v_val_2544_, 2);
v_rightIndex_2550_ = lean_ctor_get(v_val_2544_, 3);
v_isSharedCheck_2622_ = !lean_is_exclusive(v_val_2544_);
if (v_isSharedCheck_2622_ == 0)
{
lean_object* v_unused_2623_; 
v_unused_2623_ = lean_ctor_get(v_val_2544_, 1);
lean_dec(v_unused_2623_);
v___x_2552_ = v_val_2544_;
v_isShared_2553_ = v_isSharedCheck_2622_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_rightIndex_2550_);
lean_inc(v_rightCount_2549_);
lean_inc(v_leftCount_2548_);
lean_dec(v_val_2544_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2622_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2557_; 
v___x_2554_ = lean_unsigned_to_nat(1u);
v___x_2555_ = lean_nat_add(v_leftCount_2548_, v___x_2554_);
lean_dec(v_leftCount_2548_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 0, v_index_2478_);
v___x_2557_ = v___x_2546_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_index_2478_);
v___x_2557_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
lean_object* v___x_2559_; 
if (v_isShared_2553_ == 0)
{
lean_ctor_set(v___x_2552_, 1, v___x_2557_);
lean_ctor_set(v___x_2552_, 0, v___x_2555_);
v___x_2559_ = v___x_2552_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___x_2555_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v___x_2557_);
lean_ctor_set(v_reuseFailAlloc_2620_, 2, v_rightCount_2549_);
lean_ctor_set(v_reuseFailAlloc_2620_, 3, v_rightIndex_2550_);
v___x_2559_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
lean_object* v___y_2561_; lean_object* v_i_2562_; lean_object* v___y_2567_; lean_object* v___y_2577_; lean_object* v_i_2578_; lean_object* v___x_2592_; 
v___x_2592_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11___redArg(v_histogram_2477_, v_val_2479_);
switch(lean_obj_tag(v___x_2592_))
{
case 0:
{
lean_object* v_index_2593_; lean_object* v_size_2594_; lean_object* v___x_2595_; 
v_index_2593_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_index_2593_);
lean_dec_ref_known(v___x_2592_, 3);
v_size_2594_ = lean_ctor_get(v_histogram_2477_, 0);
lean_inc(v_size_2594_);
v___x_2595_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_2477_, v_size_2594_, v_index_2593_, v_val_2479_, v___x_2559_);
lean_dec(v_index_2593_);
return v___x_2595_;
}
case 1:
{
lean_object* v_index_2596_; lean_object* v_size_2597_; lean_object* v_keyArray_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; uint8_t v___x_2601_; 
v_index_2596_ = lean_ctor_get(v___x_2592_, 0);
lean_inc(v_index_2596_);
lean_dec_ref_known(v___x_2592_, 1);
v_size_2597_ = lean_ctor_get(v_histogram_2477_, 0);
v_keyArray_2598_ = lean_ctor_get(v_histogram_2477_, 1);
v___x_2599_ = lean_nat_add(v_size_2597_, v___x_2554_);
v___x_2600_ = lean_array_get_size(v_keyArray_2598_);
v___x_2601_ = lean_nat_dec_lt(v___x_2599_, v___x_2600_);
if (v___x_2601_ == 0)
{
lean_dec(v___x_2599_);
lean_dec(v_index_2596_);
goto v___jp_2582_;
}
else
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; uint8_t v___x_2606_; 
v___x_2602_ = lean_unsigned_to_nat(4u);
v___x_2603_ = lean_nat_mul(v___x_2599_, v___x_2602_);
v___x_2604_ = lean_unsigned_to_nat(3u);
v___x_2605_ = lean_nat_mul(v___x_2600_, v___x_2604_);
v___x_2606_ = lean_nat_dec_le(v___x_2603_, v___x_2605_);
lean_dec(v___x_2605_);
lean_dec(v___x_2603_);
if (v___x_2606_ == 0)
{
lean_dec(v___x_2599_);
lean_dec(v_index_2596_);
goto v___jp_2582_;
}
else
{
lean_object* v___x_2607_; 
v___x_2607_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_2477_, v___x_2599_, v_index_2596_, v_val_2479_, v___x_2559_);
lean_dec(v_index_2596_);
return v___x_2607_;
}
}
}
default: 
{
lean_object* v_size_2608_; lean_object* v_keyArray_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; uint8_t v___x_2612_; 
v_size_2608_ = lean_ctor_get(v_histogram_2477_, 0);
v_keyArray_2609_ = lean_ctor_get(v_histogram_2477_, 1);
v___x_2610_ = lean_nat_add(v_size_2608_, v___x_2554_);
v___x_2611_ = lean_array_get_size(v_keyArray_2609_);
v___x_2612_ = lean_nat_dec_lt(v___x_2610_, v___x_2611_);
if (v___x_2612_ == 0)
{
lean_object* v___x_2613_; 
lean_dec(v___x_2610_);
v___x_2613_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12___redArg(v_histogram_2477_);
lean_dec_ref(v_histogram_2477_);
v___y_2567_ = v___x_2613_;
goto v___jp_2566_;
}
else
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; uint8_t v___x_2618_; 
v___x_2614_ = lean_unsigned_to_nat(4u);
v___x_2615_ = lean_nat_mul(v___x_2610_, v___x_2614_);
lean_dec(v___x_2610_);
v___x_2616_ = lean_unsigned_to_nat(3u);
v___x_2617_ = lean_nat_mul(v___x_2611_, v___x_2616_);
v___x_2618_ = lean_nat_dec_le(v___x_2615_, v___x_2617_);
lean_dec(v___x_2617_);
lean_dec(v___x_2615_);
if (v___x_2618_ == 0)
{
lean_object* v___x_2619_; 
v___x_2619_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12___redArg(v_histogram_2477_);
lean_dec_ref(v_histogram_2477_);
v___y_2567_ = v___x_2619_;
goto v___jp_2566_;
}
else
{
v___y_2567_ = v_histogram_2477_;
goto v___jp_2566_;
}
}
}
}
v___jp_2560_:
{
lean_object* v_size_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v_size_2563_ = lean_ctor_get(v___y_2561_, 0);
v___x_2564_ = lean_nat_add(v_size_2563_, v___x_2554_);
v___x_2565_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2561_, v___x_2564_, v_i_2562_, v_val_2479_, v___x_2559_);
lean_dec(v_i_2562_);
return v___x_2565_;
}
v___jp_2566_:
{
lean_object* v___x_2568_; 
v___x_2568_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11___redArg(v___y_2567_, v_val_2479_);
switch(lean_obj_tag(v___x_2568_))
{
case 0:
{
lean_object* v_index_2569_; lean_object* v_size_2570_; lean_object* v___x_2571_; 
v_index_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_index_2569_);
lean_dec_ref_known(v___x_2568_, 3);
v_size_2570_ = lean_ctor_get(v___y_2567_, 0);
lean_inc(v_size_2570_);
v___x_2571_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2567_, v_size_2570_, v_index_2569_, v_val_2479_, v___x_2559_);
lean_dec(v_index_2569_);
return v___x_2571_;
}
case 1:
{
lean_object* v_index_2572_; 
v_index_2572_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_index_2572_);
lean_dec_ref_known(v___x_2568_, 1);
v___y_2561_ = v___y_2567_;
v_i_2562_ = v_index_2572_;
goto v___jp_2560_;
}
default: 
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2573_ = lean_unsigned_to_nat(0u);
v___x_2574_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2567_, v___x_2573_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_index_2575_; 
v_index_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_index_2575_);
lean_dec_ref_known(v___x_2574_, 1);
v___y_2561_ = v___y_2567_;
v_i_2562_ = v_index_2575_;
goto v___jp_2560_;
}
else
{
lean_dec_ref(v___x_2559_);
lean_dec_ref(v_val_2479_);
return v___y_2567_;
}
}
}
}
v___jp_2576_:
{
lean_object* v_size_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
v_size_2579_ = lean_ctor_get(v___y_2577_, 0);
v___x_2580_ = lean_nat_add(v_size_2579_, v___x_2554_);
v___x_2581_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2577_, v___x_2580_, v_i_2578_, v_val_2479_, v___x_2559_);
lean_dec(v_i_2578_);
return v___x_2581_;
}
v___jp_2582_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2583_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12___redArg(v_histogram_2477_);
lean_dec_ref(v_histogram_2477_);
v___x_2584_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11___redArg(v___x_2583_, v_val_2479_);
switch(lean_obj_tag(v___x_2584_))
{
case 0:
{
lean_object* v_index_2585_; lean_object* v_size_2586_; lean_object* v___x_2587_; 
v_index_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_index_2585_);
lean_dec_ref_known(v___x_2584_, 3);
v_size_2586_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_size_2586_);
v___x_2587_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2583_, v_size_2586_, v_index_2585_, v_val_2479_, v___x_2559_);
lean_dec(v_index_2585_);
return v___x_2587_;
}
case 1:
{
lean_object* v_index_2588_; 
v_index_2588_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_index_2588_);
lean_dec_ref_known(v___x_2584_, 1);
v___y_2577_ = v___x_2583_;
v_i_2578_ = v_index_2588_;
goto v___jp_2576_;
}
default: 
{
lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2589_ = lean_unsigned_to_nat(0u);
v___x_2590_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2583_, v___x_2589_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_index_2591_; 
v_index_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_index_2591_);
lean_dec_ref_known(v___x_2590_, 1);
v___y_2577_ = v___x_2583_;
v_i_2578_ = v_index_2591_;
goto v___jp_2576_;
}
else
{
lean_dec_ref(v___x_2559_);
lean_dec_ref(v_val_2479_);
return v___x_2583_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(lean_object* v_upperBound_2625_, lean_object* v_fst_2626_, lean_object* v___x_2627_, lean_object* v_fst_2628_, lean_object* v_a_2629_, lean_object* v_b_2630_){
_start:
{
uint8_t v___x_2631_; 
v___x_2631_ = lean_nat_dec_lt(v_a_2629_, v_upperBound_2625_);
if (v___x_2631_ == 0)
{
lean_dec(v_a_2629_);
return v_b_2630_;
}
else
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2632_ = l_Subarray_get___redArg(v_fst_2628_, v_a_2629_);
lean_inc(v_a_2629_);
v___x_2633_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(v_b_2630_, v_a_2629_, v___x_2632_);
v___x_2634_ = lean_unsigned_to_nat(1u);
v___x_2635_ = lean_nat_add(v_a_2629_, v___x_2634_);
lean_dec(v_a_2629_);
v_a_2629_ = v___x_2635_;
v_b_2630_ = v___x_2633_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg___boxed(lean_object* v_upperBound_2637_, lean_object* v_fst_2638_, lean_object* v___x_2639_, lean_object* v_fst_2640_, lean_object* v_a_2641_, lean_object* v_b_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(v_upperBound_2637_, v_fst_2638_, v___x_2639_, v_fst_2640_, v_a_2641_, v_b_2642_);
lean_dec_ref(v_fst_2640_);
lean_dec(v___x_2639_);
lean_dec_ref(v_fst_2638_);
lean_dec(v_upperBound_2637_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6___redArg(lean_object* v_histogram_2644_, lean_object* v_index_2645_, lean_object* v_val_2646_){
_start:
{
lean_object* v___x_2647_; 
v___x_2647_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10___redArg(v_histogram_2644_, v_val_2646_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___y_2654_; lean_object* v_i_2655_; lean_object* v___y_2660_; lean_object* v___y_2669_; lean_object* v_i_2670_; lean_object* v___x_2683_; 
v___x_2648_ = lean_unsigned_to_nat(0u);
v___x_2649_ = lean_box(0);
v___x_2650_ = lean_unsigned_to_nat(1u);
v___x_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2651_, 0, v_index_2645_);
v___x_2652_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2648_);
lean_ctor_set(v___x_2652_, 1, v___x_2649_);
lean_ctor_set(v___x_2652_, 2, v___x_2650_);
lean_ctor_set(v___x_2652_, 3, v___x_2651_);
v___x_2683_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11___redArg(v_histogram_2644_, v_val_2646_);
switch(lean_obj_tag(v___x_2683_))
{
case 0:
{
lean_object* v_index_2684_; lean_object* v_size_2685_; lean_object* v___x_2686_; 
v_index_2684_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_index_2684_);
lean_dec_ref_known(v___x_2683_, 3);
v_size_2685_ = lean_ctor_get(v_histogram_2644_, 0);
lean_inc(v_size_2685_);
v___x_2686_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_2644_, v_size_2685_, v_index_2684_, v_val_2646_, v___x_2652_);
lean_dec(v_index_2684_);
return v___x_2686_;
}
case 1:
{
lean_object* v_index_2687_; lean_object* v_size_2688_; lean_object* v_keyArray_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; uint8_t v___x_2692_; 
v_index_2687_ = lean_ctor_get(v___x_2683_, 0);
lean_inc(v_index_2687_);
lean_dec_ref_known(v___x_2683_, 1);
v_size_2688_ = lean_ctor_get(v_histogram_2644_, 0);
v_keyArray_2689_ = lean_ctor_get(v_histogram_2644_, 1);
v___x_2690_ = lean_nat_add(v_size_2688_, v___x_2650_);
v___x_2691_ = lean_array_get_size(v_keyArray_2689_);
v___x_2692_ = lean_nat_dec_lt(v___x_2690_, v___x_2691_);
if (v___x_2692_ == 0)
{
lean_dec(v___x_2690_);
lean_dec(v_index_2687_);
goto v___jp_2674_;
}
else
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; 
v___x_2693_ = lean_unsigned_to_nat(4u);
v___x_2694_ = lean_nat_mul(v___x_2690_, v___x_2693_);
v___x_2695_ = lean_unsigned_to_nat(3u);
v___x_2696_ = lean_nat_mul(v___x_2691_, v___x_2695_);
v___x_2697_ = lean_nat_dec_le(v___x_2694_, v___x_2696_);
lean_dec(v___x_2696_);
lean_dec(v___x_2694_);
if (v___x_2697_ == 0)
{
lean_dec(v___x_2690_);
lean_dec(v_index_2687_);
goto v___jp_2674_;
}
else
{
lean_object* v___x_2698_; 
v___x_2698_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_2644_, v___x_2690_, v_index_2687_, v_val_2646_, v___x_2652_);
lean_dec(v_index_2687_);
return v___x_2698_;
}
}
}
default: 
{
lean_object* v_size_2699_; lean_object* v_keyArray_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; uint8_t v___x_2703_; 
v_size_2699_ = lean_ctor_get(v_histogram_2644_, 0);
v_keyArray_2700_ = lean_ctor_get(v_histogram_2644_, 1);
v___x_2701_ = lean_nat_add(v_size_2699_, v___x_2650_);
v___x_2702_ = lean_array_get_size(v_keyArray_2700_);
v___x_2703_ = lean_nat_dec_lt(v___x_2701_, v___x_2702_);
if (v___x_2703_ == 0)
{
lean_object* v___x_2704_; 
lean_dec(v___x_2701_);
v___x_2704_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12___redArg(v_histogram_2644_);
lean_dec_ref(v_histogram_2644_);
v___y_2660_ = v___x_2704_;
goto v___jp_2659_;
}
else
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; uint8_t v___x_2709_; 
v___x_2705_ = lean_unsigned_to_nat(4u);
v___x_2706_ = lean_nat_mul(v___x_2701_, v___x_2705_);
lean_dec(v___x_2701_);
v___x_2707_ = lean_unsigned_to_nat(3u);
v___x_2708_ = lean_nat_mul(v___x_2702_, v___x_2707_);
v___x_2709_ = lean_nat_dec_le(v___x_2706_, v___x_2708_);
lean_dec(v___x_2708_);
lean_dec(v___x_2706_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; 
v___x_2710_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12___redArg(v_histogram_2644_);
lean_dec_ref(v_histogram_2644_);
v___y_2660_ = v___x_2710_;
goto v___jp_2659_;
}
else
{
v___y_2660_ = v_histogram_2644_;
goto v___jp_2659_;
}
}
}
}
v___jp_2653_:
{
lean_object* v_size_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v_size_2656_ = lean_ctor_get(v___y_2654_, 0);
v___x_2657_ = lean_nat_add(v_size_2656_, v___x_2650_);
v___x_2658_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2654_, v___x_2657_, v_i_2655_, v_val_2646_, v___x_2652_);
lean_dec(v_i_2655_);
return v___x_2658_;
}
v___jp_2659_:
{
lean_object* v___x_2661_; 
v___x_2661_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11___redArg(v___y_2660_, v_val_2646_);
switch(lean_obj_tag(v___x_2661_))
{
case 0:
{
lean_object* v_index_2662_; lean_object* v_size_2663_; lean_object* v___x_2664_; 
v_index_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_index_2662_);
lean_dec_ref_known(v___x_2661_, 3);
v_size_2663_ = lean_ctor_get(v___y_2660_, 0);
lean_inc(v_size_2663_);
v___x_2664_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2660_, v_size_2663_, v_index_2662_, v_val_2646_, v___x_2652_);
lean_dec(v_index_2662_);
return v___x_2664_;
}
case 1:
{
lean_object* v_index_2665_; 
v_index_2665_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_index_2665_);
lean_dec_ref_known(v___x_2661_, 1);
v___y_2654_ = v___y_2660_;
v_i_2655_ = v_index_2665_;
goto v___jp_2653_;
}
default: 
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2660_, v___x_2648_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_index_2667_; 
v_index_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_index_2667_);
lean_dec_ref_known(v___x_2666_, 1);
v___y_2654_ = v___y_2660_;
v_i_2655_ = v_index_2667_;
goto v___jp_2653_;
}
else
{
lean_dec_ref_known(v___x_2652_, 4);
lean_dec_ref(v_val_2646_);
return v___y_2660_;
}
}
}
}
v___jp_2668_:
{
lean_object* v_size_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v_size_2671_ = lean_ctor_get(v___y_2669_, 0);
v___x_2672_ = lean_nat_add(v_size_2671_, v___x_2650_);
v___x_2673_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2669_, v___x_2672_, v_i_2670_, v_val_2646_, v___x_2652_);
lean_dec(v_i_2670_);
return v___x_2673_;
}
v___jp_2674_:
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2675_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12___redArg(v_histogram_2644_);
lean_dec_ref(v_histogram_2644_);
v___x_2676_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11___redArg(v___x_2675_, v_val_2646_);
switch(lean_obj_tag(v___x_2676_))
{
case 0:
{
lean_object* v_index_2677_; lean_object* v_size_2678_; lean_object* v___x_2679_; 
v_index_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_index_2677_);
lean_dec_ref_known(v___x_2676_, 3);
v_size_2678_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_size_2678_);
v___x_2679_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2675_, v_size_2678_, v_index_2677_, v_val_2646_, v___x_2652_);
lean_dec(v_index_2677_);
return v___x_2679_;
}
case 1:
{
lean_object* v_index_2680_; 
v_index_2680_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_index_2680_);
lean_dec_ref_known(v___x_2676_, 1);
v___y_2669_ = v___x_2675_;
v_i_2670_ = v_index_2680_;
goto v___jp_2668_;
}
default: 
{
lean_object* v___x_2681_; 
v___x_2681_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2675_, v___x_2648_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_index_2682_; 
v_index_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_index_2682_);
lean_dec_ref_known(v___x_2681_, 1);
v___y_2669_ = v___x_2675_;
v_i_2670_ = v_index_2682_;
goto v___jp_2668_;
}
else
{
lean_dec_ref_known(v___x_2652_, 4);
lean_dec_ref(v_val_2646_);
return v___x_2675_;
}
}
}
}
}
else
{
lean_object* v_val_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2791_; 
v_val_2711_ = lean_ctor_get(v___x_2647_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2647_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2713_ = v___x_2647_;
v_isShared_2714_ = v_isSharedCheck_2791_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_val_2711_);
lean_dec(v___x_2647_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2791_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v_leftCount_2715_; lean_object* v_leftIndex_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2788_; 
v_leftCount_2715_ = lean_ctor_get(v_val_2711_, 0);
v_leftIndex_2716_ = lean_ctor_get(v_val_2711_, 1);
v_isSharedCheck_2788_ = !lean_is_exclusive(v_val_2711_);
if (v_isSharedCheck_2788_ == 0)
{
lean_object* v_unused_2789_; lean_object* v_unused_2790_; 
v_unused_2789_ = lean_ctor_get(v_val_2711_, 3);
lean_dec(v_unused_2789_);
v_unused_2790_ = lean_ctor_get(v_val_2711_, 2);
lean_dec(v_unused_2790_);
v___x_2718_ = v_val_2711_;
v_isShared_2719_ = v_isSharedCheck_2788_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_leftIndex_2716_);
lean_inc(v_leftCount_2715_);
lean_dec(v_val_2711_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2788_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2723_; 
v___x_2720_ = lean_unsigned_to_nat(1u);
v___x_2721_ = lean_nat_add(v_leftCount_2715_, v___x_2720_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 0, v_index_2645_);
v___x_2723_ = v___x_2713_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_index_2645_);
v___x_2723_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
lean_object* v___x_2725_; 
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 3, v___x_2723_);
lean_ctor_set(v___x_2718_, 2, v___x_2721_);
v___x_2725_ = v___x_2718_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_leftCount_2715_);
lean_ctor_set(v_reuseFailAlloc_2786_, 1, v_leftIndex_2716_);
lean_ctor_set(v_reuseFailAlloc_2786_, 2, v___x_2721_);
lean_ctor_set(v_reuseFailAlloc_2786_, 3, v___x_2723_);
v___x_2725_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
lean_object* v___y_2727_; lean_object* v_i_2728_; lean_object* v___y_2733_; lean_object* v___y_2743_; lean_object* v_i_2744_; lean_object* v___x_2758_; 
v___x_2758_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11___redArg(v_histogram_2644_, v_val_2646_);
switch(lean_obj_tag(v___x_2758_))
{
case 0:
{
lean_object* v_index_2759_; lean_object* v_size_2760_; lean_object* v___x_2761_; 
v_index_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_index_2759_);
lean_dec_ref_known(v___x_2758_, 3);
v_size_2760_ = lean_ctor_get(v_histogram_2644_, 0);
lean_inc(v_size_2760_);
v___x_2761_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_2644_, v_size_2760_, v_index_2759_, v_val_2646_, v___x_2725_);
lean_dec(v_index_2759_);
return v___x_2761_;
}
case 1:
{
lean_object* v_index_2762_; lean_object* v_size_2763_; lean_object* v_keyArray_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; uint8_t v___x_2767_; 
v_index_2762_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_index_2762_);
lean_dec_ref_known(v___x_2758_, 1);
v_size_2763_ = lean_ctor_get(v_histogram_2644_, 0);
v_keyArray_2764_ = lean_ctor_get(v_histogram_2644_, 1);
v___x_2765_ = lean_nat_add(v_size_2763_, v___x_2720_);
v___x_2766_ = lean_array_get_size(v_keyArray_2764_);
v___x_2767_ = lean_nat_dec_lt(v___x_2765_, v___x_2766_);
if (v___x_2767_ == 0)
{
lean_dec(v___x_2765_);
lean_dec(v_index_2762_);
goto v___jp_2748_;
}
else
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; uint8_t v___x_2772_; 
v___x_2768_ = lean_unsigned_to_nat(4u);
v___x_2769_ = lean_nat_mul(v___x_2765_, v___x_2768_);
v___x_2770_ = lean_unsigned_to_nat(3u);
v___x_2771_ = lean_nat_mul(v___x_2766_, v___x_2770_);
v___x_2772_ = lean_nat_dec_le(v___x_2769_, v___x_2771_);
lean_dec(v___x_2771_);
lean_dec(v___x_2769_);
if (v___x_2772_ == 0)
{
lean_dec(v___x_2765_);
lean_dec(v_index_2762_);
goto v___jp_2748_;
}
else
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Std_DHashMap_Raw_setEntry___redArg(v_histogram_2644_, v___x_2765_, v_index_2762_, v_val_2646_, v___x_2725_);
lean_dec(v_index_2762_);
return v___x_2773_;
}
}
}
default: 
{
lean_object* v_size_2774_; lean_object* v_keyArray_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; uint8_t v___x_2778_; 
v_size_2774_ = lean_ctor_get(v_histogram_2644_, 0);
v_keyArray_2775_ = lean_ctor_get(v_histogram_2644_, 1);
v___x_2776_ = lean_nat_add(v_size_2774_, v___x_2720_);
v___x_2777_ = lean_array_get_size(v_keyArray_2775_);
v___x_2778_ = lean_nat_dec_lt(v___x_2776_, v___x_2777_);
if (v___x_2778_ == 0)
{
lean_object* v___x_2779_; 
lean_dec(v___x_2776_);
v___x_2779_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12___redArg(v_histogram_2644_);
lean_dec_ref(v_histogram_2644_);
v___y_2733_ = v___x_2779_;
goto v___jp_2732_;
}
else
{
lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
v___x_2780_ = lean_unsigned_to_nat(4u);
v___x_2781_ = lean_nat_mul(v___x_2776_, v___x_2780_);
lean_dec(v___x_2776_);
v___x_2782_ = lean_unsigned_to_nat(3u);
v___x_2783_ = lean_nat_mul(v___x_2777_, v___x_2782_);
v___x_2784_ = lean_nat_dec_le(v___x_2781_, v___x_2783_);
lean_dec(v___x_2783_);
lean_dec(v___x_2781_);
if (v___x_2784_ == 0)
{
lean_object* v___x_2785_; 
v___x_2785_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12___redArg(v_histogram_2644_);
lean_dec_ref(v_histogram_2644_);
v___y_2733_ = v___x_2785_;
goto v___jp_2732_;
}
else
{
v___y_2733_ = v_histogram_2644_;
goto v___jp_2732_;
}
}
}
}
v___jp_2726_:
{
lean_object* v_size_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v_size_2729_ = lean_ctor_get(v___y_2727_, 0);
v___x_2730_ = lean_nat_add(v_size_2729_, v___x_2720_);
v___x_2731_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2727_, v___x_2730_, v_i_2728_, v_val_2646_, v___x_2725_);
lean_dec(v_i_2728_);
return v___x_2731_;
}
v___jp_2732_:
{
lean_object* v___x_2734_; 
v___x_2734_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11___redArg(v___y_2733_, v_val_2646_);
switch(lean_obj_tag(v___x_2734_))
{
case 0:
{
lean_object* v_index_2735_; lean_object* v_size_2736_; lean_object* v___x_2737_; 
v_index_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_index_2735_);
lean_dec_ref_known(v___x_2734_, 3);
v_size_2736_ = lean_ctor_get(v___y_2733_, 0);
lean_inc(v_size_2736_);
v___x_2737_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2733_, v_size_2736_, v_index_2735_, v_val_2646_, v___x_2725_);
lean_dec(v_index_2735_);
return v___x_2737_;
}
case 1:
{
lean_object* v_index_2738_; 
v_index_2738_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_index_2738_);
lean_dec_ref_known(v___x_2734_, 1);
v___y_2727_ = v___y_2733_;
v_i_2728_ = v_index_2738_;
goto v___jp_2726_;
}
default: 
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2739_ = lean_unsigned_to_nat(0u);
v___x_2740_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2733_, v___x_2739_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_index_2741_; 
v_index_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_index_2741_);
lean_dec_ref_known(v___x_2740_, 1);
v___y_2727_ = v___y_2733_;
v_i_2728_ = v_index_2741_;
goto v___jp_2726_;
}
else
{
lean_dec_ref(v___x_2725_);
lean_dec_ref(v_val_2646_);
return v___y_2733_;
}
}
}
}
v___jp_2742_:
{
lean_object* v_size_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
v_size_2745_ = lean_ctor_get(v___y_2743_, 0);
v___x_2746_ = lean_nat_add(v_size_2745_, v___x_2720_);
v___x_2747_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2743_, v___x_2746_, v_i_2744_, v_val_2646_, v___x_2725_);
lean_dec(v_i_2744_);
return v___x_2747_;
}
v___jp_2748_:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12___redArg(v_histogram_2644_);
lean_dec_ref(v_histogram_2644_);
v___x_2750_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11___redArg(v___x_2749_, v_val_2646_);
switch(lean_obj_tag(v___x_2750_))
{
case 0:
{
lean_object* v_index_2751_; lean_object* v_size_2752_; lean_object* v___x_2753_; 
v_index_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_index_2751_);
lean_dec_ref_known(v___x_2750_, 3);
v_size_2752_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_size_2752_);
v___x_2753_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2749_, v_size_2752_, v_index_2751_, v_val_2646_, v___x_2725_);
lean_dec(v_index_2751_);
return v___x_2753_;
}
case 1:
{
lean_object* v_index_2754_; 
v_index_2754_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_index_2754_);
lean_dec_ref_known(v___x_2750_, 1);
v___y_2743_ = v___x_2749_;
v_i_2744_ = v_index_2754_;
goto v___jp_2742_;
}
default: 
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = lean_unsigned_to_nat(0u);
v___x_2756_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2749_, v___x_2755_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_index_2757_; 
v_index_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_index_2757_);
lean_dec_ref_known(v___x_2756_, 1);
v___y_2743_ = v___x_2749_;
v_i_2744_ = v_index_2757_;
goto v___jp_2742_;
}
else
{
lean_dec_ref(v___x_2725_);
lean_dec_ref(v_val_2646_);
return v___x_2749_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(lean_object* v_upperBound_2792_, lean_object* v___x_2793_, lean_object* v_fst_2794_, lean_object* v___x_2795_, lean_object* v_a_2796_, lean_object* v_b_2797_){
_start:
{
uint8_t v___x_2798_; 
v___x_2798_ = lean_nat_dec_lt(v_a_2796_, v_upperBound_2792_);
if (v___x_2798_ == 0)
{
lean_dec(v_a_2796_);
return v_b_2797_;
}
else
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2799_ = l_Subarray_get___redArg(v_fst_2794_, v_a_2796_);
lean_inc(v_a_2796_);
v___x_2800_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6___redArg(v_b_2797_, v_a_2796_, v___x_2799_);
v___x_2801_ = lean_unsigned_to_nat(1u);
v___x_2802_ = lean_nat_add(v_a_2796_, v___x_2801_);
lean_dec(v_a_2796_);
v_a_2796_ = v___x_2802_;
v_b_2797_ = v___x_2800_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg___boxed(lean_object* v_upperBound_2804_, lean_object* v___x_2805_, lean_object* v_fst_2806_, lean_object* v___x_2807_, lean_object* v_a_2808_, lean_object* v_b_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(v_upperBound_2804_, v___x_2805_, v_fst_2806_, v___x_2807_, v_a_2808_, v_b_2809_);
lean_dec(v___x_2807_);
lean_dec_ref(v_fst_2806_);
lean_dec(v___x_2805_);
lean_dec(v_upperBound_2804_);
return v_res_2810_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5___redArg(lean_object* v_as_x27_2811_, lean_object* v_b_2812_){
_start:
{
if (lean_obj_tag(v_as_x27_2811_) == 0)
{
return v_b_2812_;
}
else
{
lean_object* v_head_2813_; lean_object* v_snd_2814_; lean_object* v_leftIndex_2815_; 
v_head_2813_ = lean_ctor_get(v_as_x27_2811_, 0);
v_snd_2814_ = lean_ctor_get(v_head_2813_, 1);
v_leftIndex_2815_ = lean_ctor_get(v_snd_2814_, 1);
if (lean_obj_tag(v_leftIndex_2815_) == 1)
{
lean_object* v_rightIndex_2816_; 
v_rightIndex_2816_ = lean_ctor_get(v_snd_2814_, 3);
if (lean_obj_tag(v_rightIndex_2816_) == 1)
{
if (lean_obj_tag(v_b_2812_) == 0)
{
lean_object* v_tail_2817_; lean_object* v_fst_2818_; lean_object* v_leftCount_2819_; lean_object* v_rightCount_2820_; lean_object* v_val_2821_; lean_object* v_val_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v_tail_2817_ = lean_ctor_get(v_as_x27_2811_, 1);
v_fst_2818_ = lean_ctor_get(v_head_2813_, 0);
v_leftCount_2819_ = lean_ctor_get(v_snd_2814_, 0);
v_rightCount_2820_ = lean_ctor_get(v_snd_2814_, 2);
v_val_2821_ = lean_ctor_get(v_leftIndex_2815_, 0);
v_val_2822_ = lean_ctor_get(v_rightIndex_2816_, 0);
v___x_2823_ = lean_nat_add(v_leftCount_2819_, v_rightCount_2820_);
lean_inc(v_val_2822_);
lean_inc(v_val_2821_);
v___x_2824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2824_, 0, v_val_2821_);
lean_ctor_set(v___x_2824_, 1, v_val_2822_);
lean_inc(v_fst_2818_);
v___x_2825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2825_, 0, v_fst_2818_);
lean_ctor_set(v___x_2825_, 1, v___x_2824_);
v___x_2826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2823_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
v___x_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2826_);
v_as_x27_2811_ = v_tail_2817_;
v_b_2812_ = v___x_2827_;
goto _start;
}
else
{
lean_object* v_val_2829_; lean_object* v_tail_2830_; lean_object* v_fst_2831_; lean_object* v_leftCount_2832_; lean_object* v_rightCount_2833_; lean_object* v_val_2834_; lean_object* v_val_2835_; lean_object* v_fst_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2857_; 
v_val_2829_ = lean_ctor_get(v_b_2812_, 0);
lean_inc(v_val_2829_);
v_tail_2830_ = lean_ctor_get(v_as_x27_2811_, 1);
v_fst_2831_ = lean_ctor_get(v_head_2813_, 0);
v_leftCount_2832_ = lean_ctor_get(v_snd_2814_, 0);
v_rightCount_2833_ = lean_ctor_get(v_snd_2814_, 2);
v_val_2834_ = lean_ctor_get(v_leftIndex_2815_, 0);
v_val_2835_ = lean_ctor_get(v_rightIndex_2816_, 0);
v_fst_2836_ = lean_ctor_get(v_val_2829_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v_val_2829_);
if (v_isSharedCheck_2857_ == 0)
{
lean_object* v_unused_2858_; 
v_unused_2858_ = lean_ctor_get(v_val_2829_, 1);
lean_dec(v_unused_2858_);
v___x_2838_ = v_val_2829_;
v_isShared_2839_ = v_isSharedCheck_2857_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_fst_2836_);
lean_dec(v_val_2829_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2857_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2840_; uint8_t v___x_2841_; 
v___x_2840_ = lean_nat_add(v_leftCount_2832_, v_rightCount_2833_);
v___x_2841_ = lean_nat_dec_lt(v___x_2840_, v_fst_2836_);
lean_dec(v_fst_2836_);
if (v___x_2841_ == 0)
{
lean_dec(v___x_2840_);
lean_del_object(v___x_2838_);
v_as_x27_2811_ = v_tail_2830_;
goto _start;
}
else
{
lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2855_; 
v_isSharedCheck_2855_ = !lean_is_exclusive(v_b_2812_);
if (v_isSharedCheck_2855_ == 0)
{
lean_object* v_unused_2856_; 
v_unused_2856_ = lean_ctor_get(v_b_2812_, 0);
lean_dec(v_unused_2856_);
v___x_2844_ = v_b_2812_;
v_isShared_2845_ = v_isSharedCheck_2855_;
goto v_resetjp_2843_;
}
else
{
lean_dec(v_b_2812_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2855_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
lean_inc(v_val_2835_);
lean_inc(v_val_2834_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 1, v_val_2835_);
lean_ctor_set(v___x_2838_, 0, v_val_2834_);
v___x_2847_ = v___x_2838_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_val_2834_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_val_2835_);
v___x_2847_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2851_; 
lean_inc(v_fst_2831_);
v___x_2848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2848_, 0, v_fst_2831_);
lean_ctor_set(v___x_2848_, 1, v___x_2847_);
v___x_2849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2840_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v___x_2849_);
v___x_2851_ = v___x_2844_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2849_);
v___x_2851_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
v_as_x27_2811_ = v_tail_2830_;
v_b_2812_ = v___x_2851_;
goto _start;
}
}
}
}
}
}
}
else
{
lean_object* v_tail_2859_; 
v_tail_2859_ = lean_ctor_get(v_as_x27_2811_, 1);
v_as_x27_2811_ = v_tail_2859_;
goto _start;
}
}
else
{
lean_object* v_tail_2861_; 
v_tail_2861_ = lean_ctor_get(v_as_x27_2811_, 1);
v_as_x27_2811_ = v_tail_2861_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5___redArg___boxed(lean_object* v_as_x27_2863_, lean_object* v_b_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5___redArg(v_as_x27_2863_, v_b_2864_);
lean_dec(v_as_x27_2863_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4(lean_object* v_b_2866_, lean_object* v_acc_2867_, lean_object* v_i_2868_){
_start:
{
lean_object* v_keyArray_2873_; lean_object* v_valueArray_2874_; lean_object* v___x_2875_; uint8_t v___x_2876_; 
v_keyArray_2873_ = lean_ctor_get(v_b_2866_, 1);
v_valueArray_2874_ = lean_ctor_get(v_b_2866_, 2);
v___x_2875_ = lean_array_get_size(v_keyArray_2873_);
v___x_2876_ = lean_nat_dec_lt(v_i_2868_, v___x_2875_);
if (v___x_2876_ == 0)
{
lean_dec(v_i_2868_);
lean_inc(v_acc_2867_);
return v_acc_2867_;
}
else
{
lean_object* v___x_2877_; uint8_t v_isSome_2878_; 
v___x_2877_ = lean_array_fget_borrowed(v_keyArray_2873_, v_i_2868_);
v_isSome_2878_ = lean_noption_is_some(v___x_2877_);
if (v_isSome_2878_ == 0)
{
goto v___jp_2869_;
}
else
{
lean_object* v___x_2879_; uint8_t v_isSome_2880_; 
v___x_2879_ = lean_array_fget_borrowed(v_valueArray_2874_, v_i_2868_);
v_isSome_2880_ = lean_noption_is_some(v___x_2879_);
if (v_isSome_2880_ == 0)
{
goto v___jp_2869_;
}
else
{
lean_object* v_val_2881_; lean_object* v_val_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
lean_inc(v___x_2877_);
v_val_2881_ = lean_noption_get(v___x_2877_);
lean_inc(v___x_2879_);
v_val_2882_ = lean_noption_get(v___x_2879_);
v___x_2883_ = lean_unsigned_to_nat(1u);
v___x_2884_ = lean_nat_add(v_i_2868_, v___x_2883_);
lean_dec(v_i_2868_);
v___x_2885_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4(v_b_2866_, v_acc_2867_, v___x_2884_);
v___x_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2886_, 0, v_val_2881_);
lean_ctor_set(v___x_2886_, 1, v_val_2882_);
v___x_2887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
lean_ctor_set(v___x_2887_, 1, v___x_2885_);
return v___x_2887_;
}
}
}
v___jp_2869_:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
v___x_2870_ = lean_unsigned_to_nat(1u);
v___x_2871_ = lean_nat_add(v_i_2868_, v___x_2870_);
lean_dec(v_i_2868_);
v_i_2868_ = v___x_2871_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___boxed(lean_object* v_b_2888_, lean_object* v_acc_2889_, lean_object* v_i_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4(v_b_2888_, v_acc_2889_, v_i_2890_);
lean_dec(v_acc_2889_);
lean_dec_ref(v_b_2888_);
return v_res_2891_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v_cellCount_2892_; lean_object* v___x_2893_; 
v_cellCount_2892_ = lean_unsigned_to_nat(16u);
v___x_2893_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_2892_);
return v___x_2893_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1(void){
_start:
{
lean_object* v_cellCount_2894_; lean_object* v___x_2895_; 
v_cellCount_2894_ = lean_unsigned_to_nat(16u);
v___x_2895_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2894_);
return v___x_2895_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__2(void){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v_hist_2899_; 
v___x_2896_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1);
v___x_2897_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0);
v___x_2898_ = lean_unsigned_to_nat(0u);
v_hist_2899_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_hist_2899_, 0, v___x_2898_);
lean_ctor_set(v_hist_2899_, 1, v___x_2897_);
lean_ctor_set(v_hist_2899_, 2, v___x_2896_);
return v_hist_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(lean_object* v_left_2900_, lean_object* v_right_2901_){
_start:
{
lean_object* v___x_2902_; lean_object* v_snd_2903_; lean_object* v_fst_2904_; lean_object* v_fst_2905_; lean_object* v_snd_2906_; lean_object* v___x_2907_; lean_object* v_snd_2908_; lean_object* v_fst_2909_; lean_object* v_fst_2910_; lean_object* v_snd_2911_; lean_object* v_start_2912_; lean_object* v_stop_2913_; lean_object* v___x_2914_; lean_object* v_hist_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v_start_2918_; lean_object* v_stop_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2902_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2(v_left_2900_, v_right_2901_);
v_snd_2903_ = lean_ctor_get(v___x_2902_, 1);
lean_inc(v_snd_2903_);
v_fst_2904_ = lean_ctor_get(v___x_2902_, 0);
lean_inc(v_fst_2904_);
lean_dec_ref(v___x_2902_);
v_fst_2905_ = lean_ctor_get(v_snd_2903_, 0);
lean_inc(v_fst_2905_);
v_snd_2906_ = lean_ctor_get(v_snd_2903_, 1);
lean_inc(v_snd_2906_);
lean_dec(v_snd_2903_);
v___x_2907_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3(v_fst_2905_, v_snd_2906_);
v_snd_2908_ = lean_ctor_get(v___x_2907_, 1);
lean_inc(v_snd_2908_);
v_fst_2909_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_fst_2909_);
lean_dec_ref(v___x_2907_);
v_fst_2910_ = lean_ctor_get(v_snd_2908_, 0);
lean_inc(v_fst_2910_);
v_snd_2911_ = lean_ctor_get(v_snd_2908_, 1);
lean_inc(v_snd_2911_);
lean_dec(v_snd_2908_);
v_start_2912_ = lean_ctor_get(v_fst_2909_, 1);
v_stop_2913_ = lean_ctor_get(v_fst_2909_, 2);
v___x_2914_ = lean_unsigned_to_nat(0u);
v_hist_2915_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__2, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__2_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__2);
v___x_2916_ = lean_nat_sub(v_stop_2913_, v_start_2912_);
v___x_2917_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(v___x_2916_, v_fst_2910_, v___x_2916_, v_fst_2909_, v___x_2914_, v_hist_2915_);
v_start_2918_ = lean_ctor_get(v_fst_2910_, 1);
v_stop_2919_ = lean_ctor_get(v_fst_2910_, 2);
v___x_2920_ = lean_nat_sub(v_stop_2919_, v_start_2918_);
v___x_2921_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(v___x_2920_, v___x_2920_, v_fst_2910_, v___x_2916_, v___x_2914_, v___x_2917_);
lean_dec(v___x_2916_);
lean_dec(v___x_2920_);
v___x_2922_ = lean_box(0);
v___x_2923_ = lean_box(0);
v___x_2924_ = l_Std_DHashMap_Raw_foldRevMFrom___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4(v___x_2921_, v___x_2923_, v___x_2914_);
lean_dec_ref(v___x_2921_);
v___x_2925_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5___redArg(v___x_2924_, v___x_2922_);
lean_dec(v___x_2924_);
if (lean_obj_tag(v___x_2925_) == 1)
{
lean_object* v_val_2926_; lean_object* v_snd_2927_; lean_object* v_snd_2928_; lean_object* v_fst_2929_; lean_object* v_fst_2930_; lean_object* v_snd_2931_; lean_object* v___x_2932_; lean_object* v_fst_2933_; lean_object* v_snd_2934_; lean_object* v___x_2935_; lean_object* v_fst_2936_; lean_object* v_snd_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; 
v_val_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_val_2926_);
lean_dec_ref_known(v___x_2925_, 1);
v_snd_2927_ = lean_ctor_get(v_val_2926_, 1);
lean_inc(v_snd_2927_);
lean_dec(v_val_2926_);
v_snd_2928_ = lean_ctor_get(v_snd_2927_, 1);
lean_inc(v_snd_2928_);
v_fst_2929_ = lean_ctor_get(v_snd_2927_, 0);
lean_inc(v_fst_2929_);
lean_dec(v_snd_2927_);
v_fst_2930_ = lean_ctor_get(v_snd_2928_, 0);
lean_inc(v_fst_2930_);
v_snd_2931_ = lean_ctor_get(v_snd_2928_, 1);
lean_inc(v_snd_2931_);
lean_dec(v_snd_2928_);
v___x_2932_ = l_Subarray_split___redArg(v_fst_2909_, v_fst_2930_);
lean_dec(v_fst_2930_);
v_fst_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_fst_2933_);
v_snd_2934_ = lean_ctor_get(v___x_2932_, 1);
lean_inc(v_snd_2934_);
lean_dec_ref(v___x_2932_);
v___x_2935_ = l_Subarray_split___redArg(v_fst_2910_, v_snd_2931_);
lean_dec(v_snd_2931_);
v_fst_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc(v_fst_2936_);
v_snd_2937_ = lean_ctor_get(v___x_2935_, 1);
lean_inc(v_snd_2937_);
lean_dec_ref(v___x_2935_);
v___x_2938_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v_fst_2933_, v_fst_2936_);
v___x_2939_ = l_Array_append___redArg(v_fst_2904_, v___x_2938_);
lean_dec_ref(v___x_2938_);
v___x_2940_ = lean_unsigned_to_nat(1u);
v___x_2941_ = lean_mk_empty_array_with_capacity(v___x_2940_);
v___x_2942_ = lean_array_push(v___x_2941_, v_fst_2929_);
v___x_2943_ = l_Array_append___redArg(v___x_2939_, v___x_2942_);
lean_dec_ref(v___x_2942_);
v___x_2944_ = l_Subarray_drop___redArg(v_snd_2934_, v___x_2940_);
v___x_2945_ = l_Subarray_drop___redArg(v_snd_2937_, v___x_2940_);
v___x_2946_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v___x_2944_, v___x_2945_);
v___x_2947_ = l_Array_append___redArg(v___x_2943_, v___x_2946_);
lean_dec_ref(v___x_2946_);
v___x_2948_ = l_Array_append___redArg(v___x_2947_, v_snd_2911_);
lean_dec(v_snd_2911_);
return v___x_2948_;
}
else
{
lean_object* v___x_2949_; 
lean_dec(v___x_2925_);
lean_dec(v_fst_2910_);
lean_dec(v_fst_2909_);
v___x_2949_ = l_Array_append___redArg(v_fst_2904_, v_snd_2911_);
lean_dec(v_snd_2911_);
return v___x_2949_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(size_t v_sz_2950_, size_t v_i_2951_, lean_object* v_bs_2952_){
_start:
{
uint8_t v___x_2953_; 
v___x_2953_ = lean_usize_dec_lt(v_i_2951_, v_sz_2950_);
if (v___x_2953_ == 0)
{
return v_bs_2952_;
}
else
{
lean_object* v_v_2954_; lean_object* v___x_2955_; lean_object* v_bs_x27_2956_; uint8_t v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; size_t v___x_2960_; size_t v___x_2961_; lean_object* v___x_2962_; 
v_v_2954_ = lean_array_uget(v_bs_2952_, v_i_2951_);
v___x_2955_ = lean_unsigned_to_nat(0u);
v_bs_x27_2956_ = lean_array_uset(v_bs_2952_, v_i_2951_, v___x_2955_);
v___x_2957_ = 1;
v___x_2958_ = lean_box(v___x_2957_);
v___x_2959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2959_, 0, v___x_2958_);
lean_ctor_set(v___x_2959_, 1, v_v_2954_);
v___x_2960_ = ((size_t)1ULL);
v___x_2961_ = lean_usize_add(v_i_2951_, v___x_2960_);
v___x_2962_ = lean_array_uset(v_bs_x27_2956_, v_i_2951_, v___x_2959_);
v_i_2951_ = v___x_2961_;
v_bs_2952_ = v___x_2962_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7___boxed(lean_object* v_sz_2964_, lean_object* v_i_2965_, lean_object* v_bs_2966_){
_start:
{
size_t v_sz_boxed_2967_; size_t v_i_boxed_2968_; lean_object* v_res_2969_; 
v_sz_boxed_2967_ = lean_unbox_usize(v_sz_2964_);
lean_dec(v_sz_2964_);
v_i_boxed_2968_ = lean_unbox_usize(v_i_2965_);
lean_dec(v_i_2965_);
v_res_2969_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_boxed_2967_, v_i_boxed_2968_, v_bs_2966_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(lean_object* v_original_2975_, lean_object* v_edited_2976_){
_start:
{
lean_object* v_i_2977_; lean_object* v___x_2978_; uint8_t v___x_2979_; 
v_i_2977_ = lean_unsigned_to_nat(0u);
v___x_2978_ = lean_array_get_size(v_original_2975_);
v___x_2979_ = lean_nat_dec_lt(v_i_2977_, v___x_2978_);
if (v___x_2979_ == 0)
{
size_t v_sz_2980_; size_t v___x_2981_; lean_object* v___x_2982_; 
lean_dec_ref(v_original_2975_);
v_sz_2980_ = lean_array_size(v_edited_2976_);
v___x_2981_ = ((size_t)0ULL);
v___x_2982_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_2980_, v___x_2981_, v_edited_2976_);
return v___x_2982_;
}
else
{
lean_object* v___x_2983_; uint8_t v___x_2984_; 
v___x_2983_ = lean_array_get_size(v_edited_2976_);
v___x_2984_ = lean_nat_dec_lt(v_i_2977_, v___x_2983_);
if (v___x_2984_ == 0)
{
size_t v_sz_2985_; size_t v___x_2986_; lean_object* v___x_2987_; 
lean_dec_ref(v_edited_2976_);
v_sz_2985_ = lean_array_size(v_original_2975_);
v___x_2986_ = ((size_t)0ULL);
v___x_2987_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_2985_, v___x_2986_, v_original_2975_);
return v___x_2987_;
}
else
{
lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v_ds_2990_; lean_object* v___x_2991_; size_t v_sz_2992_; size_t v___x_2993_; lean_object* v___x_2994_; lean_object* v_snd_2995_; lean_object* v_fst_2996_; lean_object* v_fst_2997_; lean_object* v_snd_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3017_; 
lean_inc_ref(v_original_2975_);
v___x_2988_ = l_Array_toSubarray___redArg(v_original_2975_, v_i_2977_, v___x_2978_);
lean_inc_ref(v_edited_2976_);
v___x_2989_ = l_Array_toSubarray___redArg(v_edited_2976_, v_i_2977_, v___x_2983_);
v_ds_2990_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v___x_2988_, v___x_2989_);
v___x_2991_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__1));
v_sz_2992_ = lean_array_size(v_ds_2990_);
v___x_2993_ = ((size_t)0ULL);
v___x_2994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v_edited_2976_, v___x_2983_, v_original_2975_, v___x_2978_, v_ds_2990_, v_sz_2992_, v___x_2993_, v___x_2991_);
lean_dec_ref(v_ds_2990_);
v_snd_2995_ = lean_ctor_get(v___x_2994_, 1);
lean_inc(v_snd_2995_);
v_fst_2996_ = lean_ctor_get(v___x_2994_, 0);
lean_inc(v_fst_2996_);
lean_dec_ref(v___x_2994_);
v_fst_2997_ = lean_ctor_get(v_snd_2995_, 0);
v_snd_2998_ = lean_ctor_get(v_snd_2995_, 1);
v_isSharedCheck_3017_ = !lean_is_exclusive(v_snd_2995_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3000_ = v_snd_2995_;
v_isShared_3001_ = v_isSharedCheck_3017_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_snd_2998_);
lean_inc(v_fst_2997_);
lean_dec(v_snd_2995_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3017_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 1, v_fst_2997_);
lean_ctor_set(v___x_3000_, 0, v_fst_2996_);
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_fst_2996_);
lean_ctor_set(v_reuseFailAlloc_3016_, 1, v_fst_2997_);
v___x_3003_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
lean_object* v___x_3004_; lean_object* v_fst_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3014_; 
v___x_3004_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2978_, v_original_2975_, v___x_3003_);
lean_dec_ref(v_original_2975_);
v_fst_3005_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3014_ == 0)
{
lean_object* v_unused_3015_; 
v_unused_3015_ = lean_ctor_get(v___x_3004_, 1);
lean_dec(v_unused_3015_);
v___x_3007_ = v___x_3004_;
v_isShared_3008_ = v_isSharedCheck_3014_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_fst_3005_);
lean_dec(v___x_3004_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3014_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
lean_ctor_set(v___x_3007_, 1, v_snd_2998_);
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_fst_3005_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_snd_2998_);
v___x_3010_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
lean_object* v___x_3011_; lean_object* v_fst_3012_; 
v___x_3011_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2983_, v_edited_2976_, v___x_3010_);
lean_dec_ref(v_edited_2976_);
v_fst_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_fst_3012_);
lean_dec_ref(v___x_3011_);
return v_fst_3012_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(size_t v_sz_3018_, size_t v_i_3019_, lean_object* v_bs_3020_){
_start:
{
uint8_t v___x_3021_; 
v___x_3021_ = lean_usize_dec_lt(v_i_3019_, v_sz_3018_);
if (v___x_3021_ == 0)
{
return v_bs_3020_;
}
else
{
lean_object* v_v_3022_; lean_object* v_fst_3023_; lean_object* v_snd_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3058_; 
v_v_3022_ = lean_array_uget(v_bs_3020_, v_i_3019_);
v_fst_3023_ = lean_ctor_get(v_v_3022_, 0);
v_snd_3024_ = lean_ctor_get(v_v_3022_, 1);
v_isSharedCheck_3058_ = !lean_is_exclusive(v_v_3022_);
if (v_isSharedCheck_3058_ == 0)
{
v___x_3026_ = v_v_3022_;
v_isShared_3027_ = v_isSharedCheck_3058_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_snd_3024_);
lean_inc(v_fst_3023_);
lean_dec(v_v_3022_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3058_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3028_; lean_object* v_bs_x27_3029_; lean_object* v___y_3031_; lean_object* v___x_3036_; lean_object* v___x_3037_; uint8_t v___x_3038_; 
v___x_3028_ = lean_unsigned_to_nat(0u);
v_bs_x27_3029_ = lean_array_uset(v_bs_3020_, v_i_3019_, v___x_3028_);
v___x_3036_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_3037_ = lean_array_get_size(v_snd_3024_);
v___x_3038_ = lean_nat_dec_lt(v___x_3028_, v___x_3037_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3040_; 
lean_dec(v_snd_3024_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 1, v___x_3036_);
v___x_3040_ = v___x_3026_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_fst_3023_);
lean_ctor_set(v_reuseFailAlloc_3041_, 1, v___x_3036_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
v___y_3031_ = v___x_3040_;
goto v___jp_3030_;
}
}
else
{
uint8_t v___x_3042_; 
v___x_3042_ = lean_nat_dec_le(v___x_3037_, v___x_3037_);
if (v___x_3042_ == 0)
{
if (v___x_3038_ == 0)
{
lean_object* v___x_3044_; 
lean_dec(v_snd_3024_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 1, v___x_3036_);
v___x_3044_ = v___x_3026_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_fst_3023_);
lean_ctor_set(v_reuseFailAlloc_3045_, 1, v___x_3036_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
v___y_3031_ = v___x_3044_;
goto v___jp_3030_;
}
}
else
{
size_t v___x_3046_; size_t v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3050_; 
v___x_3046_ = ((size_t)0ULL);
v___x_3047_ = lean_usize_of_nat(v___x_3037_);
v___x_3048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_3024_, v___x_3046_, v___x_3047_, v___x_3036_);
lean_dec(v_snd_3024_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 1, v___x_3048_);
v___x_3050_ = v___x_3026_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_fst_3023_);
lean_ctor_set(v_reuseFailAlloc_3051_, 1, v___x_3048_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
v___y_3031_ = v___x_3050_;
goto v___jp_3030_;
}
}
}
else
{
size_t v___x_3052_; size_t v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3056_; 
v___x_3052_ = ((size_t)0ULL);
v___x_3053_ = lean_usize_of_nat(v___x_3037_);
v___x_3054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_3024_, v___x_3052_, v___x_3053_, v___x_3036_);
lean_dec(v_snd_3024_);
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 1, v___x_3054_);
v___x_3056_ = v___x_3026_;
goto v_reusejp_3055_;
}
else
{
lean_object* v_reuseFailAlloc_3057_; 
v_reuseFailAlloc_3057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3057_, 0, v_fst_3023_);
lean_ctor_set(v_reuseFailAlloc_3057_, 1, v___x_3054_);
v___x_3056_ = v_reuseFailAlloc_3057_;
goto v_reusejp_3055_;
}
v_reusejp_3055_:
{
v___y_3031_ = v___x_3056_;
goto v___jp_3030_;
}
}
}
v___jp_3030_:
{
size_t v___x_3032_; size_t v___x_3033_; lean_object* v___x_3034_; 
v___x_3032_ = ((size_t)1ULL);
v___x_3033_ = lean_usize_add(v_i_3019_, v___x_3032_);
v___x_3034_ = lean_array_uset(v_bs_x27_3029_, v_i_3019_, v___y_3031_);
v_i_3019_ = v___x_3033_;
v_bs_3020_ = v___x_3034_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0___boxed(lean_object* v_sz_3059_, lean_object* v_i_3060_, lean_object* v_bs_3061_){
_start:
{
size_t v_sz_boxed_3062_; size_t v_i_boxed_3063_; lean_object* v_res_3064_; 
v_sz_boxed_3062_ = lean_unbox_usize(v_sz_3059_);
lean_dec(v_sz_3059_);
v_i_boxed_3063_ = lean_unbox_usize(v_i_3060_);
lean_dec(v_i_3060_);
v_res_3064_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_boxed_3062_, v_i_boxed_3063_, v_bs_3061_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(lean_object* v_fst_3065_, uint8_t v___x_3066_, lean_object* v_fst_3067_, lean_object* v___x_3068_, lean_object* v_00___3069_){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3070_ = lean_box(v___x_3066_);
v___x_3071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3071_, 0, v_fst_3065_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
v___x_3072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3072_, 0, v_fst_3067_);
lean_ctor_set(v___x_3072_, 1, v___x_3071_);
v___x_3073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3068_);
lean_ctor_set(v___x_3073_, 1, v___x_3072_);
v___x_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0___boxed(lean_object* v_fst_3075_, lean_object* v___x_3076_, lean_object* v_fst_3077_, lean_object* v___x_3078_, lean_object* v_00___3079_){
_start:
{
uint8_t v___x_10196__boxed_3080_; lean_object* v_res_3081_; 
v___x_10196__boxed_3080_ = lean_unbox(v___x_3076_);
v_res_3081_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_3075_, v___x_10196__boxed_3080_, v_fst_3077_, v___x_3078_, v_00___3079_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(lean_object* v___x_3082_, uint8_t v_inSubst_3083_, lean_object* v___x_3084_, lean_object* v_____r_3085_, lean_object* v_wssIdx_3086_){
_start:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3087_ = lean_box(v_inSubst_3083_);
v___x_3088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3082_);
lean_ctor_set(v___x_3088_, 1, v___x_3087_);
v___x_3089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3089_, 0, v_wssIdx_3086_);
lean_ctor_set(v___x_3089_, 1, v___x_3088_);
v___x_3090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3084_);
lean_ctor_set(v___x_3090_, 1, v___x_3089_);
v___x_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1___boxed(lean_object* v___x_3092_, lean_object* v_inSubst_3093_, lean_object* v___x_3094_, lean_object* v_____r_3095_, lean_object* v_wssIdx_3096_){
_start:
{
uint8_t v_inSubst_boxed_3097_; lean_object* v_res_3098_; 
v_inSubst_boxed_3097_ = lean_unbox(v_inSubst_3093_);
v_res_3098_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_3092_, v_inSubst_boxed_3097_, v___x_3094_, v_____r_3095_, v_wssIdx_3096_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(uint8_t v_inSubst_3099_, lean_object* v_snd_3100_, lean_object* v_fst_3101_, lean_object* v_____r_3102_, lean_object* v_withWs_3103_, lean_object* v_wssIdx_3104_){
_start:
{
lean_object* v_wss_x27Idx_3106_; uint8_t v___x_3112_; 
v___x_3112_ = lean_unbox(v_snd_3100_);
if (v___x_3112_ == 0)
{
v_wss_x27Idx_3106_ = v_fst_3101_;
goto v___jp_3105_;
}
else
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3113_ = lean_unsigned_to_nat(1u);
v___x_3114_ = lean_nat_add(v_fst_3101_, v___x_3113_);
lean_dec(v_fst_3101_);
v_wss_x27Idx_3106_ = v___x_3114_;
goto v___jp_3105_;
}
v___jp_3105_:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; 
v___x_3107_ = lean_box(v_inSubst_3099_);
v___x_3108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3108_, 0, v_wss_x27Idx_3106_);
lean_ctor_set(v___x_3108_, 1, v___x_3107_);
v___x_3109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3109_, 0, v_wssIdx_3104_);
lean_ctor_set(v___x_3109_, 1, v___x_3108_);
v___x_3110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3110_, 0, v_withWs_3103_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
v___x_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3110_);
return v___x_3111_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2___boxed(lean_object* v_inSubst_3115_, lean_object* v_snd_3116_, lean_object* v_fst_3117_, lean_object* v_____r_3118_, lean_object* v_withWs_3119_, lean_object* v_wssIdx_3120_){
_start:
{
uint8_t v_inSubst_boxed_3121_; lean_object* v_res_3122_; 
v_inSubst_boxed_3121_ = lean_unbox(v_inSubst_3115_);
v_res_3122_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_boxed_3121_, v_snd_3116_, v_fst_3117_, v_____r_3118_, v_withWs_3119_, v_wssIdx_3120_);
lean_dec(v_snd_3116_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(lean_object* v_upperBound_3123_, lean_object* v_diff_3124_, lean_object* v_snd_3125_, lean_object* v_snd_3126_, lean_object* v_a_3127_, lean_object* v_b_3128_){
_start:
{
lean_object* v_a_3130_; lean_object* v___y_3135_; uint8_t v___x_3138_; 
v___x_3138_ = lean_nat_dec_lt(v_a_3127_, v_upperBound_3123_);
if (v___x_3138_ == 0)
{
lean_dec(v_a_3127_);
return v_b_3128_;
}
else
{
lean_object* v___x_3139_; lean_object* v_snd_3140_; lean_object* v_snd_3141_; lean_object* v_fst_3142_; lean_object* v_fst_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3283_; 
v___x_3139_ = lean_array_fget_borrowed(v_diff_3124_, v_a_3127_);
v_snd_3140_ = lean_ctor_get(v_b_3128_, 1);
lean_inc(v_snd_3140_);
v_snd_3141_ = lean_ctor_get(v_snd_3140_, 1);
lean_inc(v_snd_3141_);
v_fst_3142_ = lean_ctor_get(v___x_3139_, 0);
v_fst_3143_ = lean_ctor_get(v_b_3128_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v_b_3128_);
if (v_isSharedCheck_3283_ == 0)
{
lean_object* v_unused_3284_; 
v_unused_3284_ = lean_ctor_get(v_b_3128_, 1);
lean_dec(v_unused_3284_);
v___x_3145_ = v_b_3128_;
v_isShared_3146_ = v_isSharedCheck_3283_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_fst_3143_);
lean_dec(v_b_3128_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3283_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v_fst_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3281_; 
v_fst_3147_ = lean_ctor_get(v_snd_3140_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v_snd_3140_);
if (v_isSharedCheck_3281_ == 0)
{
lean_object* v_unused_3282_; 
v_unused_3282_ = lean_ctor_get(v_snd_3140_, 1);
lean_dec(v_unused_3282_);
v___x_3149_ = v_snd_3140_;
v_isShared_3150_ = v_isSharedCheck_3281_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_fst_3147_);
lean_dec(v_snd_3140_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3281_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v_fst_3151_; lean_object* v_snd_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3280_; 
v_fst_3151_ = lean_ctor_get(v_snd_3141_, 0);
v_snd_3152_ = lean_ctor_get(v_snd_3141_, 1);
v_isSharedCheck_3280_ = !lean_is_exclusive(v_snd_3141_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3154_ = v_snd_3141_;
v_isShared_3155_ = v_isSharedCheck_3280_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_snd_3152_);
lean_inc(v_fst_3151_);
lean_dec(v_snd_3141_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3280_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3156_; lean_object* v___y_3158_; lean_object* v___y_3173_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; uint8_t v___x_3184_; 
lean_inc(v___x_3139_);
v___x_3156_ = lean_array_push(v_fst_3143_, v___x_3139_);
v___x_3181_ = lean_unsigned_to_nat(1u);
v___x_3182_ = lean_nat_add(v_a_3127_, v___x_3181_);
v___x_3183_ = lean_array_get_size(v_diff_3124_);
v___x_3184_ = lean_nat_dec_lt(v___x_3182_, v___x_3183_);
if (v___x_3184_ == 0)
{
lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
lean_dec(v___x_3182_);
lean_del_object(v___x_3154_);
lean_del_object(v___x_3149_);
lean_del_object(v___x_3145_);
v___x_3185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3185_, 0, v_fst_3151_);
lean_ctor_set(v___x_3185_, 1, v_snd_3152_);
v___x_3186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3186_, 0, v_fst_3147_);
lean_ctor_set(v___x_3186_, 1, v___x_3185_);
v___x_3187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3156_);
lean_ctor_set(v___x_3187_, 1, v___x_3186_);
v_a_3130_ = v___x_3187_;
goto v___jp_3129_;
}
else
{
lean_object* v___x_3188_; lean_object* v_fst_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3278_; 
v___x_3188_ = lean_array_fget(v_diff_3124_, v___x_3182_);
lean_dec(v___x_3182_);
v_fst_3189_ = lean_ctor_get(v___x_3188_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3188_);
if (v_isSharedCheck_3278_ == 0)
{
lean_object* v_unused_3279_; 
v_unused_3279_ = lean_ctor_get(v___x_3188_, 1);
lean_dec(v_unused_3279_);
v___x_3191_ = v___x_3188_;
v_isShared_3192_ = v_isSharedCheck_3278_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_fst_3189_);
lean_dec(v___x_3188_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3278_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
uint8_t v_inSubst_3193_; lean_object* v___y_3195_; lean_object* v___x_3204_; uint8_t v___x_3205_; 
v_inSubst_3193_ = 0;
v___x_3204_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_3205_ = lean_unbox(v_fst_3142_);
switch(v___x_3205_)
{
case 0:
{
uint8_t v___x_3206_; 
lean_del_object(v___x_3154_);
lean_del_object(v___x_3149_);
lean_del_object(v___x_3145_);
v___x_3206_ = lean_unbox(v_fst_3189_);
switch(v___x_3206_)
{
case 0:
{
lean_object* v___x_3207_; lean_object* v___x_3209_; 
v___x_3207_ = lean_array_get_borrowed(v___x_3204_, v_snd_3125_, v_fst_3151_);
lean_inc(v___x_3207_);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 1, v___x_3207_);
v___x_3209_ = v___x_3191_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_fst_3189_);
lean_ctor_set(v_reuseFailAlloc_3215_, 1, v___x_3207_);
v___x_3209_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3210_ = lean_array_push(v___x_3156_, v___x_3209_);
v___x_3211_ = lean_nat_add(v_fst_3151_, v___x_3181_);
lean_dec(v_fst_3151_);
v___x_3212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
lean_ctor_set(v___x_3212_, 1, v_snd_3152_);
v___x_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3213_, 0, v_fst_3147_);
lean_ctor_set(v___x_3213_, 1, v___x_3212_);
v___x_3214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3210_);
lean_ctor_set(v___x_3214_, 1, v___x_3213_);
v_a_3130_ = v___x_3214_;
goto v___jp_3129_;
}
}
case 1:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
lean_del_object(v___x_3191_);
lean_dec(v_fst_3189_);
lean_dec(v_snd_3152_);
v___x_3216_ = lean_box(0);
v___x_3217_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_3151_, v___x_3138_, v_fst_3147_, v___x_3156_, v___x_3216_);
v___y_3135_ = v___x_3217_;
goto v___jp_3134_;
}
default: 
{
lean_object* v___x_3218_; uint8_t v___x_3219_; 
lean_dec(v_fst_3189_);
v___x_3218_ = lean_array_get_borrowed(v___x_3204_, v_snd_3125_, v_fst_3151_);
v___x_3219_ = lean_unbox(v_snd_3152_);
if (v___x_3219_ == 0)
{
lean_object* v___x_3221_; 
lean_inc(v___x_3218_);
lean_inc(v_fst_3142_);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 1, v___x_3218_);
lean_ctor_set(v___x_3191_, 0, v_fst_3142_);
v___x_3221_ = v___x_3191_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_fst_3142_);
lean_ctor_set(v_reuseFailAlloc_3224_, 1, v___x_3218_);
v___x_3221_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = lean_mk_empty_array_with_capacity(v___x_3181_);
v___x_3223_ = lean_array_push(v___x_3222_, v___x_3221_);
v___y_3195_ = v___x_3223_;
goto v___jp_3194_;
}
}
else
{
lean_object* v___x_3225_; lean_object* v___x_3226_; 
lean_del_object(v___x_3191_);
v___x_3225_ = lean_array_get_borrowed(v___x_3204_, v_snd_3126_, v_fst_3147_);
lean_inc(v___x_3218_);
lean_inc(v___x_3225_);
v___x_3226_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_3225_, v___x_3218_);
v___y_3195_ = v___x_3226_;
goto v___jp_3194_;
}
}
}
}
case 1:
{
uint8_t v___x_3227_; 
lean_del_object(v___x_3154_);
lean_del_object(v___x_3149_);
lean_del_object(v___x_3145_);
v___x_3227_ = lean_unbox(v_fst_3189_);
switch(v___x_3227_)
{
case 0:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; 
lean_del_object(v___x_3191_);
lean_dec(v_fst_3189_);
lean_dec(v_snd_3152_);
v___x_3228_ = lean_box(0);
v___x_3229_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_3151_, v___x_3138_, v_fst_3147_, v___x_3156_, v___x_3228_);
v___y_3135_ = v___x_3229_;
goto v___jp_3134_;
}
case 1:
{
lean_object* v___x_3230_; lean_object* v___x_3232_; 
v___x_3230_ = lean_array_get_borrowed(v___x_3204_, v_snd_3126_, v_fst_3147_);
lean_inc(v___x_3230_);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 1, v___x_3230_);
v___x_3232_ = v___x_3191_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_fst_3189_);
lean_ctor_set(v_reuseFailAlloc_3238_, 1, v___x_3230_);
v___x_3232_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3233_ = lean_array_push(v___x_3156_, v___x_3232_);
v___x_3234_ = lean_nat_add(v_fst_3147_, v___x_3181_);
lean_dec(v_fst_3147_);
v___x_3235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3235_, 0, v_fst_3151_);
lean_ctor_set(v___x_3235_, 1, v_snd_3152_);
v___x_3236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3234_);
lean_ctor_set(v___x_3236_, 1, v___x_3235_);
v___x_3237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3233_);
lean_ctor_set(v___x_3237_, 1, v___x_3236_);
v_a_3130_ = v___x_3237_;
goto v___jp_3129_;
}
}
default: 
{
uint8_t v___x_3242_; 
lean_dec(v_fst_3189_);
v___x_3242_ = lean_unbox(v_snd_3152_);
if (v___x_3242_ == 0)
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; uint8_t v___x_3247_; 
v___x_3243_ = lean_array_get_borrowed(v___x_3204_, v_snd_3126_, v_fst_3147_);
v___x_3244_ = lean_unsigned_to_nat(0u);
v___x_3245_ = lean_string_utf8_byte_size(v___x_3243_);
lean_inc(v___x_3243_);
v___x_3246_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3243_);
lean_ctor_set(v___x_3246_, 1, v___x_3244_);
lean_ctor_set(v___x_3246_, 2, v___x_3245_);
v___x_3247_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_3246_);
lean_dec_ref_known(v___x_3246_, 3);
if (v___x_3247_ == 0)
{
lean_object* v___x_3249_; 
lean_inc(v___x_3243_);
lean_inc(v_fst_3142_);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 1, v___x_3243_);
lean_ctor_set(v___x_3191_, 0, v_fst_3142_);
v___x_3249_ = v___x_3191_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_fst_3142_);
lean_ctor_set(v_reuseFailAlloc_3254_, 1, v___x_3243_);
v___x_3249_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3250_ = lean_array_push(v___x_3156_, v___x_3249_);
v___x_3251_ = lean_nat_add(v_fst_3147_, v___x_3181_);
lean_dec(v_fst_3147_);
v___x_3252_ = lean_box(0);
v___x_3253_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_3193_, v_snd_3152_, v_fst_3151_, v___x_3252_, v___x_3250_, v___x_3251_);
lean_dec(v_snd_3152_);
v___y_3135_ = v___x_3253_;
goto v___jp_3134_;
}
}
else
{
lean_del_object(v___x_3191_);
goto v___jp_3239_;
}
}
else
{
lean_del_object(v___x_3191_);
goto v___jp_3239_;
}
v___jp_3239_:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3240_ = lean_box(0);
v___x_3241_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_3193_, v_snd_3152_, v_fst_3151_, v___x_3240_, v___x_3156_, v_fst_3147_);
lean_dec(v_snd_3152_);
v___y_3135_ = v___x_3241_;
goto v___jp_3134_;
}
}
}
}
default: 
{
uint8_t v___x_3255_; 
v___x_3255_ = lean_unbox(v_fst_3189_);
if (v___x_3255_ == 1)
{
lean_object* v___x_3256_; lean_object* v___x_3257_; uint8_t v___x_3258_; 
v___x_3256_ = lean_array_get_borrowed(v___x_3204_, v_snd_3126_, v_fst_3147_);
v___x_3257_ = lean_array_get_size(v_snd_3125_);
v___x_3258_ = lean_nat_dec_lt(v_fst_3151_, v___x_3257_);
if (v___x_3258_ == 0)
{
lean_object* v___x_3260_; 
lean_inc(v___x_3256_);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 1, v___x_3256_);
v___x_3260_ = v___x_3191_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v_fst_3189_);
lean_ctor_set(v_reuseFailAlloc_3263_, 1, v___x_3256_);
v___x_3260_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3261_ = lean_mk_empty_array_with_capacity(v___x_3181_);
v___x_3262_ = lean_array_push(v___x_3261_, v___x_3260_);
v___y_3158_ = v___x_3262_;
goto v___jp_3157_;
}
}
else
{
lean_object* v___x_3264_; lean_object* v___x_3265_; 
lean_del_object(v___x_3191_);
lean_dec(v_fst_3189_);
v___x_3264_ = lean_array_fget_borrowed(v_snd_3125_, v_fst_3151_);
lean_inc(v___x_3264_);
lean_inc(v___x_3256_);
v___x_3265_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_3256_, v___x_3264_);
v___y_3158_ = v___x_3265_;
goto v___jp_3157_;
}
}
else
{
lean_object* v___x_3266_; lean_object* v___x_3267_; uint8_t v___x_3268_; 
lean_dec(v_fst_3189_);
lean_del_object(v___x_3154_);
lean_del_object(v___x_3149_);
lean_del_object(v___x_3145_);
v___x_3266_ = lean_array_get_borrowed(v___x_3204_, v_snd_3125_, v_fst_3151_);
v___x_3267_ = lean_array_get_size(v_snd_3126_);
v___x_3268_ = lean_nat_dec_lt(v_fst_3147_, v___x_3267_);
if (v___x_3268_ == 0)
{
uint8_t v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3272_; 
v___x_3269_ = 0;
v___x_3270_ = lean_box(v___x_3269_);
lean_inc(v___x_3266_);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 1, v___x_3266_);
lean_ctor_set(v___x_3191_, 0, v___x_3270_);
v___x_3272_ = v___x_3191_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v___x_3270_);
lean_ctor_set(v_reuseFailAlloc_3275_, 1, v___x_3266_);
v___x_3272_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3273_ = lean_mk_empty_array_with_capacity(v___x_3181_);
v___x_3274_ = lean_array_push(v___x_3273_, v___x_3272_);
v___y_3173_ = v___x_3274_;
goto v___jp_3172_;
}
}
else
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
lean_del_object(v___x_3191_);
v___x_3276_ = lean_array_fget_borrowed(v_snd_3126_, v_fst_3147_);
lean_inc(v___x_3266_);
lean_inc(v___x_3276_);
v___x_3277_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_3276_, v___x_3266_);
v___y_3173_ = v___x_3277_;
goto v___jp_3172_;
}
}
}
}
v___jp_3194_:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; uint8_t v___x_3198_; 
v___x_3196_ = l_Array_append___redArg(v___x_3156_, v___y_3195_);
lean_dec_ref(v___y_3195_);
v___x_3197_ = lean_nat_add(v_fst_3151_, v___x_3181_);
lean_dec(v_fst_3151_);
v___x_3198_ = lean_unbox(v_snd_3152_);
lean_dec(v_snd_3152_);
if (v___x_3198_ == 0)
{
lean_object* v___x_3199_; lean_object* v___x_3200_; 
v___x_3199_ = lean_box(0);
v___x_3200_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_3197_, v_inSubst_3193_, v___x_3196_, v___x_3199_, v_fst_3147_);
v___y_3135_ = v___x_3200_;
goto v___jp_3134_;
}
else
{
lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3201_ = lean_nat_add(v_fst_3147_, v___x_3181_);
lean_dec(v_fst_3147_);
v___x_3202_ = lean_box(0);
v___x_3203_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_3197_, v_inSubst_3193_, v___x_3196_, v___x_3202_, v___x_3201_);
v___y_3135_ = v___x_3203_;
goto v___jp_3134_;
}
}
}
}
v___jp_3157_:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3164_; 
v___x_3159_ = l_Array_append___redArg(v___x_3156_, v___y_3158_);
lean_dec_ref(v___y_3158_);
v___x_3160_ = lean_unsigned_to_nat(1u);
v___x_3161_ = lean_nat_add(v_fst_3147_, v___x_3160_);
lean_dec(v_fst_3147_);
v___x_3162_ = lean_nat_add(v_fst_3151_, v___x_3160_);
lean_dec(v_fst_3151_);
if (v_isShared_3155_ == 0)
{
lean_ctor_set(v___x_3154_, 0, v___x_3162_);
v___x_3164_ = v___x_3154_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v___x_3162_);
lean_ctor_set(v_reuseFailAlloc_3171_, 1, v_snd_3152_);
v___x_3164_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
lean_object* v___x_3166_; 
if (v_isShared_3150_ == 0)
{
lean_ctor_set(v___x_3149_, 1, v___x_3164_);
lean_ctor_set(v___x_3149_, 0, v___x_3161_);
v___x_3166_ = v___x_3149_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v___x_3161_);
lean_ctor_set(v_reuseFailAlloc_3170_, 1, v___x_3164_);
v___x_3166_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
lean_object* v___x_3168_; 
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 1, v___x_3166_);
lean_ctor_set(v___x_3145_, 0, v___x_3159_);
v___x_3168_ = v___x_3145_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3169_; 
v_reuseFailAlloc_3169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3169_, 0, v___x_3159_);
lean_ctor_set(v_reuseFailAlloc_3169_, 1, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3169_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
v_a_3130_ = v___x_3168_;
goto v___jp_3129_;
}
}
}
}
v___jp_3172_:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3174_ = l_Array_append___redArg(v___x_3156_, v___y_3173_);
lean_dec_ref(v___y_3173_);
v___x_3175_ = lean_unsigned_to_nat(1u);
v___x_3176_ = lean_nat_add(v_fst_3147_, v___x_3175_);
lean_dec(v_fst_3147_);
v___x_3177_ = lean_nat_add(v_fst_3151_, v___x_3175_);
lean_dec(v_fst_3151_);
v___x_3178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
lean_ctor_set(v___x_3178_, 1, v_snd_3152_);
v___x_3179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3179_, 0, v___x_3176_);
lean_ctor_set(v___x_3179_, 1, v___x_3178_);
v___x_3180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3174_);
lean_ctor_set(v___x_3180_, 1, v___x_3179_);
v_a_3130_ = v___x_3180_;
goto v___jp_3129_;
}
}
}
}
}
v___jp_3129_:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
v___x_3131_ = lean_unsigned_to_nat(1u);
v___x_3132_ = lean_nat_add(v_a_3127_, v___x_3131_);
lean_dec(v_a_3127_);
v_a_3127_ = v___x_3132_;
v_b_3128_ = v_a_3130_;
goto _start;
}
v___jp_3134_:
{
if (lean_obj_tag(v___y_3135_) == 0)
{
lean_object* v_a_3136_; 
lean_dec(v_a_3127_);
v_a_3136_ = lean_ctor_get(v___y_3135_, 0);
lean_inc(v_a_3136_);
lean_dec_ref_known(v___y_3135_, 1);
return v_a_3136_;
}
else
{
lean_object* v_a_3137_; 
v_a_3137_ = lean_ctor_get(v___y_3135_, 0);
lean_inc(v_a_3137_);
lean_dec_ref_known(v___y_3135_, 1);
v_a_3130_ = v_a_3137_;
goto v___jp_3129_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___boxed(lean_object* v_upperBound_3285_, lean_object* v_diff_3286_, lean_object* v_snd_3287_, lean_object* v_snd_3288_, lean_object* v_a_3289_, lean_object* v_b_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_3285_, v_diff_3286_, v_snd_3287_, v_snd_3288_, v_a_3289_, v_b_3290_);
lean_dec_ref(v_snd_3288_);
lean_dec_ref(v_snd_3287_);
lean_dec_ref(v_diff_3286_);
lean_dec(v_upperBound_3285_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(lean_object* v_s_3302_, lean_object* v_s_x27_3303_){
_start:
{
lean_object* v___x_3304_; lean_object* v_fst_3305_; lean_object* v_snd_3306_; lean_object* v___x_3307_; lean_object* v_fst_3308_; lean_object* v_snd_3309_; lean_object* v_diff_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v_fst_3315_; lean_object* v___x_3316_; size_t v_sz_3317_; size_t v___x_3318_; lean_object* v___x_3319_; 
v___x_3304_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_3302_);
v_fst_3305_ = lean_ctor_get(v___x_3304_, 0);
lean_inc(v_fst_3305_);
v_snd_3306_ = lean_ctor_get(v___x_3304_, 1);
lean_inc(v_snd_3306_);
lean_dec_ref(v___x_3304_);
v___x_3307_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_x27_3303_);
v_fst_3308_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_fst_3308_);
v_snd_3309_ = lean_ctor_get(v___x_3307_, 1);
lean_inc(v_snd_3309_);
lean_dec_ref(v___x_3307_);
v_diff_3310_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(v_fst_3305_, v_fst_3308_);
v___x_3311_ = lean_unsigned_to_nat(0u);
v___x_3312_ = lean_array_get_size(v_diff_3310_);
v___x_3313_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__2));
v___x_3314_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v___x_3312_, v_diff_3310_, v_snd_3309_, v_snd_3306_, v___x_3311_, v___x_3313_);
lean_dec(v_snd_3306_);
lean_dec(v_snd_3309_);
lean_dec_ref(v_diff_3310_);
v_fst_3315_ = lean_ctor_get(v___x_3314_, 0);
lean_inc(v_fst_3315_);
lean_dec_ref(v___x_3314_);
v___x_3316_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_fst_3315_);
lean_dec(v_fst_3315_);
v_sz_3317_ = lean_array_size(v___x_3316_);
v___x_3318_ = ((size_t)0ULL);
v___x_3319_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_3317_, v___x_3318_, v___x_3316_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___boxed(lean_object* v_s_3320_, lean_object* v_s_x27_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3320_, v_s_x27_3321_);
lean_dec_ref(v_s_x27_3321_);
lean_dec_ref(v_s_3320_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(lean_object* v_upperBound_3323_, lean_object* v_diff_3324_, lean_object* v_snd_3325_, lean_object* v_snd_3326_, lean_object* v_inst_3327_, lean_object* v_R_3328_, lean_object* v_a_3329_, lean_object* v_b_3330_, lean_object* v_c_3331_){
_start:
{
lean_object* v___x_3332_; 
v___x_3332_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_3323_, v_diff_3324_, v_snd_3325_, v_snd_3326_, v_a_3329_, v_b_3330_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___boxed(lean_object* v_upperBound_3333_, lean_object* v_diff_3334_, lean_object* v_snd_3335_, lean_object* v_snd_3336_, lean_object* v_inst_3337_, lean_object* v_R_3338_, lean_object* v_a_3339_, lean_object* v_b_3340_, lean_object* v_c_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(v_upperBound_3333_, v_diff_3334_, v_snd_3335_, v_snd_3336_, v_inst_3337_, v_R_3338_, v_a_3339_, v_b_3340_, v_c_3341_);
lean_dec_ref(v_snd_3336_);
lean_dec_ref(v_snd_3335_);
lean_dec_ref(v_diff_3334_);
lean_dec(v_upperBound_3333_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(lean_object* v_original_3343_, lean_object* v___x_3344_, lean_object* v_a_3345_, lean_object* v_inst_3346_, lean_object* v_a_3347_){
_start:
{
lean_object* v___x_3348_; 
v___x_3348_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v_original_3343_, v___x_3344_, v_a_3345_, v_a_3347_);
return v___x_3348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___boxed(lean_object* v_original_3349_, lean_object* v___x_3350_, lean_object* v_a_3351_, lean_object* v_inst_3352_, lean_object* v_a_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(v_original_3349_, v___x_3350_, v_a_3351_, v_inst_3352_, v_a_3353_);
lean_dec_ref(v_a_3351_);
lean_dec(v___x_3350_);
lean_dec_ref(v_original_3349_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(lean_object* v_edited_3355_, lean_object* v___x_3356_, lean_object* v_a_3357_, lean_object* v_inst_3358_, lean_object* v_a_3359_){
_start:
{
lean_object* v___x_3360_; 
v___x_3360_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(v_edited_3355_, v___x_3356_, v_a_3357_, v_a_3359_);
return v___x_3360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___boxed(lean_object* v_edited_3361_, lean_object* v___x_3362_, lean_object* v_a_3363_, lean_object* v_inst_3364_, lean_object* v_a_3365_){
_start:
{
lean_object* v_res_3366_; 
v_res_3366_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v_edited_3361_, v___x_3362_, v_a_3363_, v_inst_3364_, v_a_3365_);
lean_dec_ref(v_a_3363_);
lean_dec(v___x_3362_);
lean_dec_ref(v_edited_3361_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(lean_object* v___x_3367_, lean_object* v_original_3368_, lean_object* v_inst_3369_, lean_object* v_a_3370_){
_start:
{
lean_object* v___x_3371_; 
v___x_3371_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_3367_, v_original_3368_, v_a_3370_);
return v___x_3371_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___boxed(lean_object* v___x_3372_, lean_object* v_original_3373_, lean_object* v_inst_3374_, lean_object* v_a_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(v___x_3372_, v_original_3373_, v_inst_3374_, v_a_3375_);
lean_dec_ref(v_original_3373_);
lean_dec(v___x_3372_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(lean_object* v___x_3377_, lean_object* v_edited_3378_, lean_object* v_inst_3379_, lean_object* v_a_3380_){
_start:
{
lean_object* v___x_3381_; 
v___x_3381_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_3377_, v_edited_3378_, v_a_3380_);
return v___x_3381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___boxed(lean_object* v___x_3382_, lean_object* v_edited_3383_, lean_object* v_inst_3384_, lean_object* v_a_3385_){
_start:
{
lean_object* v_res_3386_; 
v_res_3386_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(v___x_3382_, v_edited_3383_, v_inst_3384_, v_a_3385_);
lean_dec_ref(v_edited_3383_);
lean_dec(v___x_3382_);
return v_res_3386_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(lean_object* v_as_3387_, lean_object* v_as_x27_3388_, lean_object* v_b_3389_, lean_object* v_a_3390_){
_start:
{
lean_object* v___x_3391_; 
v___x_3391_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5___redArg(v_as_x27_3388_, v_b_3389_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5___boxed(lean_object* v_as_3392_, lean_object* v_as_x27_3393_, lean_object* v_b_3394_, lean_object* v_a_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(v_as_3392_, v_as_x27_3393_, v_b_3394_, v_a_3395_);
lean_dec(v_as_x27_3393_);
lean_dec(v_as_3392_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(lean_object* v_lsize_3397_, lean_object* v_rsize_3398_, lean_object* v_histogram_3399_, lean_object* v_index_3400_, lean_object* v_val_3401_){
_start:
{
lean_object* v___x_3402_; 
v___x_3402_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6___redArg(v_histogram_3399_, v_index_3400_, v_val_3401_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6___boxed(lean_object* v_lsize_3403_, lean_object* v_rsize_3404_, lean_object* v_histogram_3405_, lean_object* v_index_3406_, lean_object* v_val_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(v_lsize_3403_, v_rsize_3404_, v_histogram_3405_, v_index_3406_, v_val_3407_);
lean_dec(v_rsize_3404_);
lean_dec(v_lsize_3403_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7(lean_object* v_upperBound_3409_, lean_object* v___x_3410_, lean_object* v_fst_3411_, lean_object* v___x_3412_, lean_object* v_inst_3413_, lean_object* v_R_3414_, lean_object* v_a_3415_, lean_object* v_b_3416_, lean_object* v_c_3417_){
_start:
{
lean_object* v___x_3418_; 
v___x_3418_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(v_upperBound_3409_, v___x_3410_, v_fst_3411_, v___x_3412_, v_a_3415_, v_b_3416_);
return v___x_3418_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___boxed(lean_object* v_upperBound_3419_, lean_object* v___x_3420_, lean_object* v_fst_3421_, lean_object* v___x_3422_, lean_object* v_inst_3423_, lean_object* v_R_3424_, lean_object* v_a_3425_, lean_object* v_b_3426_, lean_object* v_c_3427_){
_start:
{
lean_object* v_res_3428_; 
v_res_3428_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7(v_upperBound_3419_, v___x_3420_, v_fst_3421_, v___x_3422_, v_inst_3423_, v_R_3424_, v_a_3425_, v_b_3426_, v_c_3427_);
lean_dec(v___x_3422_);
lean_dec_ref(v_fst_3421_);
lean_dec(v___x_3420_);
lean_dec(v_upperBound_3419_);
return v_res_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8(lean_object* v_lsize_3429_, lean_object* v_rsize_3430_, lean_object* v_histogram_3431_, lean_object* v_index_3432_, lean_object* v_val_3433_){
_start:
{
lean_object* v___x_3434_; 
v___x_3434_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(v_histogram_3431_, v_index_3432_, v_val_3433_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___boxed(lean_object* v_lsize_3435_, lean_object* v_rsize_3436_, lean_object* v_histogram_3437_, lean_object* v_index_3438_, lean_object* v_val_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8(v_lsize_3435_, v_rsize_3436_, v_histogram_3437_, v_index_3438_, v_val_3439_);
lean_dec(v_rsize_3436_);
lean_dec(v_lsize_3435_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9(lean_object* v_upperBound_3441_, lean_object* v_fst_3442_, lean_object* v___x_3443_, lean_object* v_fst_3444_, lean_object* v_inst_3445_, lean_object* v_R_3446_, lean_object* v_a_3447_, lean_object* v_b_3448_, lean_object* v_c_3449_){
_start:
{
lean_object* v___x_3450_; 
v___x_3450_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(v_upperBound_3441_, v_fst_3442_, v___x_3443_, v_fst_3444_, v_a_3447_, v_b_3448_);
return v___x_3450_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___boxed(lean_object* v_upperBound_3451_, lean_object* v_fst_3452_, lean_object* v___x_3453_, lean_object* v_fst_3454_, lean_object* v_inst_3455_, lean_object* v_R_3456_, lean_object* v_a_3457_, lean_object* v_b_3458_, lean_object* v_c_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9(v_upperBound_3451_, v_fst_3452_, v___x_3453_, v_fst_3454_, v_inst_3455_, v_R_3456_, v_a_3457_, v_b_3458_, v_c_3459_);
lean_dec_ref(v_fst_3454_);
lean_dec(v___x_3453_);
lean_dec_ref(v_fst_3452_);
lean_dec(v_upperBound_3451_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10(lean_object* v_00_u03b2_3461_, lean_object* v_m_3462_, lean_object* v_a_3463_){
_start:
{
lean_object* v___x_3464_; 
v___x_3464_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10___redArg(v_m_3462_, v_a_3463_);
return v___x_3464_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10___boxed(lean_object* v_00_u03b2_3465_, lean_object* v_m_3466_, lean_object* v_a_3467_){
_start:
{
lean_object* v_res_3468_; 
v_res_3468_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10(v_00_u03b2_3465_, v_m_3466_, v_a_3467_);
lean_dec_ref(v_a_3467_);
lean_dec_ref(v_m_3466_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11(lean_object* v_00_u03b2_3469_, lean_object* v_m_3470_, lean_object* v_query_3471_){
_start:
{
lean_object* v___x_3472_; 
v___x_3472_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11___redArg(v_m_3470_, v_query_3471_);
return v___x_3472_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11___boxed(lean_object* v_00_u03b2_3473_, lean_object* v_m_3474_, lean_object* v_query_3475_){
_start:
{
lean_object* v_res_3476_; 
v_res_3476_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11(v_00_u03b2_3473_, v_m_3474_, v_query_3475_);
lean_dec_ref(v_query_3475_);
lean_dec_ref(v_m_3474_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12(lean_object* v_00_u03b2_3477_, lean_object* v_m_3478_){
_start:
{
lean_object* v___x_3479_; 
v___x_3479_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12___redArg(v_m_3478_);
return v___x_3479_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12___boxed(lean_object* v_00_u03b2_3480_, lean_object* v_m_3481_){
_start:
{
lean_object* v_res_3482_; 
v_res_3482_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12(v_00_u03b2_3480_, v_m_3481_);
lean_dec_ref(v_m_3481_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14(lean_object* v_inst_3483_, lean_object* v_R_3484_, lean_object* v_a_3485_, lean_object* v_b_3486_){
_start:
{
lean_object* v___x_3487_; 
v___x_3487_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v_a_3485_, v_b_3486_);
return v___x_3487_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10_spec__19(lean_object* v_00_u03b2_3488_, lean_object* v_m_3489_, lean_object* v_query_3490_){
_start:
{
lean_object* v___x_3491_; 
v___x_3491_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10_spec__19___redArg(v_m_3489_, v_query_3490_);
return v___x_3491_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10_spec__19___boxed(lean_object* v_00_u03b2_3492_, lean_object* v_m_3493_, lean_object* v_query_3494_){
_start:
{
lean_object* v_res_3495_; 
v_res_3495_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__10_spec__19(v_00_u03b2_3492_, v_m_3493_, v_query_3494_);
lean_dec_ref(v_query_3494_);
lean_dec_ref(v_m_3493_);
return v_res_3495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11_spec__21(lean_object* v_00_u03b2_3496_, lean_object* v_m_3497_, lean_object* v_query_3498_, lean_object* v_x_3499_, lean_object* v_x_3500_, lean_object* v_x_3501_, lean_object* v_x_3502_){
_start:
{
lean_object* v___x_3503_; 
v___x_3503_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11_spec__21___redArg(v_m_3497_, v_query_3498_, v_x_3499_, v_x_3500_, v_x_3501_);
return v___x_3503_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11_spec__21___boxed(lean_object* v_00_u03b2_3504_, lean_object* v_m_3505_, lean_object* v_query_3506_, lean_object* v_x_3507_, lean_object* v_x_3508_, lean_object* v_x_3509_, lean_object* v_x_3510_){
_start:
{
lean_object* v_res_3511_; 
v_res_3511_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__11_spec__21(v_00_u03b2_3504_, v_m_3505_, v_query_3506_, v_x_3507_, v_x_3508_, v_x_3509_, v_x_3510_);
lean_dec_ref(v_query_3506_);
lean_dec_ref(v_m_3505_);
return v_res_3511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23(lean_object* v_00_u03b2_3512_, lean_object* v_init_3513_, lean_object* v_b_3514_){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23___redArg(v_init_3513_, v_b_3514_);
return v___x_3515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23___boxed(lean_object* v_00_u03b2_3516_, lean_object* v_init_3517_, lean_object* v_b_3518_){
_start:
{
lean_object* v_res_3519_; 
v_res_3519_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23(v_00_u03b2_3516_, v_init_3517_, v_b_3518_);
lean_dec_ref(v_b_3518_);
return v_res_3519_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23_spec__28(lean_object* v_00_u03b2_3520_, lean_object* v_b_3521_, lean_object* v_acc_3522_, lean_object* v_i_3523_){
_start:
{
lean_object* v___x_3524_; 
v___x_3524_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23_spec__28___redArg(v_b_3521_, v_acc_3522_, v_i_3523_);
return v___x_3524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23_spec__28___boxed(lean_object* v_00_u03b2_3525_, lean_object* v_b_3526_, lean_object* v_acc_3527_, lean_object* v_i_3528_){
_start:
{
lean_object* v_res_3529_; 
v_res_3529_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6_spec__12_spec__23_spec__28(v_00_u03b2_3525_, v_b_3526_, v_acc_3527_, v_i_3528_);
lean_dec_ref(v_b_3526_);
return v_res_3529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(lean_object* v_s_3530_){
_start:
{
lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3531_ = lean_string_data(v_s_3530_);
v___x_3532_ = lean_array_mk(v___x_3531_);
return v___x_3532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(lean_object* v_s_3533_, lean_object* v_s_x27_3534_){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3535_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3533_);
v___x_3536_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3534_);
v___x_3537_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3535_, v___x_3536_);
v___x_3538_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_3537_);
lean_dec_ref(v___x_3537_);
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(lean_object* v_s_3539_, lean_object* v_s_x27_3540_){
_start:
{
uint8_t v___x_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; uint8_t v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3541_ = 1;
v___x_3542_ = lean_box(v___x_3541_);
v___x_3543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3543_, 0, v___x_3542_);
lean_ctor_set(v___x_3543_, 1, v_s_3539_);
v___x_3544_ = 0;
v___x_3545_ = lean_box(v___x_3544_);
v___x_3546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3545_);
lean_ctor_set(v___x_3546_, 1, v_s_x27_3540_);
v___x_3547_ = lean_unsigned_to_nat(2u);
v___x_3548_ = lean_mk_empty_array_with_capacity(v___x_3547_);
v___x_3549_ = lean_array_push(v___x_3548_, v___x_3543_);
v___x_3550_ = lean_array_push(v___x_3549_, v___x_3546_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(lean_object* v_as_3551_, size_t v_i_3552_, size_t v_stop_3553_, lean_object* v_b_3554_){
_start:
{
lean_object* v___y_3556_; uint8_t v___x_3560_; 
v___x_3560_ = lean_usize_dec_eq(v_i_3552_, v_stop_3553_);
if (v___x_3560_ == 0)
{
lean_object* v___x_3561_; lean_object* v_fst_3562_; uint8_t v___x_3563_; uint8_t v___x_3564_; uint8_t v___x_3565_; 
v___x_3561_ = lean_array_uget_borrowed(v_as_3551_, v_i_3552_);
v_fst_3562_ = lean_ctor_get(v___x_3561_, 0);
v___x_3563_ = 2;
v___x_3564_ = lean_unbox(v_fst_3562_);
v___x_3565_ = l_Lean_Diff_instBEqAction_beq(v___x_3564_, v___x_3563_);
if (v___x_3565_ == 0)
{
lean_object* v___x_3566_; 
lean_inc(v___x_3561_);
v___x_3566_ = lean_array_push(v_b_3554_, v___x_3561_);
v___y_3556_ = v___x_3566_;
goto v___jp_3555_;
}
else
{
v___y_3556_ = v_b_3554_;
goto v___jp_3555_;
}
}
else
{
return v_b_3554_;
}
v___jp_3555_:
{
size_t v___x_3557_; size_t v___x_3558_; 
v___x_3557_ = ((size_t)1ULL);
v___x_3558_ = lean_usize_add(v_i_3552_, v___x_3557_);
v_i_3552_ = v___x_3558_;
v_b_3554_ = v___y_3556_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0___boxed(lean_object* v_as_3567_, lean_object* v_i_3568_, lean_object* v_stop_3569_, lean_object* v_b_3570_){
_start:
{
size_t v_i_boxed_3571_; size_t v_stop_boxed_3572_; lean_object* v_res_3573_; 
v_i_boxed_3571_ = lean_unbox_usize(v_i_3568_);
lean_dec(v_i_3568_);
v_stop_boxed_3572_ = lean_unbox_usize(v_stop_3569_);
lean_dec(v_stop_3569_);
v_res_3573_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_as_3567_, v_i_boxed_3571_, v_stop_boxed_3572_, v_b_3570_);
lean_dec_ref(v_as_3567_);
return v_res_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff(lean_object* v_s_3574_, lean_object* v_s_x27_3575_, uint8_t v_granularity_3576_){
_start:
{
lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___y_3580_; uint8_t v___y_3581_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; 
switch(v_granularity_3576_)
{
case 0:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___y_3623_; uint8_t v___x_3629_; 
v___x_3620_ = lean_string_length(v_s_3574_);
v___x_3621_ = lean_string_length(v_s_x27_3575_);
v___x_3629_ = lean_nat_dec_le(v___x_3620_, v___x_3621_);
if (v___x_3629_ == 0)
{
v___y_3623_ = v___x_3621_;
goto v___jp_3622_;
}
else
{
v___y_3623_ = v___x_3620_;
goto v___jp_3622_;
}
v___jp_3622_:
{
lean_object* v___x_3624_; lean_object* v_maxCharDiffDistance_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; uint8_t v___x_3628_; 
v___x_3624_ = lean_unsigned_to_nat(5u);
v_maxCharDiffDistance_3625_ = lean_nat_div(v___y_3623_, v___x_3624_);
v___x_3626_ = lean_unsigned_to_nat(1u);
v___x_3627_ = lean_nat_shiftr(v___y_3623_, v___x_3626_);
lean_dec(v___y_3623_);
v___x_3628_ = lean_nat_dec_le(v___x_3620_, v___x_3621_);
if (v___x_3628_ == 0)
{
v___y_3600_ = v___x_3627_;
v___y_3601_ = v___x_3626_;
v___y_3602_ = v_maxCharDiffDistance_3625_;
v___y_3603_ = v___x_3620_;
goto v___jp_3599_;
}
else
{
v___y_3600_ = v___x_3627_;
v___y_3601_ = v___x_3626_;
v___y_3602_ = v_maxCharDiffDistance_3625_;
v___y_3603_ = v___x_3621_;
goto v___jp_3599_;
}
}
}
case 1:
{
lean_object* v___x_3630_; 
v___x_3630_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(v_s_3574_, v_s_x27_3575_);
return v___x_3630_;
}
case 2:
{
lean_object* v___x_3631_; 
v___x_3631_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3574_, v_s_x27_3575_);
lean_dec_ref(v_s_x27_3575_);
lean_dec_ref(v_s_3574_);
return v___x_3631_;
}
case 3:
{
lean_object* v___x_3632_; 
v___x_3632_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3574_, v_s_x27_3575_);
return v___x_3632_;
}
default: 
{
uint8_t v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
lean_dec_ref(v_s_3574_);
v___x_3633_ = 0;
v___x_3634_ = lean_box(v___x_3633_);
v___x_3635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3634_);
lean_ctor_set(v___x_3635_, 1, v_s_x27_3575_);
v___x_3636_ = lean_unsigned_to_nat(1u);
v___x_3637_ = lean_mk_empty_array_with_capacity(v___x_3636_);
v___x_3638_ = lean_array_push(v___x_3637_, v___x_3635_);
return v___x_3638_;
}
}
v___jp_3577_:
{
if (v___y_3581_ == 0)
{
uint8_t v___x_3582_; 
lean_dec_ref(v___y_3579_);
v___x_3582_ = lean_nat_dec_le(v___y_3578_, v___y_3580_);
lean_dec(v___y_3580_);
lean_dec(v___y_3578_);
if (v___x_3582_ == 0)
{
lean_object* v___x_3583_; 
v___x_3583_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3574_, v_s_x27_3575_);
return v___x_3583_;
}
else
{
lean_object* v___x_3584_; 
v___x_3584_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3574_, v_s_x27_3575_);
lean_dec_ref(v_s_x27_3575_);
lean_dec_ref(v_s_3574_);
return v___x_3584_;
}
}
else
{
size_t v_sz_3585_; size_t v___x_3586_; lean_object* v___x_3587_; 
lean_dec(v___y_3580_);
lean_dec(v___y_3578_);
lean_dec_ref(v_s_x27_3575_);
lean_dec_ref(v_s_3574_);
v_sz_3585_ = lean_array_size(v___y_3579_);
v___x_3586_ = ((size_t)0ULL);
v___x_3587_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_3585_, v___x_3586_, v___y_3579_);
return v___x_3587_;
}
}
v___jp_3588_:
{
lean_object* v_approxEditDistance_3593_; lean_object* v_charArrDiff_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; uint8_t v___x_3597_; 
v_approxEditDistance_3593_ = lean_array_get_size(v___y_3592_);
lean_dec_ref(v___y_3592_);
v_charArrDiff_3594_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v___y_3589_);
lean_dec_ref(v___y_3589_);
v___x_3595_ = lean_array_get_size(v_charArrDiff_3594_);
v___x_3596_ = lean_unsigned_to_nat(3u);
v___x_3597_ = lean_nat_dec_le(v___x_3595_, v___x_3596_);
if (v___x_3597_ == 0)
{
uint8_t v___x_3598_; 
v___x_3598_ = lean_nat_dec_le(v_approxEditDistance_3593_, v___y_3590_);
lean_dec(v___y_3590_);
v___y_3578_ = v_approxEditDistance_3593_;
v___y_3579_ = v_charArrDiff_3594_;
v___y_3580_ = v___y_3591_;
v___y_3581_ = v___x_3598_;
goto v___jp_3577_;
}
else
{
lean_dec(v___y_3590_);
v___y_3578_ = v_approxEditDistance_3593_;
v___y_3579_ = v_charArrDiff_3594_;
v___y_3580_ = v___y_3591_;
v___y_3581_ = v___x_3597_;
goto v___jp_3577_;
}
}
v___jp_3599_:
{
lean_object* v___x_3604_; lean_object* v_maxWordDiffDistance_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v_charDiffRaw_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; uint8_t v___x_3612_; 
v___x_3604_ = lean_nat_shiftr(v___y_3603_, v___y_3601_);
lean_dec(v___y_3603_);
v_maxWordDiffDistance_3605_ = lean_nat_add(v___y_3600_, v___x_3604_);
lean_dec(v___x_3604_);
lean_dec(v___y_3600_);
lean_inc_ref(v_s_3574_);
v___x_3606_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3574_);
lean_inc_ref(v_s_x27_3575_);
v___x_3607_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3575_);
v_charDiffRaw_3608_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3606_, v___x_3607_);
v___x_3609_ = lean_unsigned_to_nat(0u);
v___x_3610_ = lean_array_get_size(v_charDiffRaw_3608_);
v___x_3611_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0));
v___x_3612_ = lean_nat_dec_lt(v___x_3609_, v___x_3610_);
if (v___x_3612_ == 0)
{
v___y_3589_ = v_charDiffRaw_3608_;
v___y_3590_ = v___y_3602_;
v___y_3591_ = v_maxWordDiffDistance_3605_;
v___y_3592_ = v___x_3611_;
goto v___jp_3588_;
}
else
{
uint8_t v___x_3613_; 
v___x_3613_ = lean_nat_dec_le(v___x_3610_, v___x_3610_);
if (v___x_3613_ == 0)
{
if (v___x_3612_ == 0)
{
v___y_3589_ = v_charDiffRaw_3608_;
v___y_3590_ = v___y_3602_;
v___y_3591_ = v_maxWordDiffDistance_3605_;
v___y_3592_ = v___x_3611_;
goto v___jp_3588_;
}
else
{
size_t v___x_3614_; size_t v___x_3615_; lean_object* v___x_3616_; 
v___x_3614_ = ((size_t)0ULL);
v___x_3615_ = lean_usize_of_nat(v___x_3610_);
v___x_3616_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3608_, v___x_3614_, v___x_3615_, v___x_3611_);
v___y_3589_ = v_charDiffRaw_3608_;
v___y_3590_ = v___y_3602_;
v___y_3591_ = v_maxWordDiffDistance_3605_;
v___y_3592_ = v___x_3616_;
goto v___jp_3588_;
}
}
else
{
size_t v___x_3617_; size_t v___x_3618_; lean_object* v___x_3619_; 
v___x_3617_ = ((size_t)0ULL);
v___x_3618_ = lean_usize_of_nat(v___x_3610_);
v___x_3619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3608_, v___x_3617_, v___x_3618_, v___x_3611_);
v___y_3589_ = v_charDiffRaw_3608_;
v___y_3590_ = v___y_3602_;
v___y_3591_ = v_maxWordDiffDistance_3605_;
v___y_3592_ = v___x_3619_;
goto v___jp_3588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff___boxed(lean_object* v_s_3639_, lean_object* v_s_x27_3640_, lean_object* v_granularity_3641_){
_start:
{
uint8_t v_granularity_boxed_3642_; lean_object* v_res_3643_; 
v_granularity_boxed_3642_ = lean_unbox(v_granularity_3641_);
v_res_3643_ = l_Lean_Meta_Hint_readableDiff(v_s_3639_, v_s_x27_3640_, v_granularity_boxed_3642_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(lean_object* v_as_3644_, size_t v_i_3645_, size_t v_stop_3646_, lean_object* v_b_3647_){
_start:
{
uint8_t v___x_3648_; 
v___x_3648_ = lean_usize_dec_eq(v_i_3645_, v_stop_3646_);
if (v___x_3648_ == 0)
{
lean_object* v___x_3649_; lean_object* v_snd_3650_; lean_object* v___x_3651_; size_t v___x_3652_; size_t v___x_3653_; 
v___x_3649_ = lean_array_uget_borrowed(v_as_3644_, v_i_3645_);
v_snd_3650_ = lean_ctor_get(v___x_3649_, 1);
v___x_3651_ = lean_string_append(v_b_3647_, v_snd_3650_);
v___x_3652_ = ((size_t)1ULL);
v___x_3653_ = lean_usize_add(v_i_3645_, v___x_3652_);
v_i_3645_ = v___x_3653_;
v_b_3647_ = v___x_3651_;
goto _start;
}
else
{
return v_b_3647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0___boxed(lean_object* v_as_3655_, lean_object* v_i_3656_, lean_object* v_stop_3657_, lean_object* v_b_3658_){
_start:
{
size_t v_i_boxed_3659_; size_t v_stop_boxed_3660_; lean_object* v_res_3661_; 
v_i_boxed_3659_ = lean_unbox_usize(v_i_3656_);
lean_dec(v_i_3656_);
v_stop_boxed_3660_ = lean_unbox_usize(v_stop_3657_);
lean_dec(v_stop_3657_);
v_res_3661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v_as_3655_, v_i_boxed_3659_, v_stop_boxed_3660_, v_b_3658_);
lean_dec_ref(v_as_3655_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(lean_object* v_t_3662_, lean_object* v___y_3663_){
_start:
{
lean_object* v___x_3665_; lean_object* v_infoState_3666_; uint8_t v_enabled_3667_; 
v___x_3665_ = lean_st_ref_get(v___y_3663_);
v_infoState_3666_ = lean_ctor_get(v___x_3665_, 7);
lean_inc_ref(v_infoState_3666_);
lean_dec(v___x_3665_);
v_enabled_3667_ = lean_ctor_get_uint8(v_infoState_3666_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3666_);
if (v_enabled_3667_ == 0)
{
lean_object* v___x_3668_; lean_object* v___x_3669_; 
lean_dec_ref(v_t_3662_);
v___x_3668_ = lean_box(0);
v___x_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3668_);
return v___x_3669_;
}
else
{
lean_object* v___x_3670_; lean_object* v_infoState_3671_; lean_object* v_env_3672_; lean_object* v_nextMacroScope_3673_; lean_object* v_ngen_3674_; lean_object* v_auxDeclNGen_3675_; lean_object* v_traceState_3676_; lean_object* v_cache_3677_; lean_object* v_messages_3678_; lean_object* v_snapshotTasks_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3701_; 
v___x_3670_ = lean_st_ref_take(v___y_3663_);
v_infoState_3671_ = lean_ctor_get(v___x_3670_, 7);
v_env_3672_ = lean_ctor_get(v___x_3670_, 0);
v_nextMacroScope_3673_ = lean_ctor_get(v___x_3670_, 1);
v_ngen_3674_ = lean_ctor_get(v___x_3670_, 2);
v_auxDeclNGen_3675_ = lean_ctor_get(v___x_3670_, 3);
v_traceState_3676_ = lean_ctor_get(v___x_3670_, 4);
v_cache_3677_ = lean_ctor_get(v___x_3670_, 5);
v_messages_3678_ = lean_ctor_get(v___x_3670_, 6);
v_snapshotTasks_3679_ = lean_ctor_get(v___x_3670_, 8);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3681_ = v___x_3670_;
v_isShared_3682_ = v_isSharedCheck_3701_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_snapshotTasks_3679_);
lean_inc(v_infoState_3671_);
lean_inc(v_messages_3678_);
lean_inc(v_cache_3677_);
lean_inc(v_traceState_3676_);
lean_inc(v_auxDeclNGen_3675_);
lean_inc(v_ngen_3674_);
lean_inc(v_nextMacroScope_3673_);
lean_inc(v_env_3672_);
lean_dec(v___x_3670_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3701_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
uint8_t v_enabled_3683_; lean_object* v_assignment_3684_; lean_object* v_lazyAssignment_3685_; lean_object* v_trees_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3700_; 
v_enabled_3683_ = lean_ctor_get_uint8(v_infoState_3671_, sizeof(void*)*3);
v_assignment_3684_ = lean_ctor_get(v_infoState_3671_, 0);
v_lazyAssignment_3685_ = lean_ctor_get(v_infoState_3671_, 1);
v_trees_3686_ = lean_ctor_get(v_infoState_3671_, 2);
v_isSharedCheck_3700_ = !lean_is_exclusive(v_infoState_3671_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3688_ = v_infoState_3671_;
v_isShared_3689_ = v_isSharedCheck_3700_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_trees_3686_);
lean_inc(v_lazyAssignment_3685_);
lean_inc(v_assignment_3684_);
lean_dec(v_infoState_3671_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3700_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3690_; lean_object* v___x_3692_; 
v___x_3690_ = l_Lean_PersistentArray_push___redArg(v_trees_3686_, v_t_3662_);
if (v_isShared_3689_ == 0)
{
lean_ctor_set(v___x_3688_, 2, v___x_3690_);
v___x_3692_ = v___x_3688_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_assignment_3684_);
lean_ctor_set(v_reuseFailAlloc_3699_, 1, v_lazyAssignment_3685_);
lean_ctor_set(v_reuseFailAlloc_3699_, 2, v___x_3690_);
lean_ctor_set_uint8(v_reuseFailAlloc_3699_, sizeof(void*)*3, v_enabled_3683_);
v___x_3692_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
lean_object* v___x_3694_; 
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 7, v___x_3692_);
v___x_3694_ = v___x_3681_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_env_3672_);
lean_ctor_set(v_reuseFailAlloc_3698_, 1, v_nextMacroScope_3673_);
lean_ctor_set(v_reuseFailAlloc_3698_, 2, v_ngen_3674_);
lean_ctor_set(v_reuseFailAlloc_3698_, 3, v_auxDeclNGen_3675_);
lean_ctor_set(v_reuseFailAlloc_3698_, 4, v_traceState_3676_);
lean_ctor_set(v_reuseFailAlloc_3698_, 5, v_cache_3677_);
lean_ctor_set(v_reuseFailAlloc_3698_, 6, v_messages_3678_);
lean_ctor_set(v_reuseFailAlloc_3698_, 7, v___x_3692_);
lean_ctor_set(v_reuseFailAlloc_3698_, 8, v_snapshotTasks_3679_);
v___x_3694_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; 
v___x_3695_ = lean_st_ref_put(v___y_3663_, v___x_3694_);
v___x_3696_ = lean_box(0);
v___x_3697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3696_);
return v___x_3697_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg___boxed(lean_object* v_t_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
lean_object* v_res_3705_; 
v_res_3705_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3702_, v___y_3703_);
lean_dec(v___y_3703_);
return v_res_3705_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
v___x_3706_ = lean_unsigned_to_nat(32u);
v___x_3707_ = lean_mk_empty_array_with_capacity(v___x_3706_);
v___x_3708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3707_);
return v___x_3708_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1(void){
_start:
{
size_t v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; 
v___x_3709_ = ((size_t)5ULL);
v___x_3710_ = lean_unsigned_to_nat(0u);
v___x_3711_ = lean_unsigned_to_nat(32u);
v___x_3712_ = lean_mk_empty_array_with_capacity(v___x_3711_);
v___x_3713_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0);
v___x_3714_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3714_, 0, v___x_3713_);
lean_ctor_set(v___x_3714_, 1, v___x_3712_);
lean_ctor_set(v___x_3714_, 2, v___x_3710_);
lean_ctor_set(v___x_3714_, 3, v___x_3710_);
lean_ctor_set_usize(v___x_3714_, 4, v___x_3709_);
return v___x_3714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(lean_object* v_t_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
lean_object* v___x_3719_; lean_object* v_infoState_3720_; uint8_t v_enabled_3721_; 
v___x_3719_ = lean_st_ref_get(v___y_3717_);
v_infoState_3720_ = lean_ctor_get(v___x_3719_, 7);
lean_inc_ref(v_infoState_3720_);
lean_dec(v___x_3719_);
v_enabled_3721_ = lean_ctor_get_uint8(v_infoState_3720_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3720_);
if (v_enabled_3721_ == 0)
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
lean_dec_ref(v_t_3715_);
v___x_3722_ = lean_box(0);
v___x_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
return v___x_3723_;
}
else
{
lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3724_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1);
v___x_3725_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3725_, 0, v_t_3715_);
lean_ctor_set(v___x_3725_, 1, v___x_3724_);
v___x_3726_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v___x_3725_, v___y_3717_);
return v___x_3726_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___boxed(lean_object* v_t_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v_t_3727_, v___y_3728_, v___y_3729_);
lean_dec(v___y_3729_);
lean_dec_ref(v___y_3728_);
return v_res_3731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0(lean_object* v___x_3732_, lean_object* v___y_3733_){
_start:
{
lean_object* v___x_3734_; 
v___x_3734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3732_);
lean_ctor_set(v___x_3734_, 1, v___y_3733_);
return v___x_3734_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3736_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__0));
v___x_3737_ = l_Lean_stringToMessageData(v___x_3736_);
return v___x_3737_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3739_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__2));
v___x_3740_ = l_Lean_stringToMessageData(v___x_3739_);
return v___x_3740_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29(void){
_start:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3789_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__28));
v___x_3790_ = l_Lean_Json_mkObj(v___x_3789_);
return v___x_3790_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30(void){
_start:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
v___x_3791_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29);
v___x_3792_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__19));
v___x_3793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3793_, 0, v___x_3792_);
lean_ctor_set(v___x_3793_, 1, v___x_3791_);
return v___x_3793_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31(void){
_start:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3794_ = lean_box(0);
v___x_3795_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30);
v___x_3796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3795_);
lean_ctor_set(v___x_3796_, 1, v___x_3794_);
return v___x_3796_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33(void){
_start:
{
lean_object* v___x_3799_; lean_object* v___x_3800_; 
v___x_3799_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__32));
v___x_3800_ = l_Lean_MessageData_ofFormat(v___x_3799_);
return v___x_3800_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35(void){
_start:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3802_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__34));
v___x_3803_ = l_Lean_stringToMessageData(v___x_3802_);
return v___x_3803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(lean_object* v_suggestions_3805_, uint8_t v_forceList_3806_, lean_object* v_codeActionPrefix_x3f_3807_, lean_object* v_ref_3808_, lean_object* v_as_3809_, size_t v_sz_3810_, size_t v_i_3811_, lean_object* v_b_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_){
_start:
{
lean_object* v_a_3817_; lean_object* v___y_3822_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3833_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; uint8_t v___x_3861_; 
v___x_3861_ = lean_usize_dec_lt(v_i_3811_, v_sz_3810_);
if (v___x_3861_ == 0)
{
lean_object* v___x_3862_; 
lean_dec(v_ref_3808_);
lean_dec(v_codeActionPrefix_x3f_3807_);
v___x_3862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3862_, 0, v_b_3812_);
return v___x_3862_;
}
else
{
lean_object* v_a_3863_; lean_object* v_span_x3f_3864_; lean_object* v___x_3865_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; uint8_t v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; uint8_t v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; uint8_t v___y_3953_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; uint8_t v___y_3962_; uint8_t v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3966_; lean_object* v___y_3967_; lean_object* v___y_3968_; lean_object* v_postInfo_x3f_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; uint8_t v___y_3972_; uint8_t v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; uint8_t v___y_3981_; uint8_t v___y_3982_; lean_object* v_edits_3983_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; uint8_t v___y_3995_; uint8_t v___y_3996_; lean_object* v_stop_3997_; lean_object* v_edits_3998_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; uint8_t v___y_4013_; uint8_t v___y_4014_; lean_object* v___y_4015_; lean_object* v_edits_4016_; lean_object* v___y_4017_; lean_object* v___x_4041_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; uint8_t v___y_4050_; uint8_t v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; uint8_t v___y_4093_; uint8_t v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4106_; 
v_a_3863_ = lean_array_uget_borrowed(v_as_3809_, v_i_3811_);
v_span_x3f_3864_ = lean_ctor_get(v_a_3863_, 1);
v___x_3865_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_4041_ = l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_;
if (lean_obj_tag(v_span_x3f_3864_) == 0)
{
lean_inc(v_ref_3808_);
v___y_4106_ = v_ref_3808_;
goto v___jp_4105_;
}
else
{
lean_object* v_val_4127_; 
v_val_4127_ = lean_ctor_get(v_span_x3f_3864_, 0);
lean_inc(v_val_4127_);
v___y_4106_ = v_val_4127_;
goto v___jp_4105_;
}
v___jp_3866_:
{
lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___f_3887_; 
lean_inc_ref(v___y_3867_);
v___x_3873_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson(v___y_3867_);
v___x_3874_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__9));
v___x_3875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3874_);
lean_ctor_set(v___x_3875_, 1, v___x_3873_);
v___x_3876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3877_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3877_, 0, v___y_3870_);
v___x_3878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3878_, 0, v___x_3876_);
lean_ctor_set(v___x_3878_, 1, v___x_3877_);
v___x_3879_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3880_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3869_);
v___x_3881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3879_);
lean_ctor_set(v___x_3881_, 1, v___x_3880_);
v___x_3882_ = lean_box(0);
v___x_3883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3881_);
lean_ctor_set(v___x_3883_, 1, v___x_3882_);
v___x_3884_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3878_);
lean_ctor_set(v___x_3884_, 1, v___x_3883_);
v___x_3885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3875_);
lean_ctor_set(v___x_3885_, 1, v___x_3884_);
v___x_3886_ = l_Lean_Json_mkObj(v___x_3885_);
lean_dec_ref_known(v___x_3885_, 2);
v___f_3887_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3887_, 0, v___x_3886_);
if (v___y_3871_ == 0)
{
lean_object* v___x_3888_; 
v___x_3888_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString(v___y_3867_);
v___y_3841_ = v___y_3872_;
v___y_3842_ = v___y_3868_;
v___y_3843_ = v___f_3887_;
v___y_3844_ = v___x_3888_;
goto v___jp_3840_;
}
else
{
lean_object* v___x_3889_; lean_object* v___x_3890_; uint8_t v___x_3891_; 
v___x_3889_ = lean_unsigned_to_nat(0u);
v___x_3890_ = lean_array_get_size(v___y_3867_);
v___x_3891_ = lean_nat_dec_lt(v___x_3889_, v___x_3890_);
if (v___x_3891_ == 0)
{
lean_dec_ref(v___y_3867_);
v___y_3841_ = v___y_3872_;
v___y_3842_ = v___y_3868_;
v___y_3843_ = v___f_3887_;
v___y_3844_ = v___x_3865_;
goto v___jp_3840_;
}
else
{
uint8_t v___x_3892_; 
v___x_3892_ = lean_nat_dec_le(v___x_3890_, v___x_3890_);
if (v___x_3892_ == 0)
{
if (v___x_3891_ == 0)
{
lean_dec_ref(v___y_3867_);
v___y_3841_ = v___y_3872_;
v___y_3842_ = v___y_3868_;
v___y_3843_ = v___f_3887_;
v___y_3844_ = v___x_3865_;
goto v___jp_3840_;
}
else
{
size_t v___x_3893_; size_t v___x_3894_; lean_object* v___x_3895_; 
v___x_3893_ = ((size_t)0ULL);
v___x_3894_ = lean_usize_of_nat(v___x_3890_);
v___x_3895_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3867_, v___x_3893_, v___x_3894_, v___x_3865_);
lean_dec_ref(v___y_3867_);
v___y_3841_ = v___y_3872_;
v___y_3842_ = v___y_3868_;
v___y_3843_ = v___f_3887_;
v___y_3844_ = v___x_3895_;
goto v___jp_3840_;
}
}
else
{
size_t v___x_3896_; size_t v___x_3897_; lean_object* v___x_3898_; 
v___x_3896_ = ((size_t)0ULL);
v___x_3897_ = lean_usize_of_nat(v___x_3890_);
v___x_3898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3867_, v___x_3896_, v___x_3897_, v___x_3865_);
lean_dec_ref(v___y_3867_);
v___y_3841_ = v___y_3872_;
v___y_3842_ = v___y_3868_;
v___y_3843_ = v___f_3887_;
v___y_3844_ = v___x_3898_;
goto v___jp_3840_;
}
}
}
}
v___jp_3899_:
{
if (lean_obj_tag(v___y_3901_) == 0)
{
lean_object* v___x_3908_; uint64_t v_javascriptHash_3909_; lean_object* v_suggestion_3910_; lean_object* v_messageData_x3f_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___f_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; 
lean_dec_ref(v___y_3900_);
v___x_3908_ = l_Lean_Meta_Hint_textInsertionWidget;
v_javascriptHash_3909_ = lean_ctor_get_uint64(v___x_3908_, sizeof(void*)*1);
v_suggestion_3910_ = lean_ctor_get(v___y_3902_, 0);
lean_inc_ref(v_suggestion_3910_);
v_messageData_x3f_3911_ = lean_ctor_get(v___y_3902_, 4);
lean_inc(v_messageData_x3f_3911_);
lean_dec_ref(v___y_3902_);
v___x_3912_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18));
v___x_3913_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3914_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3904_);
v___x_3915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3913_);
lean_ctor_set(v___x_3915_, 1, v___x_3914_);
v___x_3916_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3917_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3917_, 0, v___y_3905_);
v___x_3918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3916_);
lean_ctor_set(v___x_3918_, 1, v___x_3917_);
v___x_3919_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31);
v___x_3920_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3918_);
lean_ctor_set(v___x_3920_, 1, v___x_3919_);
v___x_3921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3915_);
lean_ctor_set(v___x_3921_, 1, v___x_3920_);
v___x_3922_ = l_Lean_Json_mkObj(v___x_3921_);
lean_dec_ref_known(v___x_3921_, 2);
v___f_3923_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3923_, 0, v___x_3922_);
v___x_3924_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3924_, 0, v___x_3912_);
lean_ctor_set(v___x_3924_, 1, v___f_3923_);
lean_ctor_set_uint64(v___x_3924_, sizeof(void*)*2, v_javascriptHash_3909_);
v___x_3925_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33);
v___x_3926_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3924_);
lean_ctor_set(v___x_3926_, 1, v___x_3925_);
v___x_3927_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3928_, 0, v___x_3927_);
lean_ctor_set(v___x_3928_, 1, v___x_3926_);
v___x_3929_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35);
v___x_3930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3928_);
lean_ctor_set(v___x_3930_, 1, v___x_3929_);
v___x_3931_ = l_Lean_stringToMessageData(v___y_3903_);
v___x_3932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3930_);
lean_ctor_set(v___x_3932_, 1, v___x_3931_);
if (lean_obj_tag(v_messageData_x3f_3911_) == 0)
{
if (lean_obj_tag(v_suggestion_3910_) == 0)
{
lean_object* v_a_3933_; lean_object* v___x_3934_; 
v_a_3933_ = lean_ctor_get(v_suggestion_3910_, 1);
lean_inc(v_a_3933_);
lean_dec_ref_known(v_suggestion_3910_, 2);
v___x_3934_ = l_Lean_MessageData_ofSyntax(v_a_3933_);
v___y_3826_ = v___x_3932_;
v___y_3827_ = v___y_3907_;
v___y_3828_ = v___x_3934_;
goto v___jp_3825_;
}
else
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3943_; 
v_a_3935_ = lean_ctor_get(v_suggestion_3910_, 0);
v_isSharedCheck_3943_ = !lean_is_exclusive(v_suggestion_3910_);
if (v_isSharedCheck_3943_ == 0)
{
v___x_3937_ = v_suggestion_3910_;
v_isShared_3938_ = v_isSharedCheck_3943_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v_suggestion_3910_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3943_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3940_; 
if (v_isShared_3938_ == 0)
{
lean_ctor_set_tag(v___x_3937_, 3);
v___x_3940_ = v___x_3937_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3942_; 
v_reuseFailAlloc_3942_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3935_);
v___x_3940_ = v_reuseFailAlloc_3942_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
lean_object* v___x_3941_; 
v___x_3941_ = l_Lean_MessageData_ofFormat(v___x_3940_);
v___y_3826_ = v___x_3932_;
v___y_3827_ = v___y_3907_;
v___y_3828_ = v___x_3941_;
goto v___jp_3825_;
}
}
}
}
else
{
lean_object* v_val_3944_; 
lean_dec_ref(v_suggestion_3910_);
v_val_3944_ = lean_ctor_get(v_messageData_x3f_3911_, 0);
lean_inc(v_val_3944_);
lean_dec_ref_known(v_messageData_x3f_3911_, 1);
v___y_3826_ = v___x_3932_;
v___y_3827_ = v___y_3907_;
v___y_3828_ = v_val_3944_;
goto v___jp_3825_;
}
}
else
{
lean_dec_ref_known(v___y_3901_, 1);
lean_dec_ref(v___y_3902_);
v___y_3867_ = v___y_3900_;
v___y_3868_ = v___y_3903_;
v___y_3869_ = v___y_3904_;
v___y_3870_ = v___y_3905_;
v___y_3871_ = v___y_3906_;
v___y_3872_ = v___y_3907_;
goto v___jp_3866_;
}
}
v___jp_3945_:
{
if (v___y_3953_ == 0)
{
lean_object* v_messageData_x3f_3954_; 
v_messageData_x3f_3954_ = lean_ctor_get(v___y_3948_, 4);
if (lean_obj_tag(v_messageData_x3f_3954_) == 0)
{
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
v___y_3867_ = v___y_3946_;
v___y_3868_ = v___y_3949_;
v___y_3869_ = v___y_3950_;
v___y_3870_ = v___y_3951_;
v___y_3871_ = v___y_3953_;
v___y_3872_ = v___y_3952_;
goto v___jp_3866_;
}
else
{
v___y_3900_ = v___y_3946_;
v___y_3901_ = v___y_3947_;
v___y_3902_ = v___y_3948_;
v___y_3903_ = v___y_3949_;
v___y_3904_ = v___y_3950_;
v___y_3905_ = v___y_3951_;
v___y_3906_ = v___y_3953_;
v___y_3907_ = v___y_3952_;
goto v___jp_3899_;
}
}
else
{
v___y_3900_ = v___y_3946_;
v___y_3901_ = v___y_3947_;
v___y_3902_ = v___y_3948_;
v___y_3903_ = v___y_3949_;
v___y_3904_ = v___y_3950_;
v___y_3905_ = v___y_3951_;
v___y_3906_ = v___y_3953_;
v___y_3907_ = v___y_3952_;
goto v___jp_3899_;
}
}
v___jp_3955_:
{
if (v___y_3963_ == 4)
{
v___y_3946_ = v___y_3956_;
v___y_3947_ = v___y_3957_;
v___y_3948_ = v___y_3958_;
v___y_3949_ = v___y_3959_;
v___y_3950_ = v___y_3960_;
v___y_3951_ = v___y_3961_;
v___y_3952_ = v___y_3964_;
v___y_3953_ = v___x_3861_;
goto v___jp_3945_;
}
else
{
v___y_3946_ = v___y_3956_;
v___y_3947_ = v___y_3957_;
v___y_3948_ = v___y_3958_;
v___y_3949_ = v___y_3959_;
v___y_3950_ = v___y_3960_;
v___y_3951_ = v___y_3961_;
v___y_3952_ = v___y_3964_;
v___y_3953_ = v___y_3962_;
goto v___jp_3945_;
}
}
v___jp_3965_:
{
if (lean_obj_tag(v_postInfo_x3f_3969_) == 0)
{
v___y_3956_ = v___y_3966_;
v___y_3957_ = v___y_3967_;
v___y_3958_ = v___y_3968_;
v___y_3959_ = v___y_3974_;
v___y_3960_ = v___y_3970_;
v___y_3961_ = v___y_3971_;
v___y_3962_ = v___y_3972_;
v___y_3963_ = v___y_3973_;
v___y_3964_ = v___x_3865_;
goto v___jp_3955_;
}
else
{
lean_object* v_val_3975_; 
v_val_3975_ = lean_ctor_get(v_postInfo_x3f_3969_, 0);
lean_inc(v_val_3975_);
lean_dec_ref_known(v_postInfo_x3f_3969_, 1);
v___y_3956_ = v___y_3966_;
v___y_3957_ = v___y_3967_;
v___y_3958_ = v___y_3968_;
v___y_3959_ = v___y_3974_;
v___y_3960_ = v___y_3970_;
v___y_3961_ = v___y_3971_;
v___y_3962_ = v___y_3972_;
v___y_3963_ = v___y_3973_;
v___y_3964_ = v_val_3975_;
goto v___jp_3955_;
}
}
v___jp_3976_:
{
lean_object* v_preInfo_x3f_3984_; 
v_preInfo_x3f_3984_ = lean_ctor_get(v___y_3978_, 1);
if (lean_obj_tag(v_preInfo_x3f_3984_) == 0)
{
lean_object* v_postInfo_x3f_3985_; 
v_postInfo_x3f_3985_ = lean_ctor_get(v___y_3978_, 2);
lean_inc(v_postInfo_x3f_3985_);
v___y_3966_ = v_edits_3983_;
v___y_3967_ = v___y_3977_;
v___y_3968_ = v___y_3978_;
v_postInfo_x3f_3969_ = v_postInfo_x3f_3985_;
v___y_3970_ = v___y_3979_;
v___y_3971_ = v___y_3980_;
v___y_3972_ = v___y_3981_;
v___y_3973_ = v___y_3982_;
v___y_3974_ = v___x_3865_;
goto v___jp_3965_;
}
else
{
lean_object* v_postInfo_x3f_3986_; lean_object* v_val_3987_; 
v_postInfo_x3f_3986_ = lean_ctor_get(v___y_3978_, 2);
lean_inc(v_postInfo_x3f_3986_);
v_val_3987_ = lean_ctor_get(v_preInfo_x3f_3984_, 0);
lean_inc(v_val_3987_);
v___y_3966_ = v_edits_3983_;
v___y_3967_ = v___y_3977_;
v___y_3968_ = v___y_3978_;
v_postInfo_x3f_3969_ = v_postInfo_x3f_3986_;
v___y_3970_ = v___y_3979_;
v___y_3971_ = v___y_3980_;
v___y_3972_ = v___y_3981_;
v___y_3973_ = v___y_3982_;
v___y_3974_ = v_val_3987_;
goto v___jp_3965_;
}
}
v___jp_3988_:
{
uint8_t v___x_3999_; 
v___x_3999_ = lean_nat_dec_lt(v___y_3992_, v_stop_3997_);
if (v___x_3999_ == 0)
{
lean_dec(v_stop_3997_);
lean_dec(v___y_3992_);
v___y_3977_ = v___y_3989_;
v___y_3978_ = v___y_3990_;
v___y_3979_ = v___y_3993_;
v___y_3980_ = v___y_3994_;
v___y_3981_ = v___y_3995_;
v___y_3982_ = v___y_3996_;
v_edits_3983_ = v_edits_3998_;
goto v___jp_3976_;
}
else
{
lean_object* v_source_4000_; uint8_t v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; lean_object* v___x_4005_; 
v_source_4000_ = lean_ctor_get(v___y_3991_, 0);
v___x_4001_ = 2;
v___x_4002_ = lean_string_utf8_extract(v_source_4000_, v___y_3992_, v_stop_3997_);
lean_dec(v_stop_3997_);
lean_dec(v___y_3992_);
v___x_4003_ = lean_box(v___x_4001_);
v___x_4004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4004_, 0, v___x_4003_);
lean_ctor_set(v___x_4004_, 1, v___x_4002_);
v___x_4005_ = lean_array_push(v_edits_3998_, v___x_4004_);
v___y_3977_ = v___y_3989_;
v___y_3978_ = v___y_3990_;
v___y_3979_ = v___y_3993_;
v___y_3980_ = v___y_3994_;
v___y_3981_ = v___y_3995_;
v___y_3982_ = v___y_3996_;
v_edits_3983_ = v___x_4005_;
goto v___jp_3976_;
}
}
v___jp_4006_:
{
if (lean_obj_tag(v___y_4007_) == 0)
{
lean_dec_ref(v___y_4015_);
lean_dec(v___y_4010_);
lean_dec(v___y_4009_);
v___y_3977_ = v___y_4007_;
v___y_3978_ = v___y_4008_;
v___y_3979_ = v___y_4011_;
v___y_3980_ = v___y_4012_;
v___y_3981_ = v___y_4013_;
v___y_3982_ = v___y_4014_;
v_edits_3983_ = v_edits_4016_;
goto v___jp_3976_;
}
else
{
lean_object* v_val_4018_; lean_object* v___x_4019_; 
v_val_4018_ = lean_ctor_get(v___y_4007_, 0);
v___x_4019_ = l_Lean_Syntax_getRange_x3f(v_val_4018_, v___y_4013_);
if (lean_obj_tag(v___x_4019_) == 1)
{
lean_object* v_val_4020_; uint8_t v___x_4021_; 
v_val_4020_ = lean_ctor_get(v___x_4019_, 0);
lean_inc(v_val_4020_);
lean_dec_ref_known(v___x_4019_, 1);
v___x_4021_ = l_Lean_Syntax_Range_includes(v_val_4020_, v___y_4015_, v___y_4013_, v___y_4013_);
lean_dec_ref(v___y_4015_);
if (v___x_4021_ == 0)
{
lean_dec(v_val_4020_);
lean_dec(v___y_4010_);
lean_dec(v___y_4009_);
v___y_3977_ = v___y_4007_;
v___y_3978_ = v___y_4008_;
v___y_3979_ = v___y_4011_;
v___y_3980_ = v___y_4012_;
v___y_3981_ = v___y_4013_;
v___y_3982_ = v___y_4014_;
v_edits_3983_ = v_edits_4016_;
goto v___jp_3976_;
}
else
{
lean_object* v_fileMap_4022_; lean_object* v_start_4023_; lean_object* v_stop_4024_; lean_object* v___x_4026_; uint8_t v_isShared_4027_; uint8_t v_isSharedCheck_4040_; 
v_fileMap_4022_ = lean_ctor_get(v___y_4017_, 1);
v_start_4023_ = lean_ctor_get(v_val_4020_, 0);
v_stop_4024_ = lean_ctor_get(v_val_4020_, 1);
v_isSharedCheck_4040_ = !lean_is_exclusive(v_val_4020_);
if (v_isSharedCheck_4040_ == 0)
{
v___x_4026_ = v_val_4020_;
v_isShared_4027_ = v_isSharedCheck_4040_;
goto v_resetjp_4025_;
}
else
{
lean_inc(v_stop_4024_);
lean_inc(v_start_4023_);
lean_dec(v_val_4020_);
v___x_4026_ = lean_box(0);
v_isShared_4027_ = v_isSharedCheck_4040_;
goto v_resetjp_4025_;
}
v_resetjp_4025_:
{
uint8_t v___x_4028_; 
v___x_4028_ = lean_nat_dec_lt(v_start_4023_, v___y_4009_);
if (v___x_4028_ == 0)
{
lean_del_object(v___x_4026_);
lean_dec(v_start_4023_);
lean_dec(v___y_4009_);
v___y_3989_ = v___y_4007_;
v___y_3990_ = v___y_4008_;
v___y_3991_ = v_fileMap_4022_;
v___y_3992_ = v___y_4010_;
v___y_3993_ = v___y_4011_;
v___y_3994_ = v___y_4012_;
v___y_3995_ = v___y_4013_;
v___y_3996_ = v___y_4014_;
v_stop_3997_ = v_stop_4024_;
v_edits_3998_ = v_edits_4016_;
goto v___jp_3988_;
}
else
{
lean_object* v_source_4029_; uint8_t v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4034_; 
v_source_4029_ = lean_ctor_get(v_fileMap_4022_, 0);
v___x_4030_ = 2;
v___x_4031_ = lean_string_utf8_extract(v_source_4029_, v_start_4023_, v___y_4009_);
lean_dec(v___y_4009_);
lean_dec(v_start_4023_);
v___x_4032_ = lean_box(v___x_4030_);
if (v_isShared_4027_ == 0)
{
lean_ctor_set(v___x_4026_, 1, v___x_4031_);
lean_ctor_set(v___x_4026_, 0, v___x_4032_);
v___x_4034_ = v___x_4026_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v___x_4032_);
lean_ctor_set(v_reuseFailAlloc_4039_, 1, v___x_4031_);
v___x_4034_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4035_ = lean_unsigned_to_nat(1u);
v___x_4036_ = lean_mk_empty_array_with_capacity(v___x_4035_);
v___x_4037_ = lean_array_push(v___x_4036_, v___x_4034_);
v___x_4038_ = l_Array_append___redArg(v___x_4037_, v_edits_4016_);
lean_dec_ref(v_edits_4016_);
v___y_3989_ = v___y_4007_;
v___y_3990_ = v___y_4008_;
v___y_3991_ = v_fileMap_4022_;
v___y_3992_ = v___y_4010_;
v___y_3993_ = v___y_4011_;
v___y_3994_ = v___y_4012_;
v___y_3995_ = v___y_4013_;
v___y_3996_ = v___y_4014_;
v_stop_3997_ = v_stop_4024_;
v_edits_3998_ = v___x_4038_;
goto v___jp_3988_;
}
}
}
}
}
else
{
lean_dec(v___x_4019_);
lean_dec_ref(v___y_4015_);
lean_dec(v___y_4010_);
lean_dec(v___y_4009_);
v___y_3977_ = v___y_4007_;
v___y_3978_ = v___y_4008_;
v___y_3979_ = v___y_4011_;
v___y_3980_ = v___y_4012_;
v___y_3981_ = v___y_4013_;
v___y_3982_ = v___y_4014_;
v_edits_3983_ = v_edits_4016_;
goto v___jp_3976_;
}
}
}
v___jp_4042_:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; 
lean_inc_ref(v___y_4043_);
v___x_4053_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4053_, 0, v___y_4046_);
lean_ctor_set(v___x_4053_, 1, v___y_4052_);
lean_ctor_set(v___x_4053_, 2, v___y_4043_);
v___x_4054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4041_);
lean_ctor_set(v___x_4054_, 1, v___x_4053_);
v___x_4055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4055_, 0, v___y_4045_);
lean_ctor_set(v___x_4055_, 1, v___x_4054_);
v___x_4056_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4055_);
v___x_4057_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v___x_4056_, v___y_3813_, v___y_3814_);
if (lean_obj_tag(v___x_4057_) == 0)
{
lean_object* v_messageData_x3f_4058_; 
lean_dec_ref_known(v___x_4057_, 1);
v_messageData_x3f_4058_ = lean_ctor_get(v___y_4043_, 4);
if (lean_obj_tag(v_messageData_x3f_4058_) == 1)
{
lean_object* v_start_4059_; lean_object* v_stop_4060_; lean_object* v_val_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; uint8_t v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
v_start_4059_ = lean_ctor_get(v___y_4048_, 0);
lean_inc(v_start_4059_);
v_stop_4060_ = lean_ctor_get(v___y_4048_, 1);
lean_inc(v_stop_4060_);
v_val_4061_ = lean_ctor_get(v_messageData_x3f_4058_, 0);
v___x_4062_ = lean_box(0);
lean_inc(v_val_4061_);
v___x_4063_ = l_Lean_MessageData_format(v_val_4061_, v___x_4062_);
v___x_4064_ = 0;
v___x_4065_ = l_Std_Format_defWidth;
v___x_4066_ = lean_unsigned_to_nat(0u);
v___x_4067_ = l_Std_Format_pretty(v___x_4063_, v___x_4065_, v___x_4066_, v___x_4066_);
v___x_4068_ = lean_box(v___x_4064_);
v___x_4069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4069_, 0, v___x_4068_);
lean_ctor_set(v___x_4069_, 1, v___x_4067_);
v___x_4070_ = lean_unsigned_to_nat(1u);
v___x_4071_ = lean_mk_empty_array_with_capacity(v___x_4070_);
v___x_4072_ = lean_array_push(v___x_4071_, v___x_4069_);
v___y_4007_ = v___y_4044_;
v___y_4008_ = v___y_4043_;
v___y_4009_ = v_start_4059_;
v___y_4010_ = v_stop_4060_;
v___y_4011_ = v___y_4047_;
v___y_4012_ = v___y_4049_;
v___y_4013_ = v___y_4050_;
v___y_4014_ = v___y_4051_;
v___y_4015_ = v___y_4048_;
v_edits_4016_ = v___x_4072_;
v___y_4017_ = v___y_3813_;
goto v___jp_4006_;
}
else
{
lean_object* v_fileMap_4073_; lean_object* v_start_4074_; lean_object* v_stop_4075_; lean_object* v_source_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; 
v_fileMap_4073_ = lean_ctor_get(v___y_3813_, 1);
v_start_4074_ = lean_ctor_get(v___y_4048_, 0);
lean_inc(v_start_4074_);
v_stop_4075_ = lean_ctor_get(v___y_4048_, 1);
lean_inc(v_stop_4075_);
v_source_4076_ = lean_ctor_get(v_fileMap_4073_, 0);
v___x_4077_ = lean_string_utf8_extract(v_source_4076_, v_start_4074_, v_stop_4075_);
lean_inc_ref(v___y_4049_);
v___x_4078_ = l_Lean_Meta_Hint_readableDiff(v___x_4077_, v___y_4049_, v___y_4051_);
v___y_4007_ = v___y_4044_;
v___y_4008_ = v___y_4043_;
v___y_4009_ = v_start_4074_;
v___y_4010_ = v_stop_4075_;
v___y_4011_ = v___y_4047_;
v___y_4012_ = v___y_4049_;
v___y_4013_ = v___y_4050_;
v___y_4014_ = v___y_4051_;
v___y_4015_ = v___y_4048_;
v_edits_4016_ = v___x_4078_;
v___y_4017_ = v___y_3813_;
goto v___jp_4006_;
}
}
else
{
lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4086_; 
lean_dec_ref(v___y_4049_);
lean_dec_ref(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec_ref(v_b_3812_);
lean_dec(v_ref_3808_);
lean_dec(v_codeActionPrefix_x3f_3807_);
v_a_4079_ = lean_ctor_get(v___x_4057_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4057_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4081_ = v___x_4057_;
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v___x_4057_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4084_; 
if (v_isShared_4082_ == 0)
{
v___x_4084_ = v___x_4081_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_4079_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
}
v___jp_4087_:
{
lean_object* v_toCodeActionTitle_x3f_4097_; lean_object* v___x_4098_; 
v_toCodeActionTitle_x3f_4097_ = lean_ctor_get(v___y_4089_, 5);
v___x_4098_ = l_Lean_Syntax_ofRange(v___y_4096_, v___x_3861_);
if (lean_obj_tag(v_toCodeActionTitle_x3f_4097_) == 0)
{
if (lean_obj_tag(v_codeActionPrefix_x3f_3807_) == 0)
{
lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4099_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__36));
v___x_4100_ = lean_string_append(v___x_4099_, v___y_4092_);
v___y_4043_ = v___y_4089_;
v___y_4044_ = v___y_4088_;
v___y_4045_ = v___x_4098_;
v___y_4046_ = v___y_4090_;
v___y_4047_ = v___y_4091_;
v___y_4048_ = v___y_4095_;
v___y_4049_ = v___y_4092_;
v___y_4050_ = v___y_4093_;
v___y_4051_ = v___y_4094_;
v___y_4052_ = v___x_4100_;
goto v___jp_4042_;
}
else
{
lean_object* v_val_4101_; lean_object* v___x_4102_; 
v_val_4101_ = lean_ctor_get(v_codeActionPrefix_x3f_3807_, 0);
lean_inc(v_val_4101_);
v___x_4102_ = lean_string_append(v_val_4101_, v___y_4092_);
v___y_4043_ = v___y_4089_;
v___y_4044_ = v___y_4088_;
v___y_4045_ = v___x_4098_;
v___y_4046_ = v___y_4090_;
v___y_4047_ = v___y_4091_;
v___y_4048_ = v___y_4095_;
v___y_4049_ = v___y_4092_;
v___y_4050_ = v___y_4093_;
v___y_4051_ = v___y_4094_;
v___y_4052_ = v___x_4102_;
goto v___jp_4042_;
}
}
else
{
lean_object* v_val_4103_; lean_object* v___x_4104_; 
v_val_4103_ = lean_ctor_get(v_toCodeActionTitle_x3f_4097_, 0);
lean_inc(v_val_4103_);
lean_inc_ref(v___y_4092_);
v___x_4104_ = lean_apply_1(v_val_4103_, v___y_4092_);
v___y_4043_ = v___y_4089_;
v___y_4044_ = v___y_4088_;
v___y_4045_ = v___x_4098_;
v___y_4046_ = v___y_4090_;
v___y_4047_ = v___y_4091_;
v___y_4048_ = v___y_4095_;
v___y_4049_ = v___y_4092_;
v___y_4050_ = v___y_4093_;
v___y_4051_ = v___y_4094_;
v___y_4052_ = v___x_4104_;
goto v___jp_4042_;
}
}
v___jp_4105_:
{
uint8_t v___x_4107_; lean_object* v___x_4108_; 
v___x_4107_ = 0;
v___x_4108_ = l_Lean_Syntax_getRange_x3f(v___y_4106_, v___x_4107_);
lean_dec(v___y_4106_);
if (lean_obj_tag(v___x_4108_) == 1)
{
lean_object* v_val_4109_; lean_object* v_toTryThisSuggestion_4110_; lean_object* v_previewSpan_x3f_4111_; uint8_t v_diffGranularity_4112_; lean_object* v___x_4113_; 
v_val_4109_ = lean_ctor_get(v___x_4108_, 0);
lean_inc_n(v_val_4109_, 2);
lean_dec_ref_known(v___x_4108_, 1);
v_toTryThisSuggestion_4110_ = lean_ctor_get(v_a_3863_, 0);
v_previewSpan_x3f_4111_ = lean_ctor_get(v_a_3863_, 2);
v_diffGranularity_4112_ = lean_ctor_get_uint8(v_a_3863_, sizeof(void*)*3);
lean_inc_ref(v_toTryThisSuggestion_4110_);
v___x_4113_ = l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(v_toTryThisSuggestion_4110_, v_val_4109_, v___y_3813_, v___y_3814_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_object* v_a_4114_; lean_object* v_range_4115_; lean_object* v_newText_4116_; lean_object* v___x_4117_; 
v_a_4114_ = lean_ctor_get(v___x_4113_, 0);
lean_inc(v_a_4114_);
lean_dec_ref_known(v___x_4113_, 1);
v_range_4115_ = lean_ctor_get(v_a_4114_, 0);
lean_inc_ref(v_range_4115_);
v_newText_4116_ = lean_ctor_get(v_a_4114_, 1);
lean_inc_ref(v_newText_4116_);
v___x_4117_ = l_Lean_Syntax_getRange_x3f(v_ref_3808_, v___x_4107_);
if (lean_obj_tag(v___x_4117_) == 0)
{
lean_inc(v_val_4109_);
lean_inc_ref(v_toTryThisSuggestion_4110_);
lean_inc(v_previewSpan_x3f_4111_);
v___y_4088_ = v_previewSpan_x3f_4111_;
v___y_4089_ = v_toTryThisSuggestion_4110_;
v___y_4090_ = v_a_4114_;
v___y_4091_ = v_range_4115_;
v___y_4092_ = v_newText_4116_;
v___y_4093_ = v___x_4107_;
v___y_4094_ = v_diffGranularity_4112_;
v___y_4095_ = v_val_4109_;
v___y_4096_ = v_val_4109_;
goto v___jp_4087_;
}
else
{
lean_object* v_val_4118_; 
v_val_4118_ = lean_ctor_get(v___x_4117_, 0);
lean_inc(v_val_4118_);
lean_dec_ref_known(v___x_4117_, 1);
lean_inc_ref(v_toTryThisSuggestion_4110_);
lean_inc(v_previewSpan_x3f_4111_);
v___y_4088_ = v_previewSpan_x3f_4111_;
v___y_4089_ = v_toTryThisSuggestion_4110_;
v___y_4090_ = v_a_4114_;
v___y_4091_ = v_range_4115_;
v___y_4092_ = v_newText_4116_;
v___y_4093_ = v___x_4107_;
v___y_4094_ = v_diffGranularity_4112_;
v___y_4095_ = v_val_4109_;
v___y_4096_ = v_val_4118_;
goto v___jp_4087_;
}
}
else
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4126_; 
lean_dec(v_val_4109_);
lean_dec_ref(v_b_3812_);
lean_dec(v_ref_3808_);
lean_dec(v_codeActionPrefix_x3f_3807_);
v_a_4119_ = lean_ctor_get(v___x_4113_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4113_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4121_ = v___x_4113_;
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4113_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4122_ == 0)
{
v___x_4124_ = v___x_4121_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4119_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
}
}
else
{
lean_dec(v___x_4108_);
v_a_3817_ = v_b_3812_;
goto v___jp_3816_;
}
}
}
v___jp_3816_:
{
size_t v___x_3818_; size_t v___x_3819_; 
v___x_3818_ = ((size_t)1ULL);
v___x_3819_ = lean_usize_add(v_i_3811_, v___x_3818_);
v_i_3811_ = v___x_3819_;
v_b_3812_ = v_a_3817_;
goto _start;
}
v___jp_3821_:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3823_ = l_Lean_MessageData_nestD(v___y_3822_);
v___x_3824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3824_, 0, v_b_3812_);
lean_ctor_set(v___x_3824_, 1, v___x_3823_);
v_a_3817_ = v___x_3824_;
goto v___jp_3816_;
}
v___jp_3825_:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3829_, 0, v___y_3826_);
lean_ctor_set(v___x_3829_, 1, v___y_3828_);
v___x_3830_ = l_Lean_stringToMessageData(v___y_3827_);
v___x_3831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3831_, 0, v___x_3829_);
lean_ctor_set(v___x_3831_, 1, v___x_3830_);
v___y_3822_ = v___x_3831_;
goto v___jp_3821_;
}
v___jp_3832_:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3834_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3835_ = lean_unsigned_to_nat(2u);
v___x_3836_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3);
v___x_3837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3837_, 0, v___x_3836_);
lean_ctor_set(v___x_3837_, 1, v___y_3833_);
v___x_3838_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3835_);
lean_ctor_set(v___x_3838_, 1, v___x_3837_);
v___x_3839_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3839_, 0, v___x_3834_);
lean_ctor_set(v___x_3839_, 1, v___x_3838_);
v___y_3822_ = v___x_3839_;
goto v___jp_3821_;
}
v___jp_3840_:
{
lean_object* v___x_3845_; uint64_t v_javascriptHash_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; uint8_t v___x_3858_; 
v___x_3845_ = l_Lean_Meta_Hint_tryThisDiffWidget;
v_javascriptHash_3846_ = lean_ctor_get_uint64(v___x_3845_, sizeof(void*)*1);
v___x_3847_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8));
v___x_3848_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3848_, 0, v___x_3847_);
lean_ctor_set(v___x_3848_, 1, v___y_3843_);
lean_ctor_set_uint64(v___x_3848_, sizeof(void*)*2, v_javascriptHash_3846_);
v___x_3849_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3849_, 0, v___y_3844_);
v___x_3850_ = l_Lean_MessageData_ofFormat(v___x_3849_);
v___x_3851_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3848_);
lean_ctor_set(v___x_3851_, 1, v___x_3850_);
v___x_3852_ = l_Lean_stringToMessageData(v___y_3842_);
v___x_3853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3852_);
lean_ctor_set(v___x_3853_, 1, v___x_3851_);
v___x_3854_ = l_Lean_stringToMessageData(v___y_3841_);
v___x_3855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3853_);
lean_ctor_set(v___x_3855_, 1, v___x_3854_);
v___x_3856_ = lean_array_get_size(v_suggestions_3805_);
v___x_3857_ = lean_unsigned_to_nat(1u);
v___x_3858_ = lean_nat_dec_eq(v___x_3856_, v___x_3857_);
if (v___x_3858_ == 0)
{
v___y_3833_ = v___x_3855_;
goto v___jp_3832_;
}
else
{
if (v_forceList_3806_ == 0)
{
if (v___x_3858_ == 0)
{
v___y_3833_ = v___x_3855_;
goto v___jp_3832_;
}
else
{
lean_object* v___x_3859_; lean_object* v___x_3860_; 
v___x_3859_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3860_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3860_, 0, v___x_3859_);
lean_ctor_set(v___x_3860_, 1, v___x_3855_);
v___y_3822_ = v___x_3860_;
goto v___jp_3821_;
}
}
else
{
v___y_3833_ = v___x_3855_;
goto v___jp_3832_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___boxed(lean_object* v_suggestions_4128_, lean_object* v_forceList_4129_, lean_object* v_codeActionPrefix_x3f_4130_, lean_object* v_ref_4131_, lean_object* v_as_4132_, lean_object* v_sz_4133_, lean_object* v_i_4134_, lean_object* v_b_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_){
_start:
{
uint8_t v_forceList_boxed_4139_; size_t v_sz_boxed_4140_; size_t v_i_boxed_4141_; lean_object* v_res_4142_; 
v_forceList_boxed_4139_ = lean_unbox(v_forceList_4129_);
v_sz_boxed_4140_ = lean_unbox_usize(v_sz_4133_);
lean_dec(v_sz_4133_);
v_i_boxed_4141_ = lean_unbox_usize(v_i_4134_);
lean_dec(v_i_4134_);
v_res_4142_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_4128_, v_forceList_boxed_4139_, v_codeActionPrefix_x3f_4130_, v_ref_4131_, v_as_4132_, v_sz_boxed_4140_, v_i_boxed_4141_, v_b_4135_, v___y_4136_, v___y_4137_);
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4136_);
lean_dec_ref(v_as_4132_);
lean_dec_ref(v_suggestions_4128_);
return v_res_4142_;
}
}
static lean_object* _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0(void){
_start:
{
lean_object* v___x_4143_; lean_object* v_msg_4144_; 
v___x_4143_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v_msg_4144_ = l_Lean_stringToMessageData(v___x_4143_);
return v_msg_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage(lean_object* v_suggestions_4145_, lean_object* v_ref_4146_, lean_object* v_codeActionPrefix_x3f_4147_, uint8_t v_forceList_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_){
_start:
{
lean_object* v_msg_4152_; size_t v_sz_4153_; size_t v___x_4154_; lean_object* v___x_4155_; 
v_msg_4152_ = lean_obj_once(&l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0, &l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0_once, _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0);
v_sz_4153_ = lean_array_size(v_suggestions_4145_);
v___x_4154_ = ((size_t)0ULL);
v___x_4155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_4145_, v_forceList_4148_, v_codeActionPrefix_x3f_4147_, v_ref_4146_, v_suggestions_4145_, v_sz_4153_, v___x_4154_, v_msg_4152_, v_a_4149_, v_a_4150_);
return v___x_4155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage___boxed(lean_object* v_suggestions_4156_, lean_object* v_ref_4157_, lean_object* v_codeActionPrefix_x3f_4158_, lean_object* v_forceList_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_){
_start:
{
uint8_t v_forceList_boxed_4163_; lean_object* v_res_4164_; 
v_forceList_boxed_4163_ = lean_unbox(v_forceList_4159_);
v_res_4164_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_4156_, v_ref_4157_, v_codeActionPrefix_x3f_4158_, v_forceList_boxed_4163_, v_a_4160_, v_a_4161_);
lean_dec(v_a_4161_);
lean_dec_ref(v_a_4160_);
lean_dec_ref(v_suggestions_4156_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(lean_object* v_t_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
lean_object* v___x_4169_; 
v___x_4169_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_4165_, v___y_4167_);
return v___x_4169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___boxed(lean_object* v_t_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(v_t_4170_, v___y_4171_, v___y_4172_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
return v_res_4174_;
}
}
static lean_object* _init_l_Lean_MessageData_hint___closed__3(void){
_start:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4179_ = ((lean_object*)(l_Lean_MessageData_hint___closed__2));
v___x_4180_ = l_Lean_stringToMessageData(v___x_4179_);
return v___x_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint(lean_object* v_hint_4181_, lean_object* v_suggestions_4182_, lean_object* v_ref_x3f_4183_, lean_object* v_codeActionPrefix_x3f_4184_, uint8_t v_forceList_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_){
_start:
{
lean_object* v___y_4190_; 
if (lean_obj_tag(v_ref_x3f_4183_) == 0)
{
lean_object* v_ref_4205_; 
v_ref_4205_ = lean_ctor_get(v_a_4186_, 5);
lean_inc(v_ref_4205_);
v___y_4190_ = v_ref_4205_;
goto v___jp_4189_;
}
else
{
lean_object* v_val_4206_; 
v_val_4206_ = lean_ctor_get(v_ref_x3f_4183_, 0);
lean_inc(v_val_4206_);
lean_dec_ref_known(v_ref_x3f_4183_, 1);
v___y_4190_ = v_val_4206_;
goto v___jp_4189_;
}
v___jp_4189_:
{
lean_object* v___x_4191_; 
v___x_4191_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_4182_, v___y_4190_, v_codeActionPrefix_x3f_4184_, v_forceList_4185_, v_a_4186_, v_a_4187_);
if (lean_obj_tag(v___x_4191_) == 0)
{
lean_object* v_a_4192_; lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4204_; 
v_a_4192_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4204_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4204_ == 0)
{
v___x_4194_ = v___x_4191_;
v_isShared_4195_ = v_isSharedCheck_4204_;
goto v_resetjp_4193_;
}
else
{
lean_inc(v_a_4192_);
lean_dec(v___x_4191_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4204_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4202_; 
v___x_4196_ = ((lean_object*)(l_Lean_MessageData_hint___closed__1));
v___x_4197_ = lean_obj_once(&l_Lean_MessageData_hint___closed__3, &l_Lean_MessageData_hint___closed__3_once, _init_l_Lean_MessageData_hint___closed__3);
v___x_4198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4198_, 0, v___x_4197_);
lean_ctor_set(v___x_4198_, 1, v_hint_4181_);
v___x_4199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4198_);
lean_ctor_set(v___x_4199_, 1, v_a_4192_);
v___x_4200_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4200_, 0, v___x_4196_);
lean_ctor_set(v___x_4200_, 1, v___x_4199_);
if (v_isShared_4195_ == 0)
{
lean_ctor_set(v___x_4194_, 0, v___x_4200_);
v___x_4202_ = v___x_4194_;
goto v_reusejp_4201_;
}
else
{
lean_object* v_reuseFailAlloc_4203_; 
v_reuseFailAlloc_4203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4203_, 0, v___x_4200_);
v___x_4202_ = v_reuseFailAlloc_4203_;
goto v_reusejp_4201_;
}
v_reusejp_4201_:
{
return v___x_4202_;
}
}
}
else
{
lean_dec_ref(v_hint_4181_);
return v___x_4191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint___boxed(lean_object* v_hint_4207_, lean_object* v_suggestions_4208_, lean_object* v_ref_x3f_4209_, lean_object* v_codeActionPrefix_x3f_4210_, lean_object* v_forceList_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_){
_start:
{
uint8_t v_forceList_boxed_4215_; lean_object* v_res_4216_; 
v_forceList_boxed_4215_ = lean_unbox(v_forceList_4211_);
v_res_4216_ = l_Lean_MessageData_hint(v_hint_4207_, v_suggestions_4208_, v_ref_x3f_4209_, v_codeActionPrefix_x3f_4210_, v_forceList_boxed_4215_, v_a_4212_, v_a_4213_);
lean_dec(v_a_4213_);
lean_dec_ref(v_a_4212_);
lean_dec_ref(v_suggestions_4208_);
return v_res_4216_;
}
}
lean_object* runtime_initialize_Lean_Meta_TryThis(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Diff(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Hint(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Diff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Hint_textInsertionWidget = _init_l_Lean_Meta_Hint_textInsertionWidget();
lean_mark_persistent(l_Lean_Meta_Hint_textInsertionWidget);
l_Lean_Meta_Hint_tryThisDiffWidget = _init_l_Lean_Meta_Hint_tryThisDiffWidget();
lean_mark_persistent(l_Lean_Meta_Hint_tryThisDiffWidget);
l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0___boxed__const__1 = _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0___boxed__const__1);
l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0___boxed__const__1 = _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0___boxed__const__1);
l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1 = _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1();
lean_mark_persistent(l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Hint(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_TryThis(uint8_t builtin);
lean_object* initialize_Lean_Util_Diff(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Hint(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_TryThis(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Diff(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Hint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Hint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Hint(builtin);
}
#ifdef __cplusplus
}
#endif
