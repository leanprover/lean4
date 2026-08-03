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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint32_to_uint64(uint32_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Diff_instBEqAction_beq(uint8_t, uint8_t);
lean_object* l_Lean_Json_mkObj(lean_object*);
uint64_t lean_string_hash(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_data(lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_drop___redArg(lean_object*, lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* l_Subarray_take___redArg(lean_object*, lean_object*);
lean_object* l_Subarray_split___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_format(lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0;
static lean_once_cell_t l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg(lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12(lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24(lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0 = (const lean_object*)&l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0;
static lean_once_cell_t l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__0 = (const lean_object*)&l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__0_value;
static const lean_ctor_object l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__0_value),((lean_object*)&l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__1_value)}};
static const lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__1 = (const lean_object*)&l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(lean_object* v___x_483_, lean_object* v_original_484_, lean_object* v_a_485_){
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
v___x_495_ = 1;
v___x_496_ = lean_array_fget_borrowed(v_original_484_, v_snd_487_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg___boxed(lean_object* v___x_507_, lean_object* v_original_508_, lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_507_, v_original_508_, v_a_509_);
lean_dec_ref(v_original_508_);
lean_dec(v___x_507_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg(uint32_t v_a_511_, lean_object* v_x_512_){
_start:
{
if (lean_obj_tag(v_x_512_) == 0)
{
lean_object* v___x_513_; 
v___x_513_ = lean_box(0);
return v___x_513_;
}
else
{
lean_object* v_key_514_; lean_object* v_value_515_; lean_object* v_tail_516_; uint32_t v___x_517_; uint8_t v___x_518_; 
v_key_514_ = lean_ctor_get(v_x_512_, 0);
v_value_515_ = lean_ctor_get(v_x_512_, 1);
v_tail_516_ = lean_ctor_get(v_x_512_, 2);
v___x_517_ = lean_unbox_uint32(v_key_514_);
v___x_518_ = lean_uint32_dec_eq(v___x_517_, v_a_511_);
if (v___x_518_ == 0)
{
v_x_512_ = v_tail_516_;
goto _start;
}
else
{
lean_object* v___x_520_; 
lean_inc(v_value_515_);
v___x_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_520_, 0, v_value_515_);
return v___x_520_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg___boxed(lean_object* v_a_521_, lean_object* v_x_522_){
_start:
{
uint32_t v_a_boxed_523_; lean_object* v_res_524_; 
v_a_boxed_523_ = lean_unbox_uint32(v_a_521_);
lean_dec(v_a_521_);
v_res_524_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg(v_a_boxed_523_, v_x_522_);
lean_dec(v_x_522_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(lean_object* v_m_525_, uint32_t v_a_526_){
_start:
{
lean_object* v_buckets_527_; lean_object* v___x_528_; uint64_t v___x_529_; uint64_t v___x_530_; uint64_t v___x_531_; uint64_t v_fold_532_; uint64_t v___x_533_; uint64_t v___x_534_; uint64_t v___x_535_; size_t v___x_536_; size_t v___x_537_; size_t v___x_538_; size_t v___x_539_; size_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v_buckets_527_ = lean_ctor_get(v_m_525_, 1);
v___x_528_ = lean_array_get_size(v_buckets_527_);
v___x_529_ = lean_uint32_to_uint64(v_a_526_);
v___x_530_ = 32ULL;
v___x_531_ = lean_uint64_shift_right(v___x_529_, v___x_530_);
v_fold_532_ = lean_uint64_xor(v___x_529_, v___x_531_);
v___x_533_ = 16ULL;
v___x_534_ = lean_uint64_shift_right(v_fold_532_, v___x_533_);
v___x_535_ = lean_uint64_xor(v_fold_532_, v___x_534_);
v___x_536_ = lean_uint64_to_usize(v___x_535_);
v___x_537_ = lean_usize_of_nat(v___x_528_);
v___x_538_ = ((size_t)1ULL);
v___x_539_ = lean_usize_sub(v___x_537_, v___x_538_);
v___x_540_ = lean_usize_land(v___x_536_, v___x_539_);
v___x_541_ = lean_array_uget_borrowed(v_buckets_527_, v___x_540_);
v___x_542_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg(v_a_526_, v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg___boxed(lean_object* v_m_543_, lean_object* v_a_544_){
_start:
{
uint32_t v_a_boxed_545_; lean_object* v_res_546_; 
v_a_boxed_545_ = lean_unbox_uint32(v_a_544_);
lean_dec(v_a_544_);
v_res_546_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(v_m_543_, v_a_boxed_545_);
lean_dec_ref(v_m_543_);
return v_res_546_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg(uint32_t v_a_547_, lean_object* v_x_548_){
_start:
{
if (lean_obj_tag(v_x_548_) == 0)
{
uint8_t v___x_549_; 
v___x_549_ = 0;
return v___x_549_;
}
else
{
lean_object* v_key_550_; lean_object* v_tail_551_; uint32_t v___x_552_; uint8_t v___x_553_; 
v_key_550_ = lean_ctor_get(v_x_548_, 0);
v_tail_551_ = lean_ctor_get(v_x_548_, 2);
v___x_552_ = lean_unbox_uint32(v_key_550_);
v___x_553_ = lean_uint32_dec_eq(v___x_552_, v_a_547_);
if (v___x_553_ == 0)
{
v_x_548_ = v_tail_551_;
goto _start;
}
else
{
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg___boxed(lean_object* v_a_555_, lean_object* v_x_556_){
_start:
{
uint32_t v_a_boxed_557_; uint8_t v_res_558_; lean_object* v_r_559_; 
v_a_boxed_557_ = lean_unbox_uint32(v_a_555_);
lean_dec(v_a_555_);
v_res_558_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg(v_a_boxed_557_, v_x_556_);
lean_dec(v_x_556_);
v_r_559_ = lean_box(v_res_558_);
return v_r_559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(uint32_t v_a_560_, lean_object* v_b_561_, lean_object* v_x_562_){
_start:
{
if (lean_obj_tag(v_x_562_) == 0)
{
lean_dec(v_b_561_);
return v_x_562_;
}
else
{
lean_object* v_key_563_; lean_object* v_value_564_; lean_object* v_tail_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_579_; 
v_key_563_ = lean_ctor_get(v_x_562_, 0);
v_value_564_ = lean_ctor_get(v_x_562_, 1);
v_tail_565_ = lean_ctor_get(v_x_562_, 2);
v_isSharedCheck_579_ = !lean_is_exclusive(v_x_562_);
if (v_isSharedCheck_579_ == 0)
{
v___x_567_ = v_x_562_;
v_isShared_568_ = v_isSharedCheck_579_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_tail_565_);
lean_inc(v_value_564_);
lean_inc(v_key_563_);
lean_dec(v_x_562_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_579_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
uint32_t v___x_569_; uint8_t v___x_570_; 
v___x_569_ = lean_unbox_uint32(v_key_563_);
v___x_570_ = lean_uint32_dec_eq(v___x_569_, v_a_560_);
if (v___x_570_ == 0)
{
lean_object* v___x_571_; lean_object* v___x_573_; 
v___x_571_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(v_a_560_, v_b_561_, v_tail_565_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 2, v___x_571_);
v___x_573_ = v___x_567_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_key_563_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_value_564_);
lean_ctor_set(v_reuseFailAlloc_574_, 2, v___x_571_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
else
{
lean_object* v___x_575_; lean_object* v___x_577_; 
lean_dec(v_value_564_);
lean_dec(v_key_563_);
v___x_575_ = lean_box_uint32(v_a_560_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 1, v_b_561_);
lean_ctor_set(v___x_567_, 0, v___x_575_);
v___x_577_ = v___x_567_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v_b_561_);
lean_ctor_set(v_reuseFailAlloc_578_, 2, v_tail_565_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg___boxed(lean_object* v_a_580_, lean_object* v_b_581_, lean_object* v_x_582_){
_start:
{
uint32_t v_a_boxed_583_; lean_object* v_res_584_; 
v_a_boxed_583_ = lean_unbox_uint32(v_a_580_);
lean_dec(v_a_580_);
v_res_584_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(v_a_boxed_583_, v_b_581_, v_x_582_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29___redArg(lean_object* v_x_585_, lean_object* v_x_586_){
_start:
{
if (lean_obj_tag(v_x_586_) == 0)
{
return v_x_585_;
}
else
{
lean_object* v_key_587_; lean_object* v_value_588_; lean_object* v_tail_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_613_; 
v_key_587_ = lean_ctor_get(v_x_586_, 0);
v_value_588_ = lean_ctor_get(v_x_586_, 1);
v_tail_589_ = lean_ctor_get(v_x_586_, 2);
v_isSharedCheck_613_ = !lean_is_exclusive(v_x_586_);
if (v_isSharedCheck_613_ == 0)
{
v___x_591_ = v_x_586_;
v_isShared_592_ = v_isSharedCheck_613_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_tail_589_);
lean_inc(v_value_588_);
lean_inc(v_key_587_);
lean_dec(v_x_586_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_613_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_593_; uint32_t v___x_594_; uint64_t v___x_595_; uint64_t v___x_596_; uint64_t v___x_597_; uint64_t v_fold_598_; uint64_t v___x_599_; uint64_t v___x_600_; uint64_t v___x_601_; size_t v___x_602_; size_t v___x_603_; size_t v___x_604_; size_t v___x_605_; size_t v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_593_ = lean_array_get_size(v_x_585_);
v___x_594_ = lean_unbox_uint32(v_key_587_);
v___x_595_ = lean_uint32_to_uint64(v___x_594_);
v___x_596_ = 32ULL;
v___x_597_ = lean_uint64_shift_right(v___x_595_, v___x_596_);
v_fold_598_ = lean_uint64_xor(v___x_595_, v___x_597_);
v___x_599_ = 16ULL;
v___x_600_ = lean_uint64_shift_right(v_fold_598_, v___x_599_);
v___x_601_ = lean_uint64_xor(v_fold_598_, v___x_600_);
v___x_602_ = lean_uint64_to_usize(v___x_601_);
v___x_603_ = lean_usize_of_nat(v___x_593_);
v___x_604_ = ((size_t)1ULL);
v___x_605_ = lean_usize_sub(v___x_603_, v___x_604_);
v___x_606_ = lean_usize_land(v___x_602_, v___x_605_);
v___x_607_ = lean_array_uget_borrowed(v_x_585_, v___x_606_);
lean_inc(v___x_607_);
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 2, v___x_607_);
v___x_609_ = v___x_591_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_key_587_);
lean_ctor_set(v_reuseFailAlloc_612_, 1, v_value_588_);
lean_ctor_set(v_reuseFailAlloc_612_, 2, v___x_607_);
v___x_609_ = v_reuseFailAlloc_612_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_610_; 
v___x_610_ = lean_array_uset(v_x_585_, v___x_606_, v___x_609_);
v_x_585_ = v___x_610_;
v_x_586_ = v_tail_589_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28___redArg(lean_object* v_i_614_, lean_object* v_source_615_, lean_object* v_target_616_){
_start:
{
lean_object* v___x_617_; uint8_t v___x_618_; 
v___x_617_ = lean_array_get_size(v_source_615_);
v___x_618_ = lean_nat_dec_lt(v_i_614_, v___x_617_);
if (v___x_618_ == 0)
{
lean_dec_ref(v_source_615_);
lean_dec(v_i_614_);
return v_target_616_;
}
else
{
lean_object* v_es_619_; lean_object* v___x_620_; lean_object* v_source_621_; lean_object* v_target_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
v_es_619_ = lean_array_fget(v_source_615_, v_i_614_);
v___x_620_ = lean_box(0);
v_source_621_ = lean_array_fset(v_source_615_, v_i_614_, v___x_620_);
v_target_622_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29___redArg(v_target_616_, v_es_619_);
v___x_623_ = lean_unsigned_to_nat(1u);
v___x_624_ = lean_nat_add(v_i_614_, v___x_623_);
lean_dec(v_i_614_);
v_i_614_ = v___x_624_;
v_source_615_ = v_source_621_;
v_target_616_ = v_target_622_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23___redArg(lean_object* v_data_626_){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v_nbuckets_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_627_ = lean_array_get_size(v_data_626_);
v___x_628_ = lean_unsigned_to_nat(2u);
v_nbuckets_629_ = lean_nat_mul(v___x_627_, v___x_628_);
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_box(0);
v___x_632_ = lean_mk_array(v_nbuckets_629_, v___x_631_);
v___x_633_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28___redArg(v___x_630_, v_data_626_, v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(lean_object* v_m_634_, uint32_t v_a_635_, lean_object* v_b_636_){
_start:
{
lean_object* v_size_637_; lean_object* v_buckets_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_682_; 
v_size_637_ = lean_ctor_get(v_m_634_, 0);
v_buckets_638_ = lean_ctor_get(v_m_634_, 1);
v_isSharedCheck_682_ = !lean_is_exclusive(v_m_634_);
if (v_isSharedCheck_682_ == 0)
{
v___x_640_ = v_m_634_;
v_isShared_641_ = v_isSharedCheck_682_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_buckets_638_);
lean_inc(v_size_637_);
lean_dec(v_m_634_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_682_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; uint64_t v___x_643_; uint64_t v___x_644_; uint64_t v___x_645_; uint64_t v_fold_646_; uint64_t v___x_647_; uint64_t v___x_648_; uint64_t v___x_649_; size_t v___x_650_; size_t v___x_651_; size_t v___x_652_; size_t v___x_653_; size_t v___x_654_; lean_object* v_bkt_655_; uint8_t v___x_656_; 
v___x_642_ = lean_array_get_size(v_buckets_638_);
v___x_643_ = lean_uint32_to_uint64(v_a_635_);
v___x_644_ = 32ULL;
v___x_645_ = lean_uint64_shift_right(v___x_643_, v___x_644_);
v_fold_646_ = lean_uint64_xor(v___x_643_, v___x_645_);
v___x_647_ = 16ULL;
v___x_648_ = lean_uint64_shift_right(v_fold_646_, v___x_647_);
v___x_649_ = lean_uint64_xor(v_fold_646_, v___x_648_);
v___x_650_ = lean_uint64_to_usize(v___x_649_);
v___x_651_ = lean_usize_of_nat(v___x_642_);
v___x_652_ = ((size_t)1ULL);
v___x_653_ = lean_usize_sub(v___x_651_, v___x_652_);
v___x_654_ = lean_usize_land(v___x_650_, v___x_653_);
v_bkt_655_ = lean_array_uget_borrowed(v_buckets_638_, v___x_654_);
v___x_656_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg(v_a_635_, v_bkt_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; lean_object* v_size_x27_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v_buckets_x27_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_657_ = lean_unsigned_to_nat(1u);
v_size_x27_658_ = lean_nat_add(v_size_637_, v___x_657_);
lean_dec(v_size_637_);
v___x_659_ = lean_box_uint32(v_a_635_);
lean_inc(v_bkt_655_);
v___x_660_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v_b_636_);
lean_ctor_set(v___x_660_, 2, v_bkt_655_);
v_buckets_x27_661_ = lean_array_uset(v_buckets_638_, v___x_654_, v___x_660_);
v___x_662_ = lean_unsigned_to_nat(4u);
v___x_663_ = lean_nat_mul(v_size_x27_658_, v___x_662_);
v___x_664_ = lean_unsigned_to_nat(3u);
v___x_665_ = lean_nat_div(v___x_663_, v___x_664_);
lean_dec(v___x_663_);
v___x_666_ = lean_array_get_size(v_buckets_x27_661_);
v___x_667_ = lean_nat_dec_le(v___x_665_, v___x_666_);
lean_dec(v___x_665_);
if (v___x_667_ == 0)
{
lean_object* v_val_668_; lean_object* v___x_670_; 
v_val_668_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23___redArg(v_buckets_x27_661_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v_val_668_);
lean_ctor_set(v___x_640_, 0, v_size_x27_658_);
v___x_670_ = v___x_640_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_size_x27_658_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_val_668_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
else
{
lean_object* v___x_673_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v_buckets_x27_661_);
lean_ctor_set(v___x_640_, 0, v_size_x27_658_);
v___x_673_ = v___x_640_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_size_x27_658_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_buckets_x27_661_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
else
{
lean_object* v___x_675_; lean_object* v_buckets_x27_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_680_; 
lean_inc(v_bkt_655_);
v___x_675_ = lean_box(0);
v_buckets_x27_676_ = lean_array_uset(v_buckets_638_, v___x_654_, v___x_675_);
v___x_677_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(v_a_635_, v_b_636_, v_bkt_655_);
v___x_678_ = lean_array_uset(v_buckets_x27_676_, v___x_654_, v___x_677_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 1, v___x_678_);
v___x_680_ = v___x_640_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_size_637_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v___x_678_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg___boxed(lean_object* v_m_683_, lean_object* v_a_684_, lean_object* v_b_685_){
_start:
{
uint32_t v_a_boxed_686_; lean_object* v_res_687_; 
v_a_boxed_686_ = lean_unbox_uint32(v_a_684_);
lean_dec(v_a_684_);
v_res_687_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_m_683_, v_a_boxed_686_, v_b_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(lean_object* v_histogram_688_, lean_object* v_index_689_, uint32_t v_val_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(v_histogram_688_, v_val_690_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_692_ = lean_unsigned_to_nat(0u);
v___x_693_ = lean_box(0);
v___x_694_ = lean_unsigned_to_nat(1u);
v___x_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_695_, 0, v_index_689_);
v___x_696_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_696_, 0, v___x_692_);
lean_ctor_set(v___x_696_, 1, v___x_693_);
lean_ctor_set(v___x_696_, 2, v___x_694_);
lean_ctor_set(v___x_696_, 3, v___x_695_);
v___x_697_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_histogram_688_, v_val_690_, v___x_696_);
return v___x_697_;
}
else
{
lean_object* v_val_698_; lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_719_; 
v_val_698_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_719_ == 0)
{
v___x_700_ = v___x_691_;
v_isShared_701_ = v_isSharedCheck_719_;
goto v_resetjp_699_;
}
else
{
lean_inc(v_val_698_);
lean_dec(v___x_691_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_719_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v_leftCount_702_; lean_object* v_leftIndex_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_716_; 
v_leftCount_702_ = lean_ctor_get(v_val_698_, 0);
v_leftIndex_703_ = lean_ctor_get(v_val_698_, 1);
v_isSharedCheck_716_ = !lean_is_exclusive(v_val_698_);
if (v_isSharedCheck_716_ == 0)
{
lean_object* v_unused_717_; lean_object* v_unused_718_; 
v_unused_717_ = lean_ctor_get(v_val_698_, 3);
lean_dec(v_unused_717_);
v_unused_718_ = lean_ctor_get(v_val_698_, 2);
lean_dec(v_unused_718_);
v___x_705_ = v_val_698_;
v_isShared_706_ = v_isSharedCheck_716_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_leftIndex_703_);
lean_inc(v_leftCount_702_);
lean_dec(v_val_698_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_716_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_707_ = lean_unsigned_to_nat(1u);
v___x_708_ = lean_nat_add(v_leftCount_702_, v___x_707_);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 0, v_index_689_);
v___x_710_ = v___x_700_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_index_689_);
v___x_710_ = v_reuseFailAlloc_715_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_712_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 3, v___x_710_);
lean_ctor_set(v___x_705_, 2, v___x_708_);
v___x_712_ = v___x_705_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_leftCount_702_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_leftIndex_703_);
lean_ctor_set(v_reuseFailAlloc_714_, 2, v___x_708_);
lean_ctor_set(v_reuseFailAlloc_714_, 3, v___x_710_);
v___x_712_ = v_reuseFailAlloc_714_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
lean_object* v___x_713_; 
v___x_713_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_histogram_688_, v_val_690_, v___x_712_);
return v___x_713_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg___boxed(lean_object* v_histogram_720_, lean_object* v_index_721_, lean_object* v_val_722_){
_start:
{
uint32_t v_val_boxed_723_; lean_object* v_res_724_; 
v_val_boxed_723_ = lean_unbox_uint32(v_val_722_);
lean_dec(v_val_722_);
v_res_724_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(v_histogram_720_, v_index_721_, v_val_boxed_723_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(lean_object* v_upperBound_725_, lean_object* v___x_726_, lean_object* v_fst_727_, lean_object* v___x_728_, lean_object* v_a_729_, lean_object* v_b_730_){
_start:
{
uint8_t v___x_731_; 
v___x_731_ = lean_nat_dec_lt(v_a_729_, v_upperBound_725_);
if (v___x_731_ == 0)
{
lean_dec(v_a_729_);
return v_b_730_;
}
else
{
lean_object* v___x_732_; uint32_t v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_732_ = l_Subarray_get___redArg(v_fst_727_, v_a_729_);
v___x_733_ = lean_unbox_uint32(v___x_732_);
lean_dec(v___x_732_);
lean_inc(v_a_729_);
v___x_734_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(v_b_730_, v_a_729_, v___x_733_);
v___x_735_ = lean_unsigned_to_nat(1u);
v___x_736_ = lean_nat_add(v_a_729_, v___x_735_);
lean_dec(v_a_729_);
v_a_729_ = v___x_736_;
v_b_730_ = v___x_734_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg___boxed(lean_object* v_upperBound_738_, lean_object* v___x_739_, lean_object* v_fst_740_, lean_object* v___x_741_, lean_object* v_a_742_, lean_object* v_b_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(v_upperBound_738_, v___x_739_, v_fst_740_, v___x_741_, v_a_742_, v_b_743_);
lean_dec(v___x_741_);
lean_dec_ref(v_fst_740_);
lean_dec(v___x_739_);
lean_dec(v_upperBound_738_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg(lean_object* v_as_x27_745_, lean_object* v_b_746_){
_start:
{
if (lean_obj_tag(v_as_x27_745_) == 0)
{
return v_b_746_;
}
else
{
lean_object* v_head_747_; lean_object* v_snd_748_; lean_object* v_leftIndex_749_; 
v_head_747_ = lean_ctor_get(v_as_x27_745_, 0);
v_snd_748_ = lean_ctor_get(v_head_747_, 1);
v_leftIndex_749_ = lean_ctor_get(v_snd_748_, 1);
if (lean_obj_tag(v_leftIndex_749_) == 1)
{
lean_object* v_rightIndex_750_; 
v_rightIndex_750_ = lean_ctor_get(v_snd_748_, 3);
if (lean_obj_tag(v_rightIndex_750_) == 1)
{
if (lean_obj_tag(v_b_746_) == 0)
{
lean_object* v_tail_751_; lean_object* v_fst_752_; lean_object* v_leftCount_753_; lean_object* v_rightCount_754_; lean_object* v_val_755_; lean_object* v_val_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v_tail_751_ = lean_ctor_get(v_as_x27_745_, 1);
v_fst_752_ = lean_ctor_get(v_head_747_, 0);
v_leftCount_753_ = lean_ctor_get(v_snd_748_, 0);
v_rightCount_754_ = lean_ctor_get(v_snd_748_, 2);
v_val_755_ = lean_ctor_get(v_leftIndex_749_, 0);
v_val_756_ = lean_ctor_get(v_rightIndex_750_, 0);
v___x_757_ = lean_nat_add(v_leftCount_753_, v_rightCount_754_);
lean_inc(v_val_756_);
lean_inc(v_val_755_);
v___x_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_758_, 0, v_val_755_);
lean_ctor_set(v___x_758_, 1, v_val_756_);
lean_inc(v_fst_752_);
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v_fst_752_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
v___x_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_757_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
v_as_x27_745_ = v_tail_751_;
v_b_746_ = v___x_761_;
goto _start;
}
else
{
lean_object* v_val_763_; lean_object* v_tail_764_; lean_object* v_fst_765_; lean_object* v_leftCount_766_; lean_object* v_rightCount_767_; lean_object* v_val_768_; lean_object* v_val_769_; lean_object* v_fst_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_791_; 
v_val_763_ = lean_ctor_get(v_b_746_, 0);
lean_inc(v_val_763_);
v_tail_764_ = lean_ctor_get(v_as_x27_745_, 1);
v_fst_765_ = lean_ctor_get(v_head_747_, 0);
v_leftCount_766_ = lean_ctor_get(v_snd_748_, 0);
v_rightCount_767_ = lean_ctor_get(v_snd_748_, 2);
v_val_768_ = lean_ctor_get(v_leftIndex_749_, 0);
v_val_769_ = lean_ctor_get(v_rightIndex_750_, 0);
v_fst_770_ = lean_ctor_get(v_val_763_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v_val_763_);
if (v_isSharedCheck_791_ == 0)
{
lean_object* v_unused_792_; 
v_unused_792_ = lean_ctor_get(v_val_763_, 1);
lean_dec(v_unused_792_);
v___x_772_ = v_val_763_;
v_isShared_773_ = v_isSharedCheck_791_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_fst_770_);
lean_dec(v_val_763_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_791_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = lean_nat_add(v_leftCount_766_, v_rightCount_767_);
v___x_775_ = lean_nat_dec_lt(v___x_774_, v_fst_770_);
lean_dec(v_fst_770_);
if (v___x_775_ == 0)
{
lean_dec(v___x_774_);
lean_del_object(v___x_772_);
v_as_x27_745_ = v_tail_764_;
goto _start;
}
else
{
lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_789_; 
v_isSharedCheck_789_ = !lean_is_exclusive(v_b_746_);
if (v_isSharedCheck_789_ == 0)
{
lean_object* v_unused_790_; 
v_unused_790_ = lean_ctor_get(v_b_746_, 0);
lean_dec(v_unused_790_);
v___x_778_ = v_b_746_;
v_isShared_779_ = v_isSharedCheck_789_;
goto v_resetjp_777_;
}
else
{
lean_dec(v_b_746_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_789_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
lean_inc(v_val_769_);
lean_inc(v_val_768_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v_val_769_);
lean_ctor_set(v___x_772_, 0, v_val_768_);
v___x_781_ = v___x_772_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_val_768_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_val_769_);
v___x_781_ = v_reuseFailAlloc_788_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_785_; 
lean_inc(v_fst_765_);
v___x_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_782_, 0, v_fst_765_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_774_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_783_);
v___x_785_ = v___x_778_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_783_);
v___x_785_ = v_reuseFailAlloc_787_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
v_as_x27_745_ = v_tail_764_;
v_b_746_ = v___x_785_;
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
lean_object* v_tail_793_; 
v_tail_793_ = lean_ctor_get(v_as_x27_745_, 1);
v_as_x27_745_ = v_tail_793_;
goto _start;
}
}
else
{
lean_object* v_tail_795_; 
v_tail_795_ = lean_ctor_get(v_as_x27_745_, 1);
v_as_x27_745_ = v_tail_795_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_as_x27_797_, lean_object* v_b_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg(v_as_x27_797_, v_b_798_);
lean_dec(v_as_x27_797_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3_spec__4(lean_object* v_left_800_, lean_object* v_right_801_, lean_object* v_pref_802_){
_start:
{
lean_object* v_start_803_; lean_object* v_stop_804_; lean_object* v_i_805_; lean_object* v___x_811_; uint8_t v___x_812_; 
v_start_803_ = lean_ctor_get(v_left_800_, 1);
v_stop_804_ = lean_ctor_get(v_left_800_, 2);
v_i_805_ = lean_array_get_size(v_pref_802_);
v___x_811_ = lean_nat_sub(v_stop_804_, v_start_803_);
v___x_812_ = lean_nat_dec_lt(v_i_805_, v___x_811_);
lean_dec(v___x_811_);
if (v___x_812_ == 0)
{
goto v___jp_806_;
}
else
{
lean_object* v_start_813_; lean_object* v_stop_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v_start_813_ = lean_ctor_get(v_right_801_, 1);
v_stop_814_ = lean_ctor_get(v_right_801_, 2);
v___x_815_ = lean_nat_sub(v_stop_814_, v_start_813_);
v___x_816_ = lean_nat_dec_lt(v_i_805_, v___x_815_);
lean_dec(v___x_815_);
if (v___x_816_ == 0)
{
goto v___jp_806_;
}
else
{
lean_object* v___x_817_; lean_object* v___x_818_; uint32_t v___x_819_; uint32_t v___x_820_; uint8_t v___x_821_; 
v___x_817_ = l_Subarray_get___redArg(v_left_800_, v_i_805_);
v___x_818_ = l_Subarray_get___redArg(v_right_801_, v_i_805_);
v___x_819_ = lean_unbox_uint32(v___x_817_);
v___x_820_ = lean_unbox_uint32(v___x_818_);
lean_dec(v___x_818_);
v___x_821_ = lean_uint32_dec_eq(v___x_819_, v___x_820_);
if (v___x_821_ == 0)
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
lean_dec(v___x_817_);
v___x_822_ = l_Subarray_drop___redArg(v_left_800_, v_i_805_);
v___x_823_ = l_Subarray_drop___redArg(v_right_801_, v_i_805_);
v___x_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_822_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v_pref_802_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
return v___x_825_;
}
else
{
lean_object* v___x_826_; 
v___x_826_ = lean_array_push(v_pref_802_, v___x_817_);
v_pref_802_ = v___x_826_;
goto _start;
}
}
}
v___jp_806_:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_807_ = l_Subarray_drop___redArg(v_left_800_, v_i_805_);
v___x_808_ = l_Subarray_drop___redArg(v_right_801_, v_i_805_);
v___x_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_807_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v_pref_802_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
return v___x_810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3(lean_object* v_left_828_, lean_object* v_right_829_){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_831_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3_spec__4(v_left_828_, v_right_829_, v___x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(lean_object* v_a_832_, lean_object* v_b_833_){
_start:
{
lean_object* v_array_834_; lean_object* v_start_835_; lean_object* v_stop_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_849_; 
v_array_834_ = lean_ctor_get(v_a_832_, 0);
v_start_835_ = lean_ctor_get(v_a_832_, 1);
v_stop_836_ = lean_ctor_get(v_a_832_, 2);
v_isSharedCheck_849_ = !lean_is_exclusive(v_a_832_);
if (v_isSharedCheck_849_ == 0)
{
v___x_838_ = v_a_832_;
v_isShared_839_ = v_isSharedCheck_849_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_stop_836_);
lean_inc(v_start_835_);
lean_inc(v_array_834_);
lean_dec(v_a_832_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_849_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
uint8_t v___x_840_; 
v___x_840_ = lean_nat_dec_lt(v_start_835_, v_stop_836_);
if (v___x_840_ == 0)
{
lean_del_object(v___x_838_);
lean_dec(v_stop_836_);
lean_dec(v_start_835_);
lean_dec_ref(v_array_834_);
return v_b_833_;
}
else
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_841_ = lean_unsigned_to_nat(1u);
v___x_842_ = lean_nat_add(v_start_835_, v___x_841_);
lean_inc_ref(v_array_834_);
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 1, v___x_842_);
v___x_844_ = v___x_838_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_array_834_);
lean_ctor_set(v_reuseFailAlloc_848_, 1, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_848_, 2, v_stop_836_);
v___x_844_ = v_reuseFailAlloc_848_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_845_ = lean_array_fget(v_array_834_, v_start_835_);
lean_dec(v_start_835_);
lean_dec_ref(v_array_834_);
v___x_846_ = lean_array_push(v_b_833_, v___x_845_);
v_a_832_ = v___x_844_;
v_b_833_ = v___x_846_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6(lean_object* v_left_850_, lean_object* v_right_851_, lean_object* v_i_852_){
_start:
{
lean_object* v_start_853_; lean_object* v_stop_854_; lean_object* v___x_855_; uint8_t v___x_869_; 
v_start_853_ = lean_ctor_get(v_left_850_, 1);
v_stop_854_ = lean_ctor_get(v_left_850_, 2);
v___x_855_ = lean_nat_sub(v_stop_854_, v_start_853_);
v___x_869_ = lean_nat_dec_lt(v_i_852_, v___x_855_);
if (v___x_869_ == 0)
{
goto v___jp_856_;
}
else
{
lean_object* v_start_870_; lean_object* v_stop_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v_start_870_ = lean_ctor_get(v_right_851_, 1);
v_stop_871_ = lean_ctor_get(v_right_851_, 2);
v___x_872_ = lean_nat_sub(v_stop_871_, v_start_870_);
v___x_873_ = lean_nat_dec_lt(v_i_852_, v___x_872_);
if (v___x_873_ == 0)
{
lean_dec(v___x_872_);
goto v___jp_856_;
}
else
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; uint32_t v___x_881_; uint32_t v___x_882_; uint8_t v___x_883_; 
v___x_874_ = lean_nat_sub(v___x_855_, v_i_852_);
lean_dec(v___x_855_);
v___x_875_ = lean_unsigned_to_nat(1u);
v___x_876_ = lean_nat_sub(v___x_874_, v___x_875_);
v___x_877_ = l_Subarray_get___redArg(v_left_850_, v___x_876_);
lean_dec(v___x_876_);
v___x_878_ = lean_nat_sub(v___x_872_, v_i_852_);
lean_dec(v___x_872_);
v___x_879_ = lean_nat_sub(v___x_878_, v___x_875_);
v___x_880_ = l_Subarray_get___redArg(v_right_851_, v___x_879_);
lean_dec(v___x_879_);
v___x_881_ = lean_unbox_uint32(v___x_877_);
lean_dec(v___x_877_);
v___x_882_ = lean_unbox_uint32(v___x_880_);
lean_dec(v___x_880_);
v___x_883_ = lean_uint32_dec_eq(v___x_881_, v___x_882_);
if (v___x_883_ == 0)
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
lean_dec(v_i_852_);
lean_inc_ref(v_left_850_);
v___x_884_ = l_Subarray_take___redArg(v_left_850_, v___x_874_);
v___x_885_ = l_Subarray_take___redArg(v_right_851_, v___x_878_);
lean_dec(v___x_878_);
v___x_886_ = l_Subarray_drop___redArg(v_left_850_, v___x_874_);
lean_dec(v___x_874_);
v___x_887_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_888_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(v___x_886_, v___x_887_);
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_885_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_884_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
return v___x_890_;
}
else
{
lean_object* v___x_891_; 
lean_dec(v___x_878_);
lean_dec(v___x_874_);
v___x_891_ = lean_nat_add(v_i_852_, v___x_875_);
lean_dec(v_i_852_);
v_i_852_ = v___x_891_;
goto _start;
}
}
}
v___jp_856_:
{
lean_object* v_start_857_; lean_object* v_stop_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
v_start_857_ = lean_ctor_get(v_right_851_, 1);
v_stop_858_ = lean_ctor_get(v_right_851_, 2);
v___x_859_ = lean_nat_sub(v___x_855_, v_i_852_);
lean_dec(v___x_855_);
lean_inc_ref(v_left_850_);
v___x_860_ = l_Subarray_take___redArg(v_left_850_, v___x_859_);
v___x_861_ = lean_nat_sub(v_stop_858_, v_start_857_);
v___x_862_ = lean_nat_sub(v___x_861_, v_i_852_);
lean_dec(v_i_852_);
lean_dec(v___x_861_);
v___x_863_ = l_Subarray_take___redArg(v_right_851_, v___x_862_);
lean_dec(v___x_862_);
v___x_864_ = l_Subarray_drop___redArg(v_left_850_, v___x_859_);
lean_dec(v___x_859_);
v___x_865_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_866_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(v___x_864_, v___x_865_);
v___x_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_863_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
v___x_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_860_);
lean_ctor_set(v___x_868_, 1, v___x_867_);
return v___x_868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4(lean_object* v_left_893_, lean_object* v_right_894_){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6(v_left_893_, v_right_894_, v___x_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(lean_object* v_x_897_, lean_object* v_x_898_){
_start:
{
if (lean_obj_tag(v_x_898_) == 0)
{
lean_inc(v_x_897_);
return v_x_897_;
}
else
{
lean_object* v_key_899_; lean_object* v_value_900_; lean_object* v_tail_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v_key_899_ = lean_ctor_get(v_x_898_, 0);
v_value_900_ = lean_ctor_get(v_x_898_, 1);
v_tail_901_ = lean_ctor_get(v_x_898_, 2);
v___x_902_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(v_x_897_, v_tail_901_);
lean_inc(v_value_900_);
lean_inc(v_key_899_);
v___x_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_903_, 0, v_key_899_);
lean_ctor_set(v___x_903_, 1, v_value_900_);
v___x_904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_903_);
lean_ctor_set(v___x_904_, 1, v___x_902_);
return v___x_904_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6___boxed(lean_object* v_x_905_, lean_object* v_x_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(v_x_905_, v_x_906_);
lean_dec(v_x_906_);
lean_dec(v_x_905_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7(lean_object* v_as_908_, size_t v_i_909_, size_t v_stop_910_, lean_object* v_b_911_){
_start:
{
uint8_t v___x_912_; 
v___x_912_ = lean_usize_dec_eq(v_i_909_, v_stop_910_);
if (v___x_912_ == 0)
{
size_t v___x_913_; size_t v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_913_ = ((size_t)1ULL);
v___x_914_ = lean_usize_sub(v_i_909_, v___x_913_);
v___x_915_ = lean_array_uget_borrowed(v_as_908_, v___x_914_);
v___x_916_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(v_b_911_, v___x_915_);
lean_dec(v_b_911_);
v_i_909_ = v___x_914_;
v_b_911_ = v___x_916_;
goto _start;
}
else
{
return v_b_911_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7___boxed(lean_object* v_as_918_, lean_object* v_i_919_, lean_object* v_stop_920_, lean_object* v_b_921_){
_start:
{
size_t v_i_boxed_922_; size_t v_stop_boxed_923_; lean_object* v_res_924_; 
v_i_boxed_922_ = lean_unbox_usize(v_i_919_);
lean_dec(v_i_919_);
v_stop_boxed_923_ = lean_unbox_usize(v_stop_920_);
lean_dec(v_stop_920_);
v_res_924_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7(v_as_918_, v_i_boxed_922_, v_stop_boxed_923_, v_b_921_);
lean_dec_ref(v_as_918_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(lean_object* v_histogram_925_, lean_object* v_index_926_, uint32_t v_val_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(v_histogram_925_, v_val_927_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_929_ = lean_unsigned_to_nat(1u);
v___x_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_930_, 0, v_index_926_);
v___x_931_ = lean_unsigned_to_nat(0u);
v___x_932_ = lean_box(0);
v___x_933_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_933_, 0, v___x_929_);
lean_ctor_set(v___x_933_, 1, v___x_930_);
lean_ctor_set(v___x_933_, 2, v___x_931_);
lean_ctor_set(v___x_933_, 3, v___x_932_);
v___x_934_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_histogram_925_, v_val_927_, v___x_933_);
return v___x_934_;
}
else
{
lean_object* v_val_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_956_; 
v_val_935_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_956_ == 0)
{
v___x_937_ = v___x_928_;
v_isShared_938_ = v_isSharedCheck_956_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_val_935_);
lean_dec(v___x_928_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_956_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v_leftCount_939_; lean_object* v_rightCount_940_; lean_object* v_rightIndex_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_954_; 
v_leftCount_939_ = lean_ctor_get(v_val_935_, 0);
v_rightCount_940_ = lean_ctor_get(v_val_935_, 2);
v_rightIndex_941_ = lean_ctor_get(v_val_935_, 3);
v_isSharedCheck_954_ = !lean_is_exclusive(v_val_935_);
if (v_isSharedCheck_954_ == 0)
{
lean_object* v_unused_955_; 
v_unused_955_ = lean_ctor_get(v_val_935_, 1);
lean_dec(v_unused_955_);
v___x_943_ = v_val_935_;
v_isShared_944_ = v_isSharedCheck_954_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_rightIndex_941_);
lean_inc(v_rightCount_940_);
lean_inc(v_leftCount_939_);
lean_dec(v_val_935_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_954_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_945_ = lean_unsigned_to_nat(1u);
v___x_946_ = lean_nat_add(v_leftCount_939_, v___x_945_);
lean_dec(v_leftCount_939_);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v_index_926_);
v___x_948_ = v___x_937_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_index_926_);
v___x_948_ = v_reuseFailAlloc_953_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_950_; 
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v___x_948_);
lean_ctor_set(v___x_943_, 0, v___x_946_);
v___x_950_ = v___x_943_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_952_, 2, v_rightCount_940_);
lean_ctor_set(v_reuseFailAlloc_952_, 3, v_rightIndex_941_);
v___x_950_ = v_reuseFailAlloc_952_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_951_; 
v___x_951_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_histogram_925_, v_val_927_, v___x_950_);
return v___x_951_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg___boxed(lean_object* v_histogram_957_, lean_object* v_index_958_, lean_object* v_val_959_){
_start:
{
uint32_t v_val_boxed_960_; lean_object* v_res_961_; 
v_val_boxed_960_ = lean_unbox_uint32(v_val_959_);
lean_dec(v_val_959_);
v_res_961_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(v_histogram_957_, v_index_958_, v_val_boxed_960_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg(lean_object* v_upperBound_962_, lean_object* v_fst_963_, lean_object* v___x_964_, lean_object* v_fst_965_, lean_object* v_a_966_, lean_object* v_b_967_){
_start:
{
uint8_t v___x_968_; 
v___x_968_ = lean_nat_dec_lt(v_a_966_, v_upperBound_962_);
if (v___x_968_ == 0)
{
lean_dec(v_a_966_);
return v_b_967_;
}
else
{
lean_object* v___x_969_; uint32_t v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_969_ = l_Subarray_get___redArg(v_fst_965_, v_a_966_);
v___x_970_ = lean_unbox_uint32(v___x_969_);
lean_dec(v___x_969_);
lean_inc(v_a_966_);
v___x_971_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(v_b_967_, v_a_966_, v___x_970_);
v___x_972_ = lean_unsigned_to_nat(1u);
v___x_973_ = lean_nat_add(v_a_966_, v___x_972_);
lean_dec(v_a_966_);
v_a_966_ = v___x_973_;
v_b_967_ = v___x_971_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg___boxed(lean_object* v_upperBound_975_, lean_object* v_fst_976_, lean_object* v___x_977_, lean_object* v_fst_978_, lean_object* v_a_979_, lean_object* v_b_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg(v_upperBound_975_, v_fst_976_, v___x_977_, v_fst_978_, v_a_979_, v_b_980_);
lean_dec_ref(v_fst_978_);
lean_dec(v___x_977_);
lean_dec_ref(v_fst_976_);
lean_dec(v_upperBound_975_);
return v_res_981_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_982_ = lean_box(0);
v___x_983_ = lean_unsigned_to_nat(16u);
v___x_984_ = lean_mk_array(v___x_983_, v___x_982_);
return v___x_984_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v_hist_987_; 
v___x_985_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0);
v___x_986_ = lean_unsigned_to_nat(0u);
v_hist_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_987_, 0, v___x_986_);
lean_ctor_set(v_hist_987_, 1, v___x_985_);
return v_hist_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(lean_object* v_left_988_, lean_object* v_right_989_){
_start:
{
lean_object* v___x_990_; lean_object* v_snd_991_; lean_object* v_fst_992_; lean_object* v_fst_993_; lean_object* v_snd_994_; lean_object* v___x_995_; lean_object* v_snd_996_; lean_object* v_fst_997_; lean_object* v_fst_998_; lean_object* v_snd_999_; lean_object* v_start_1000_; lean_object* v_stop_1001_; lean_object* v___x_1002_; lean_object* v_hist_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v_start_1006_; lean_object* v_stop_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v_buckets_1010_; lean_object* v___x_1011_; lean_object* v___y_1013_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_990_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3(v_left_988_, v_right_989_);
v_snd_991_ = lean_ctor_get(v___x_990_, 1);
lean_inc(v_snd_991_);
v_fst_992_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_fst_992_);
lean_dec_ref(v___x_990_);
v_fst_993_ = lean_ctor_get(v_snd_991_, 0);
lean_inc(v_fst_993_);
v_snd_994_ = lean_ctor_get(v_snd_991_, 1);
lean_inc(v_snd_994_);
lean_dec(v_snd_991_);
v___x_995_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4(v_fst_993_, v_snd_994_);
v_snd_996_ = lean_ctor_get(v___x_995_, 1);
lean_inc(v_snd_996_);
v_fst_997_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_fst_997_);
lean_dec_ref(v___x_995_);
v_fst_998_ = lean_ctor_get(v_snd_996_, 0);
lean_inc(v_fst_998_);
v_snd_999_ = lean_ctor_get(v_snd_996_, 1);
lean_inc(v_snd_999_);
lean_dec(v_snd_996_);
v_start_1000_ = lean_ctor_get(v_fst_997_, 1);
v_stop_1001_ = lean_ctor_get(v_fst_997_, 2);
v___x_1002_ = lean_unsigned_to_nat(0u);
v_hist_1003_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1);
v___x_1004_ = lean_nat_sub(v_stop_1001_, v_start_1000_);
v___x_1005_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg(v___x_1004_, v_fst_998_, v___x_1004_, v_fst_997_, v___x_1002_, v_hist_1003_);
v_start_1006_ = lean_ctor_get(v_fst_998_, 1);
v_stop_1007_ = lean_ctor_get(v_fst_998_, 2);
v___x_1008_ = lean_nat_sub(v_stop_1007_, v_start_1006_);
v___x_1009_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(v___x_1008_, v___x_1008_, v_fst_998_, v___x_1004_, v___x_1002_, v___x_1005_);
lean_dec(v___x_1004_);
lean_dec(v___x_1008_);
v_buckets_1010_ = lean_ctor_get(v___x_1009_, 1);
lean_inc_ref(v_buckets_1010_);
lean_dec_ref(v___x_1009_);
v___x_1011_ = lean_box(0);
v___x_1039_ = lean_box(0);
v___x_1040_ = lean_array_get_size(v_buckets_1010_);
v___x_1041_ = lean_nat_dec_lt(v___x_1002_, v___x_1040_);
if (v___x_1041_ == 0)
{
lean_dec_ref(v_buckets_1010_);
v___y_1013_ = v___x_1039_;
goto v___jp_1012_;
}
else
{
size_t v___x_1042_; size_t v___x_1043_; lean_object* v___x_1044_; 
v___x_1042_ = lean_usize_of_nat(v___x_1040_);
v___x_1043_ = ((size_t)0ULL);
v___x_1044_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7(v_buckets_1010_, v___x_1042_, v___x_1043_, v___x_1039_);
lean_dec_ref(v_buckets_1010_);
v___y_1013_ = v___x_1044_;
goto v___jp_1012_;
}
v___jp_1012_:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg(v___y_1013_, v___x_1011_);
lean_dec(v___y_1013_);
if (lean_obj_tag(v___x_1014_) == 1)
{
lean_object* v_val_1015_; lean_object* v_snd_1016_; lean_object* v_snd_1017_; lean_object* v_fst_1018_; lean_object* v_fst_1019_; lean_object* v_snd_1020_; lean_object* v___x_1021_; lean_object* v_fst_1022_; lean_object* v_snd_1023_; lean_object* v___x_1024_; lean_object* v_fst_1025_; lean_object* v_snd_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_val_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_val_1015_);
lean_dec_ref_known(v___x_1014_, 1);
v_snd_1016_ = lean_ctor_get(v_val_1015_, 1);
lean_inc(v_snd_1016_);
lean_dec(v_val_1015_);
v_snd_1017_ = lean_ctor_get(v_snd_1016_, 1);
lean_inc(v_snd_1017_);
v_fst_1018_ = lean_ctor_get(v_snd_1016_, 0);
lean_inc(v_fst_1018_);
lean_dec(v_snd_1016_);
v_fst_1019_ = lean_ctor_get(v_snd_1017_, 0);
lean_inc(v_fst_1019_);
v_snd_1020_ = lean_ctor_get(v_snd_1017_, 1);
lean_inc(v_snd_1020_);
lean_dec(v_snd_1017_);
v___x_1021_ = l_Subarray_split___redArg(v_fst_997_, v_fst_1019_);
lean_dec(v_fst_1019_);
v_fst_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_fst_1022_);
v_snd_1023_ = lean_ctor_get(v___x_1021_, 1);
lean_inc(v_snd_1023_);
lean_dec_ref(v___x_1021_);
v___x_1024_ = l_Subarray_split___redArg(v_fst_998_, v_snd_1020_);
lean_dec(v_snd_1020_);
v_fst_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_fst_1025_);
v_snd_1026_ = lean_ctor_get(v___x_1024_, 1);
lean_inc(v_snd_1026_);
lean_dec_ref(v___x_1024_);
v___x_1027_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v_fst_1022_, v_fst_1025_);
v___x_1028_ = l_Array_append___redArg(v_fst_992_, v___x_1027_);
lean_dec_ref(v___x_1027_);
v___x_1029_ = lean_unsigned_to_nat(1u);
v___x_1030_ = lean_mk_empty_array_with_capacity(v___x_1029_);
v___x_1031_ = lean_array_push(v___x_1030_, v_fst_1018_);
v___x_1032_ = l_Array_append___redArg(v___x_1028_, v___x_1031_);
lean_dec_ref(v___x_1031_);
v___x_1033_ = l_Subarray_drop___redArg(v_snd_1023_, v___x_1029_);
v___x_1034_ = l_Subarray_drop___redArg(v_snd_1026_, v___x_1029_);
v___x_1035_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v___x_1033_, v___x_1034_);
v___x_1036_ = l_Array_append___redArg(v___x_1032_, v___x_1035_);
lean_dec_ref(v___x_1035_);
v___x_1037_ = l_Array_append___redArg(v___x_1036_, v_snd_999_);
lean_dec(v_snd_999_);
return v___x_1037_;
}
else
{
lean_object* v___x_1038_; 
lean_dec(v___x_1014_);
lean_dec(v_fst_998_);
lean_dec(v_fst_997_);
v___x_1038_ = l_Array_append___redArg(v_fst_992_, v_snd_999_);
lean_dec(v_snd_999_);
return v___x_1038_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(lean_object* v___x_1045_, lean_object* v_edited_1046_, lean_object* v_a_1047_){
_start:
{
lean_object* v_fst_1048_; lean_object* v_snd_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1068_; 
v_fst_1048_ = lean_ctor_get(v_a_1047_, 0);
v_snd_1049_ = lean_ctor_get(v_a_1047_, 1);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_a_1047_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1051_ = v_a_1047_;
v_isShared_1052_ = v_isSharedCheck_1068_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_snd_1049_);
lean_inc(v_fst_1048_);
lean_dec(v_a_1047_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1068_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
uint8_t v___x_1053_; 
v___x_1053_ = lean_nat_dec_lt(v_snd_1049_, v___x_1045_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1055_; 
if (v_isShared_1052_ == 0)
{
v___x_1055_ = v___x_1051_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_fst_1048_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_snd_1049_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
else
{
uint8_t v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1057_ = 0;
v___x_1058_ = lean_array_fget_borrowed(v_edited_1046_, v_snd_1049_);
v___x_1059_ = lean_box(v___x_1057_);
lean_inc(v___x_1058_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 1, v___x_1058_);
lean_ctor_set(v___x_1051_, 0, v___x_1059_);
v___x_1061_ = v___x_1051_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v___x_1058_);
v___x_1061_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1062_ = lean_array_push(v_fst_1048_, v___x_1061_);
v___x_1063_ = lean_unsigned_to_nat(1u);
v___x_1064_ = lean_nat_add(v_snd_1049_, v___x_1063_);
lean_dec(v_snd_1049_);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1062_);
lean_ctor_set(v___x_1065_, 1, v___x_1064_);
v_a_1047_ = v___x_1065_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg___boxed(lean_object* v___x_1069_, lean_object* v_edited_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1069_, v_edited_1070_, v_a_1071_);
lean_dec_ref(v_edited_1070_);
lean_dec(v___x_1069_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(size_t v_sz_1073_, size_t v_i_1074_, lean_object* v_bs_1075_){
_start:
{
uint8_t v___x_1076_; 
v___x_1076_ = lean_usize_dec_lt(v_i_1074_, v_sz_1073_);
if (v___x_1076_ == 0)
{
return v_bs_1075_;
}
else
{
lean_object* v_v_1077_; lean_object* v___x_1078_; lean_object* v_bs_x27_1079_; uint8_t v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; size_t v___x_1083_; size_t v___x_1084_; lean_object* v___x_1085_; 
v_v_1077_ = lean_array_uget(v_bs_1075_, v_i_1074_);
v___x_1078_ = lean_unsigned_to_nat(0u);
v_bs_x27_1079_ = lean_array_uset(v_bs_1075_, v_i_1074_, v___x_1078_);
v___x_1080_ = 1;
v___x_1081_ = lean_box(v___x_1080_);
v___x_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
lean_ctor_set(v___x_1082_, 1, v_v_1077_);
v___x_1083_ = ((size_t)1ULL);
v___x_1084_ = lean_usize_add(v_i_1074_, v___x_1083_);
v___x_1085_ = lean_array_uset(v_bs_x27_1079_, v_i_1074_, v___x_1082_);
v_i_1074_ = v___x_1084_;
v_bs_1075_ = v___x_1085_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8___boxed(lean_object* v_sz_1087_, lean_object* v_i_1088_, lean_object* v_bs_1089_){
_start:
{
size_t v_sz_boxed_1090_; size_t v_i_boxed_1091_; lean_object* v_res_1092_; 
v_sz_boxed_1090_ = lean_unbox_usize(v_sz_1087_);
lean_dec(v_sz_1087_);
v_i_boxed_1091_ = lean_unbox_usize(v_i_1088_);
lean_dec(v_i_1088_);
v_res_1092_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(v_sz_boxed_1090_, v_i_boxed_1091_, v_bs_1089_);
return v_res_1092_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = 65;
v___x_1094_ = lean_box_uint32(v___x_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg(lean_object* v_edited_1095_, lean_object* v___x_1096_, uint32_t v_a_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v_fst_1099_; lean_object* v_snd_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1127_; 
v_fst_1099_ = lean_ctor_get(v_a_1098_, 0);
v_snd_1100_ = lean_ctor_get(v_a_1098_, 1);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_a_1098_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1102_ = v_a_1098_;
v_isShared_1103_ = v_isSharedCheck_1127_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_snd_1100_);
lean_inc(v_fst_1099_);
lean_dec(v_a_1098_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1127_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
uint8_t v___y_1105_; uint8_t v___x_1121_; 
v___x_1121_ = lean_nat_dec_lt(v_snd_1100_, v___x_1096_);
if (v___x_1121_ == 0)
{
v___y_1105_ = v___x_1121_;
goto v___jp_1104_;
}
else
{
lean_object* v___x_1122_; lean_object* v___x_1123_; uint32_t v___x_1124_; uint8_t v___x_1125_; 
v___x_1122_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1;
v___x_1123_ = lean_array_get_borrowed(v___x_1122_, v_edited_1095_, v_snd_1100_);
v___x_1124_ = lean_unbox_uint32(v___x_1123_);
v___x_1125_ = lean_uint32_dec_eq(v___x_1124_, v_a_1097_);
if (v___x_1125_ == 0)
{
v___y_1105_ = v___x_1121_;
goto v___jp_1104_;
}
else
{
lean_object* v___x_1126_; 
lean_del_object(v___x_1102_);
v___x_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1126_, 0, v_fst_1099_);
lean_ctor_set(v___x_1126_, 1, v_snd_1100_);
return v___x_1126_;
}
}
v___jp_1104_:
{
if (v___y_1105_ == 0)
{
lean_object* v___x_1107_; 
if (v_isShared_1103_ == 0)
{
v___x_1107_ = v___x_1102_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_fst_1099_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_snd_1100_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
else
{
uint8_t v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1109_ = 0;
v___x_1110_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1;
v___x_1111_ = lean_array_get_borrowed(v___x_1110_, v_edited_1095_, v_snd_1100_);
v___x_1112_ = lean_box(v___x_1109_);
lean_inc(v___x_1111_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 1, v___x_1111_);
lean_ctor_set(v___x_1102_, 0, v___x_1112_);
v___x_1114_ = v___x_1102_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v___x_1111_);
v___x_1114_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1115_ = lean_array_push(v_fst_1099_, v___x_1114_);
v___x_1116_ = lean_unsigned_to_nat(1u);
v___x_1117_ = lean_nat_add(v_snd_1100_, v___x_1116_);
lean_dec(v_snd_1100_);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1115_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v_a_1098_ = v___x_1118_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed(lean_object* v_edited_1128_, lean_object* v___x_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
uint32_t v_a_boxed_1132_; lean_object* v_res_1133_; 
v_a_boxed_1132_ = lean_unbox_uint32(v_a_1130_);
lean_dec(v_a_1130_);
v_res_1133_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg(v_edited_1128_, v___x_1129_, v_a_boxed_1132_, v_a_1131_);
lean_dec(v___x_1129_);
lean_dec_ref(v_edited_1128_);
return v_res_1133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(lean_object* v_original_1134_, lean_object* v___x_1135_, uint32_t v_a_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v_fst_1138_; lean_object* v_snd_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1166_; 
v_fst_1138_ = lean_ctor_get(v_a_1137_, 0);
v_snd_1139_ = lean_ctor_get(v_a_1137_, 1);
v_isSharedCheck_1166_ = !lean_is_exclusive(v_a_1137_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1141_ = v_a_1137_;
v_isShared_1142_ = v_isSharedCheck_1166_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_snd_1139_);
lean_inc(v_fst_1138_);
lean_dec(v_a_1137_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1166_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
uint8_t v___y_1144_; uint8_t v___x_1160_; 
v___x_1160_ = lean_nat_dec_lt(v_snd_1139_, v___x_1135_);
if (v___x_1160_ == 0)
{
v___y_1144_ = v___x_1160_;
goto v___jp_1143_;
}
else
{
lean_object* v___x_1161_; lean_object* v___x_1162_; uint32_t v___x_1163_; uint8_t v___x_1164_; 
v___x_1161_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1;
v___x_1162_ = lean_array_get_borrowed(v___x_1161_, v_original_1134_, v_snd_1139_);
v___x_1163_ = lean_unbox_uint32(v___x_1162_);
v___x_1164_ = lean_uint32_dec_eq(v___x_1163_, v_a_1136_);
if (v___x_1164_ == 0)
{
v___y_1144_ = v___x_1160_;
goto v___jp_1143_;
}
else
{
lean_object* v___x_1165_; 
lean_del_object(v___x_1141_);
v___x_1165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1165_, 0, v_fst_1138_);
lean_ctor_set(v___x_1165_, 1, v_snd_1139_);
return v___x_1165_;
}
}
v___jp_1143_:
{
if (v___y_1144_ == 0)
{
lean_object* v___x_1146_; 
if (v_isShared_1142_ == 0)
{
v___x_1146_ = v___x_1141_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_fst_1138_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_snd_1139_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
else
{
uint8_t v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1148_ = 1;
v___x_1149_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1;
v___x_1150_ = lean_array_get_borrowed(v___x_1149_, v_original_1134_, v_snd_1139_);
v___x_1151_ = lean_box(v___x_1148_);
lean_inc(v___x_1150_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 1, v___x_1150_);
lean_ctor_set(v___x_1141_, 0, v___x_1151_);
v___x_1153_ = v___x_1141_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v___x_1150_);
v___x_1153_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1154_ = lean_array_push(v_fst_1138_, v___x_1153_);
v___x_1155_ = lean_unsigned_to_nat(1u);
v___x_1156_ = lean_nat_add(v_snd_1139_, v___x_1155_);
lean_dec(v_snd_1139_);
v___x_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1154_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
v_a_1137_ = v___x_1157_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg___boxed(lean_object* v_original_1167_, lean_object* v___x_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_){
_start:
{
uint32_t v_a_boxed_1171_; lean_object* v_res_1172_; 
v_a_boxed_1171_ = lean_unbox_uint32(v_a_1169_);
lean_dec(v_a_1169_);
v_res_1172_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v_original_1167_, v___x_1168_, v_a_boxed_1171_, v_a_1170_);
lean_dec(v___x_1168_);
lean_dec_ref(v_original_1167_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(lean_object* v_original_1173_, lean_object* v___x_1174_, lean_object* v_edited_1175_, lean_object* v___x_1176_, lean_object* v_as_1177_, size_t v_sz_1178_, size_t v_i_1179_, lean_object* v_b_1180_){
_start:
{
uint8_t v___x_1181_; 
v___x_1181_ = lean_usize_dec_lt(v_i_1179_, v_sz_1178_);
if (v___x_1181_ == 0)
{
return v_b_1180_;
}
else
{
lean_object* v_snd_1182_; lean_object* v_fst_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1232_; 
v_snd_1182_ = lean_ctor_get(v_b_1180_, 1);
v_fst_1183_ = lean_ctor_get(v_b_1180_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_b_1180_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1185_ = v_b_1180_;
v_isShared_1186_ = v_isSharedCheck_1232_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_snd_1182_);
lean_inc(v_fst_1183_);
lean_dec(v_b_1180_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1232_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v_fst_1187_; lean_object* v_snd_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1231_; 
v_fst_1187_ = lean_ctor_get(v_snd_1182_, 0);
v_snd_1188_ = lean_ctor_get(v_snd_1182_, 1);
v_isSharedCheck_1231_ = !lean_is_exclusive(v_snd_1182_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1190_ = v_snd_1182_;
v_isShared_1191_ = v_isSharedCheck_1231_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_snd_1188_);
lean_inc(v_fst_1187_);
lean_dec(v_snd_1182_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1231_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v_a_1192_; lean_object* v___x_1194_; 
v_a_1192_ = lean_array_uget_borrowed(v_as_1177_, v_i_1179_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 1, v_fst_1187_);
lean_ctor_set(v___x_1190_, 0, v_fst_1183_);
v___x_1194_ = v___x_1190_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v_fst_1183_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_fst_1187_);
v___x_1194_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
uint32_t v___x_1195_; lean_object* v___x_1196_; lean_object* v_fst_1197_; lean_object* v_snd_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1229_; 
v___x_1195_ = lean_unbox_uint32(v_a_1192_);
v___x_1196_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v_original_1173_, v___x_1174_, v___x_1195_, v___x_1194_);
v_fst_1197_ = lean_ctor_get(v___x_1196_, 0);
v_snd_1198_ = lean_ctor_get(v___x_1196_, 1);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1200_ = v___x_1196_;
v_isShared_1201_ = v_isSharedCheck_1229_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_snd_1198_);
lean_inc(v_fst_1197_);
lean_dec(v___x_1196_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1229_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 1, v_snd_1188_);
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_fst_1197_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_snd_1188_);
v___x_1203_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
uint32_t v___x_1204_; lean_object* v___x_1205_; lean_object* v_fst_1206_; lean_object* v_snd_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1227_; 
v___x_1204_ = lean_unbox_uint32(v_a_1192_);
v___x_1205_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg(v_edited_1175_, v___x_1176_, v___x_1204_, v___x_1203_);
v_fst_1206_ = lean_ctor_get(v___x_1205_, 0);
v_snd_1207_ = lean_ctor_get(v___x_1205_, 1);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1209_ = v___x_1205_;
v_isShared_1210_ = v_isSharedCheck_1227_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_snd_1207_);
lean_inc(v_fst_1206_);
lean_dec(v___x_1205_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1227_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
uint8_t v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1211_ = 2;
v___x_1212_ = lean_box(v___x_1211_);
lean_inc(v_a_1192_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 1, v_a_1192_);
lean_ctor_set(v___x_1209_, 0, v___x_1212_);
v___x_1214_ = v___x_1209_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_a_1192_);
v___x_1214_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1215_ = lean_array_push(v_fst_1206_, v___x_1214_);
v___x_1216_ = lean_unsigned_to_nat(1u);
v___x_1217_ = lean_nat_add(v_snd_1198_, v___x_1216_);
lean_dec(v_snd_1198_);
v___x_1218_ = lean_nat_add(v_snd_1207_, v___x_1216_);
lean_dec(v_snd_1207_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 1, v___x_1218_);
lean_ctor_set(v___x_1185_, 0, v___x_1217_);
v___x_1220_ = v___x_1185_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1221_; size_t v___x_1222_; size_t v___x_1223_; 
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1215_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
v___x_1222_ = ((size_t)1ULL);
v___x_1223_ = lean_usize_add(v_i_1179_, v___x_1222_);
v_i_1179_ = v___x_1223_;
v_b_1180_ = v___x_1221_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15___boxed(lean_object* v_original_1233_, lean_object* v___x_1234_, lean_object* v_edited_1235_, lean_object* v___x_1236_, lean_object* v_as_1237_, lean_object* v_sz_1238_, lean_object* v_i_1239_, lean_object* v_b_1240_){
_start:
{
size_t v_sz_boxed_1241_; size_t v_i_boxed_1242_; lean_object* v_res_1243_; 
v_sz_boxed_1241_ = lean_unbox_usize(v_sz_1238_);
lean_dec(v_sz_1238_);
v_i_boxed_1242_ = lean_unbox_usize(v_i_1239_);
lean_dec(v_i_1239_);
v_res_1243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(v_original_1233_, v___x_1234_, v_edited_1235_, v___x_1236_, v_as_1237_, v_sz_boxed_1241_, v_i_boxed_1242_, v_b_1240_);
lean_dec_ref(v_as_1237_);
lean_dec(v___x_1236_);
lean_dec_ref(v_edited_1235_);
lean_dec(v___x_1234_);
lean_dec_ref(v_original_1233_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(lean_object* v_edited_1244_, lean_object* v___x_1245_, lean_object* v_original_1246_, lean_object* v___x_1247_, lean_object* v_as_1248_, size_t v_sz_1249_, size_t v_i_1250_, lean_object* v_b_1251_){
_start:
{
uint8_t v___x_1252_; 
v___x_1252_ = lean_usize_dec_lt(v_i_1250_, v_sz_1249_);
if (v___x_1252_ == 0)
{
return v_b_1251_;
}
else
{
lean_object* v_snd_1253_; lean_object* v_fst_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1303_; 
v_snd_1253_ = lean_ctor_get(v_b_1251_, 1);
v_fst_1254_ = lean_ctor_get(v_b_1251_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v_b_1251_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1256_ = v_b_1251_;
v_isShared_1257_ = v_isSharedCheck_1303_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_snd_1253_);
lean_inc(v_fst_1254_);
lean_dec(v_b_1251_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1303_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v_fst_1258_; lean_object* v_snd_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1302_; 
v_fst_1258_ = lean_ctor_get(v_snd_1253_, 0);
v_snd_1259_ = lean_ctor_get(v_snd_1253_, 1);
v_isSharedCheck_1302_ = !lean_is_exclusive(v_snd_1253_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1261_ = v_snd_1253_;
v_isShared_1262_ = v_isSharedCheck_1302_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_snd_1259_);
lean_inc(v_fst_1258_);
lean_dec(v_snd_1253_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1302_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v_a_1263_; lean_object* v___x_1265_; 
v_a_1263_ = lean_array_uget_borrowed(v_as_1248_, v_i_1250_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v_fst_1258_);
lean_ctor_set(v___x_1261_, 0, v_fst_1254_);
v___x_1265_ = v___x_1261_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_fst_1254_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v_fst_1258_);
v___x_1265_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
uint32_t v___x_1266_; lean_object* v___x_1267_; lean_object* v_fst_1268_; lean_object* v_snd_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1300_; 
v___x_1266_ = lean_unbox_uint32(v_a_1263_);
v___x_1267_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v_original_1246_, v___x_1247_, v___x_1266_, v___x_1265_);
v_fst_1268_ = lean_ctor_get(v___x_1267_, 0);
v_snd_1269_ = lean_ctor_get(v___x_1267_, 1);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1271_ = v___x_1267_;
v_isShared_1272_ = v_isSharedCheck_1300_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_snd_1269_);
lean_inc(v_fst_1268_);
lean_dec(v___x_1267_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1300_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 1, v_snd_1259_);
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_fst_1268_);
lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_snd_1259_);
v___x_1274_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
uint32_t v___x_1275_; lean_object* v___x_1276_; lean_object* v_fst_1277_; lean_object* v_snd_1278_; lean_object* v___x_1280_; uint8_t v_isShared_1281_; uint8_t v_isSharedCheck_1298_; 
v___x_1275_ = lean_unbox_uint32(v_a_1263_);
v___x_1276_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg(v_edited_1244_, v___x_1245_, v___x_1275_, v___x_1274_);
v_fst_1277_ = lean_ctor_get(v___x_1276_, 0);
v_snd_1278_ = lean_ctor_get(v___x_1276_, 1);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1276_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1280_ = v___x_1276_;
v_isShared_1281_ = v_isSharedCheck_1298_;
goto v_resetjp_1279_;
}
else
{
lean_inc(v_snd_1278_);
lean_inc(v_fst_1277_);
lean_dec(v___x_1276_);
v___x_1280_ = lean_box(0);
v_isShared_1281_ = v_isSharedCheck_1298_;
goto v_resetjp_1279_;
}
v_resetjp_1279_:
{
uint8_t v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1285_; 
v___x_1282_ = 2;
v___x_1283_ = lean_box(v___x_1282_);
lean_inc(v_a_1263_);
if (v_isShared_1281_ == 0)
{
lean_ctor_set(v___x_1280_, 1, v_a_1263_);
lean_ctor_set(v___x_1280_, 0, v___x_1283_);
v___x_1285_ = v___x_1280_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_a_1263_);
v___x_1285_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1286_ = lean_array_push(v_fst_1277_, v___x_1285_);
v___x_1287_ = lean_unsigned_to_nat(1u);
v___x_1288_ = lean_nat_add(v_snd_1269_, v___x_1287_);
lean_dec(v_snd_1269_);
v___x_1289_ = lean_nat_add(v_snd_1278_, v___x_1287_);
lean_dec(v_snd_1278_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v___x_1289_);
lean_ctor_set(v___x_1256_, 0, v___x_1288_);
v___x_1291_ = v___x_1256_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___x_1288_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
lean_object* v___x_1292_; size_t v___x_1293_; size_t v___x_1294_; lean_object* v___x_1295_; 
v___x_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1292_, 0, v___x_1286_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
v___x_1293_ = ((size_t)1ULL);
v___x_1294_ = lean_usize_add(v_i_1250_, v___x_1293_);
v___x_1295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(v_original_1246_, v___x_1247_, v_edited_1244_, v___x_1245_, v_as_1248_, v_sz_1249_, v___x_1294_, v___x_1292_);
return v___x_1295_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5___boxed(lean_object* v_edited_1304_, lean_object* v___x_1305_, lean_object* v_original_1306_, lean_object* v___x_1307_, lean_object* v_as_1308_, lean_object* v_sz_1309_, lean_object* v_i_1310_, lean_object* v_b_1311_){
_start:
{
size_t v_sz_boxed_1312_; size_t v_i_boxed_1313_; lean_object* v_res_1314_; 
v_sz_boxed_1312_ = lean_unbox_usize(v_sz_1309_);
lean_dec(v_sz_1309_);
v_i_boxed_1313_ = lean_unbox_usize(v_i_1310_);
lean_dec(v_i_1310_);
v_res_1314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v_edited_1304_, v___x_1305_, v_original_1306_, v___x_1307_, v_as_1308_, v_sz_boxed_1312_, v_i_boxed_1313_, v_b_1311_);
lean_dec_ref(v_as_1308_);
lean_dec(v___x_1307_);
lean_dec_ref(v_original_1306_);
lean_dec(v___x_1305_);
lean_dec_ref(v_edited_1304_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(lean_object* v_original_1322_, lean_object* v_edited_1323_){
_start:
{
lean_object* v_i_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v_i_1324_ = lean_unsigned_to_nat(0u);
v___x_1325_ = lean_array_get_size(v_original_1322_);
v___x_1326_ = lean_nat_dec_lt(v_i_1324_, v___x_1325_);
if (v___x_1326_ == 0)
{
size_t v_sz_1327_; size_t v___x_1328_; lean_object* v___x_1329_; 
lean_dec_ref(v_original_1322_);
v_sz_1327_ = lean_array_size(v_edited_1323_);
v___x_1328_ = ((size_t)0ULL);
v___x_1329_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(v_sz_1327_, v___x_1328_, v_edited_1323_);
return v___x_1329_;
}
else
{
lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1330_ = lean_array_get_size(v_edited_1323_);
v___x_1331_ = lean_nat_dec_lt(v_i_1324_, v___x_1330_);
if (v___x_1331_ == 0)
{
size_t v_sz_1332_; size_t v___x_1333_; lean_object* v___x_1334_; 
lean_dec_ref(v_edited_1323_);
v_sz_1332_ = lean_array_size(v_original_1322_);
v___x_1333_ = ((size_t)0ULL);
v___x_1334_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(v_sz_1332_, v___x_1333_, v_original_1322_);
return v___x_1334_;
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v_ds_1337_; lean_object* v___x_1338_; size_t v_sz_1339_; size_t v___x_1340_; lean_object* v___x_1341_; lean_object* v_snd_1342_; lean_object* v_fst_1343_; lean_object* v_fst_1344_; lean_object* v_snd_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1364_; 
lean_inc_ref(v_original_1322_);
v___x_1335_ = l_Array_toSubarray___redArg(v_original_1322_, v_i_1324_, v___x_1325_);
lean_inc_ref(v_edited_1323_);
v___x_1336_ = l_Array_toSubarray___redArg(v_edited_1323_, v_i_1324_, v___x_1330_);
v_ds_1337_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v___x_1335_, v___x_1336_);
v___x_1338_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__2));
v_sz_1339_ = lean_array_size(v_ds_1337_);
v___x_1340_ = ((size_t)0ULL);
v___x_1341_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v_edited_1323_, v___x_1330_, v_original_1322_, v___x_1325_, v_ds_1337_, v_sz_1339_, v___x_1340_, v___x_1338_);
lean_dec_ref(v_ds_1337_);
v_snd_1342_ = lean_ctor_get(v___x_1341_, 1);
lean_inc(v_snd_1342_);
v_fst_1343_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_fst_1343_);
lean_dec_ref(v___x_1341_);
v_fst_1344_ = lean_ctor_get(v_snd_1342_, 0);
v_snd_1345_ = lean_ctor_get(v_snd_1342_, 1);
v_isSharedCheck_1364_ = !lean_is_exclusive(v_snd_1342_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1347_ = v_snd_1342_;
v_isShared_1348_ = v_isSharedCheck_1364_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_snd_1345_);
lean_inc(v_fst_1344_);
lean_dec(v_snd_1342_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1364_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 1, v_fst_1344_);
lean_ctor_set(v___x_1347_, 0, v_fst_1343_);
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_fst_1343_);
lean_ctor_set(v_reuseFailAlloc_1363_, 1, v_fst_1344_);
v___x_1350_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1351_; lean_object* v_fst_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1361_; 
v___x_1351_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_1325_, v_original_1322_, v___x_1350_);
lean_dec_ref(v_original_1322_);
v_fst_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1361_ == 0)
{
lean_object* v_unused_1362_; 
v_unused_1362_ = lean_ctor_get(v___x_1351_, 1);
lean_dec(v_unused_1362_);
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1361_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_fst_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1361_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
lean_ctor_set(v___x_1354_, 1, v_snd_1345_);
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_fst_1352_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_snd_1345_);
v___x_1357_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
lean_object* v___x_1358_; lean_object* v_fst_1359_; 
v___x_1358_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1330_, v_edited_1323_, v___x_1357_);
lean_dec_ref(v_edited_1323_);
v_fst_1359_ = lean_ctor_get(v___x_1358_, 0);
lean_inc(v_fst_1359_);
lean_dec_ref(v___x_1358_);
return v_fst_1359_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(lean_object* v_s_1365_, lean_object* v_a_1366_, uint8_t v_b_1367_){
_start:
{
lean_object* v_str_1368_; lean_object* v_startInclusive_1369_; lean_object* v_endExclusive_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v_str_1368_ = lean_ctor_get(v_s_1365_, 0);
v_startInclusive_1369_ = lean_ctor_get(v_s_1365_, 1);
v_endExclusive_1370_ = lean_ctor_get(v_s_1365_, 2);
v___x_1371_ = lean_nat_sub(v_endExclusive_1370_, v_startInclusive_1369_);
v___x_1372_ = lean_nat_dec_eq(v_a_1366_, v___x_1371_);
lean_dec(v___x_1371_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; uint32_t v___x_1374_; uint32_t v___x_1375_; uint8_t v___x_1376_; 
v___x_1373_ = lean_nat_add(v_startInclusive_1369_, v_a_1366_);
lean_dec(v_a_1366_);
v___x_1374_ = lean_string_utf8_get_fast(v_str_1368_, v___x_1373_);
v___x_1375_ = 10;
v___x_1376_ = lean_uint32_dec_eq(v___x_1374_, v___x_1375_);
if (v___x_1376_ == 0)
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = lean_string_utf8_next_fast(v_str_1368_, v___x_1373_);
lean_dec(v___x_1373_);
v___x_1378_ = lean_nat_sub(v___x_1377_, v_startInclusive_1369_);
v_a_1366_ = v___x_1378_;
v_b_1367_ = v___x_1376_;
goto _start;
}
else
{
lean_dec(v___x_1373_);
return v___x_1376_;
}
}
else
{
lean_dec(v_a_1366_);
return v_b_1367_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg___boxed(lean_object* v_s_1380_, lean_object* v_a_1381_, lean_object* v_b_1382_){
_start:
{
uint8_t v_b_boxed_1383_; uint8_t v_res_1384_; lean_object* v_r_1385_; 
v_b_boxed_1383_ = lean_unbox(v_b_1382_);
v_res_1384_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1380_, v_a_1381_, v_b_boxed_1383_);
lean_dec_ref(v_s_1380_);
v_r_1385_ = lean_box(v_res_1384_);
return v_r_1385_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(lean_object* v_s_1386_){
_start:
{
lean_object* v_searcher_1387_; uint8_t v___x_1388_; uint8_t v___x_1389_; 
v_searcher_1387_ = lean_unsigned_to_nat(0u);
v___x_1388_ = 0;
v___x_1389_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1386_, v_searcher_1387_, v___x_1388_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0___boxed(lean_object* v_s_1390_){
_start:
{
uint8_t v_res_1391_; lean_object* v_r_1392_; 
v_res_1391_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v_s_1390_);
lean_dec_ref(v_s_1390_);
v_r_1392_ = lean_box(v_res_1391_);
return v_r_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(lean_object* v_oldWs_1393_, lean_object* v_newWs_1394_){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1395_ = lean_unsigned_to_nat(0u);
v___x_1396_ = lean_string_utf8_byte_size(v_oldWs_1393_);
lean_inc_ref(v_oldWs_1393_);
v___x_1397_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1397_, 0, v_oldWs_1393_);
lean_ctor_set(v___x_1397_, 1, v___x_1395_);
lean_ctor_set(v___x_1397_, 2, v___x_1396_);
v___x_1398_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_1397_);
lean_dec_ref_known(v___x_1397_, 3);
if (v___x_1398_ == 0)
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1399_ = lean_string_data(v_oldWs_1393_);
v___x_1400_ = lean_array_mk(v___x_1399_);
v___x_1401_ = lean_string_data(v_newWs_1394_);
v___x_1402_ = lean_array_mk(v___x_1401_);
v___x_1403_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_1400_, v___x_1402_);
v___x_1404_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_1403_);
lean_dec_ref(v___x_1403_);
return v___x_1404_;
}
else
{
uint8_t v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
lean_dec_ref(v_oldWs_1393_);
v___x_1405_ = 2;
v___x_1406_ = lean_box(v___x_1405_);
v___x_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
lean_ctor_set(v___x_1407_, 1, v_newWs_1394_);
v___x_1408_ = lean_unsigned_to_nat(1u);
v___x_1409_ = lean_mk_empty_array_with_capacity(v___x_1408_);
v___x_1410_ = lean_array_push(v___x_1409_, v___x_1407_);
return v___x_1410_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(lean_object* v_s_1411_, lean_object* v_inst_1412_, lean_object* v_R_1413_, lean_object* v_a_1414_, uint8_t v_b_1415_, lean_object* v_c_1416_){
_start:
{
uint8_t v___x_1417_; 
v___x_1417_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1411_, v_a_1414_, v_b_1415_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___boxed(lean_object* v_s_1418_, lean_object* v_inst_1419_, lean_object* v_R_1420_, lean_object* v_a_1421_, lean_object* v_b_1422_, lean_object* v_c_1423_){
_start:
{
uint8_t v_b_boxed_1424_; uint8_t v_res_1425_; lean_object* v_r_1426_; 
v_b_boxed_1424_ = lean_unbox(v_b_1422_);
v_res_1425_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(v_s_1418_, v_inst_1419_, v_R_1420_, v_a_1421_, v_b_boxed_1424_, v_c_1423_);
lean_dec_ref(v_s_1418_);
v_r_1426_ = lean_box(v_res_1425_);
return v_r_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(lean_object* v_original_1427_, lean_object* v___x_1428_, uint32_t v_a_1429_, lean_object* v_inst_1430_, lean_object* v_a_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v_original_1427_, v___x_1428_, v_a_1429_, v_a_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___boxed(lean_object* v_original_1433_, lean_object* v___x_1434_, lean_object* v_a_1435_, lean_object* v_inst_1436_, lean_object* v_a_1437_){
_start:
{
uint32_t v_a_boxed_1438_; lean_object* v_res_1439_; 
v_a_boxed_1438_ = lean_unbox_uint32(v_a_1435_);
lean_dec(v_a_1435_);
v_res_1439_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(v_original_1433_, v___x_1434_, v_a_boxed_1438_, v_inst_1436_, v_a_1437_);
lean_dec(v___x_1434_);
lean_dec_ref(v_original_1433_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(lean_object* v_edited_1440_, lean_object* v___x_1441_, uint32_t v_a_1442_, lean_object* v_inst_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg(v_edited_1440_, v___x_1441_, v_a_1442_, v_a_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed(lean_object* v_edited_1446_, lean_object* v___x_1447_, lean_object* v_a_1448_, lean_object* v_inst_1449_, lean_object* v_a_1450_){
_start:
{
uint32_t v_a_boxed_1451_; lean_object* v_res_1452_; 
v_a_boxed_1451_ = lean_unbox_uint32(v_a_1448_);
lean_dec(v_a_1448_);
v_res_1452_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v_edited_1446_, v___x_1447_, v_a_boxed_1451_, v_inst_1449_, v_a_1450_);
lean_dec(v___x_1447_);
lean_dec_ref(v_edited_1446_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(lean_object* v___x_1453_, lean_object* v_original_1454_, lean_object* v_inst_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_1453_, v_original_1454_, v_a_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___boxed(lean_object* v___x_1458_, lean_object* v_original_1459_, lean_object* v_inst_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v_res_1462_; 
v_res_1462_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(v___x_1458_, v_original_1459_, v_inst_1460_, v_a_1461_);
lean_dec_ref(v_original_1459_);
lean_dec(v___x_1458_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(lean_object* v___x_1463_, lean_object* v_edited_1464_, lean_object* v_inst_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1463_, v_edited_1464_, v_a_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___boxed(lean_object* v___x_1468_, lean_object* v_edited_1469_, lean_object* v_inst_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(v___x_1468_, v_edited_1469_, v_inst_1470_, v_a_1471_);
lean_dec_ref(v_edited_1469_);
lean_dec(v___x_1468_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5(lean_object* v_as_1473_, lean_object* v_as_x27_1474_, lean_object* v_b_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg(v_as_x27_1474_, v_b_1475_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___boxed(lean_object* v_as_1478_, lean_object* v_as_x27_1479_, lean_object* v_b_1480_, lean_object* v_a_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5(v_as_1478_, v_as_x27_1479_, v_b_1480_, v_a_1481_);
lean_dec(v_as_x27_1479_);
lean_dec(v_as_1478_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8(lean_object* v_lsize_1483_, lean_object* v_rsize_1484_, lean_object* v_histogram_1485_, lean_object* v_index_1486_, uint32_t v_val_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(v_histogram_1485_, v_index_1486_, v_val_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___boxed(lean_object* v_lsize_1489_, lean_object* v_rsize_1490_, lean_object* v_histogram_1491_, lean_object* v_index_1492_, lean_object* v_val_1493_){
_start:
{
uint32_t v_val_boxed_1494_; lean_object* v_res_1495_; 
v_val_boxed_1494_ = lean_unbox_uint32(v_val_1493_);
lean_dec(v_val_1493_);
v_res_1495_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8(v_lsize_1489_, v_rsize_1490_, v_histogram_1491_, v_index_1492_, v_val_boxed_1494_);
lean_dec(v_rsize_1490_);
lean_dec(v_lsize_1489_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9(lean_object* v_upperBound_1496_, lean_object* v___x_1497_, lean_object* v_fst_1498_, lean_object* v___x_1499_, lean_object* v_inst_1500_, lean_object* v_R_1501_, lean_object* v_a_1502_, lean_object* v_b_1503_, lean_object* v_c_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(v_upperBound_1496_, v___x_1497_, v_fst_1498_, v___x_1499_, v_a_1502_, v_b_1503_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___boxed(lean_object* v_upperBound_1506_, lean_object* v___x_1507_, lean_object* v_fst_1508_, lean_object* v___x_1509_, lean_object* v_inst_1510_, lean_object* v_R_1511_, lean_object* v_a_1512_, lean_object* v_b_1513_, lean_object* v_c_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9(v_upperBound_1506_, v___x_1507_, v_fst_1508_, v___x_1509_, v_inst_1510_, v_R_1511_, v_a_1512_, v_b_1513_, v_c_1514_);
lean_dec(v___x_1509_);
lean_dec_ref(v_fst_1508_);
lean_dec(v___x_1507_);
lean_dec(v_upperBound_1506_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10(lean_object* v_lsize_1516_, lean_object* v_rsize_1517_, lean_object* v_histogram_1518_, lean_object* v_index_1519_, uint32_t v_val_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(v_histogram_1518_, v_index_1519_, v_val_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___boxed(lean_object* v_lsize_1522_, lean_object* v_rsize_1523_, lean_object* v_histogram_1524_, lean_object* v_index_1525_, lean_object* v_val_1526_){
_start:
{
uint32_t v_val_boxed_1527_; lean_object* v_res_1528_; 
v_val_boxed_1527_ = lean_unbox_uint32(v_val_1526_);
lean_dec(v_val_1526_);
v_res_1528_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10(v_lsize_1522_, v_rsize_1523_, v_histogram_1524_, v_index_1525_, v_val_boxed_1527_);
lean_dec(v_rsize_1523_);
lean_dec(v_lsize_1522_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11(lean_object* v_upperBound_1529_, lean_object* v_fst_1530_, lean_object* v___x_1531_, lean_object* v_fst_1532_, lean_object* v_inst_1533_, lean_object* v_R_1534_, lean_object* v_a_1535_, lean_object* v_b_1536_, lean_object* v_c_1537_){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg(v_upperBound_1529_, v_fst_1530_, v___x_1531_, v_fst_1532_, v_a_1535_, v_b_1536_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___boxed(lean_object* v_upperBound_1539_, lean_object* v_fst_1540_, lean_object* v___x_1541_, lean_object* v_fst_1542_, lean_object* v_inst_1543_, lean_object* v_R_1544_, lean_object* v_a_1545_, lean_object* v_b_1546_, lean_object* v_c_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11(v_upperBound_1539_, v_fst_1540_, v___x_1541_, v_fst_1542_, v_inst_1543_, v_R_1544_, v_a_1545_, v_b_1546_, v_c_1547_);
lean_dec_ref(v_fst_1542_);
lean_dec(v___x_1541_);
lean_dec_ref(v_fst_1540_);
lean_dec(v_upperBound_1539_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11(lean_object* v_00_u03b2_1549_, lean_object* v_m_1550_, uint32_t v_a_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(v_m_1550_, v_a_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___boxed(lean_object* v_00_u03b2_1553_, lean_object* v_m_1554_, lean_object* v_a_1555_){
_start:
{
uint32_t v_a_boxed_1556_; lean_object* v_res_1557_; 
v_a_boxed_1556_ = lean_unbox_uint32(v_a_1555_);
lean_dec(v_a_1555_);
v_res_1557_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11(v_00_u03b2_1553_, v_m_1554_, v_a_boxed_1556_);
lean_dec_ref(v_m_1554_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12(lean_object* v_00_u03b2_1558_, lean_object* v_m_1559_, uint32_t v_a_1560_, lean_object* v_b_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_m_1559_, v_a_1560_, v_b_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___boxed(lean_object* v_00_u03b2_1563_, lean_object* v_m_1564_, lean_object* v_a_1565_, lean_object* v_b_1566_){
_start:
{
uint32_t v_a_boxed_1567_; lean_object* v_res_1568_; 
v_a_boxed_1567_ = lean_unbox_uint32(v_a_1565_);
lean_dec(v_a_1565_);
v_res_1568_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12(v_00_u03b2_1563_, v_m_1564_, v_a_boxed_1567_, v_b_1566_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14(lean_object* v_inst_1569_, lean_object* v_R_1570_, lean_object* v_a_1571_, lean_object* v_b_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(v_a_1571_, v_b_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20(lean_object* v_00_u03b2_1574_, uint32_t v_a_1575_, lean_object* v_x_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg(v_a_1575_, v_x_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___boxed(lean_object* v_00_u03b2_1578_, lean_object* v_a_1579_, lean_object* v_x_1580_){
_start:
{
uint32_t v_a_boxed_1581_; lean_object* v_res_1582_; 
v_a_boxed_1581_ = lean_unbox_uint32(v_a_1579_);
lean_dec(v_a_1579_);
v_res_1582_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20(v_00_u03b2_1578_, v_a_boxed_1581_, v_x_1580_);
lean_dec(v_x_1580_);
return v_res_1582_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22(lean_object* v_00_u03b2_1583_, uint32_t v_a_1584_, lean_object* v_x_1585_){
_start:
{
uint8_t v___x_1586_; 
v___x_1586_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg(v_a_1584_, v_x_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___boxed(lean_object* v_00_u03b2_1587_, lean_object* v_a_1588_, lean_object* v_x_1589_){
_start:
{
uint32_t v_a_boxed_1590_; uint8_t v_res_1591_; lean_object* v_r_1592_; 
v_a_boxed_1590_ = lean_unbox_uint32(v_a_1588_);
lean_dec(v_a_1588_);
v_res_1591_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22(v_00_u03b2_1587_, v_a_boxed_1590_, v_x_1589_);
lean_dec(v_x_1589_);
v_r_1592_ = lean_box(v_res_1591_);
return v_r_1592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23(lean_object* v_00_u03b2_1593_, lean_object* v_data_1594_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23___redArg(v_data_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24(lean_object* v_00_u03b2_1596_, uint32_t v_a_1597_, lean_object* v_b_1598_, lean_object* v_x_1599_){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(v_a_1597_, v_b_1598_, v_x_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___boxed(lean_object* v_00_u03b2_1601_, lean_object* v_a_1602_, lean_object* v_b_1603_, lean_object* v_x_1604_){
_start:
{
uint32_t v_a_boxed_1605_; lean_object* v_res_1606_; 
v_a_boxed_1605_ = lean_unbox_uint32(v_a_1602_);
lean_dec(v_a_1602_);
v_res_1606_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24(v_00_u03b2_1601_, v_a_boxed_1605_, v_b_1603_, v_x_1604_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28(lean_object* v_00_u03b2_1607_, lean_object* v_i_1608_, lean_object* v_source_1609_, lean_object* v_target_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28___redArg(v_i_1608_, v_source_1609_, v_target_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_1612_, lean_object* v_x_1613_, lean_object* v_x_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29___redArg(v_x_1613_, v_x_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(lean_object* v_s_1616_, lean_object* v_stopPos_1617_, lean_object* v_i_1618_){
_start:
{
uint8_t v___y_1623_; uint8_t v___x_1624_; 
v___x_1624_ = lean_nat_dec_lt(v_i_1618_, v_stopPos_1617_);
if (v___x_1624_ == 0)
{
return v_i_1618_;
}
else
{
uint32_t v___x_1625_; uint8_t v___y_1627_; uint32_t v___x_1632_; uint8_t v___x_1633_; 
v___x_1625_ = lean_string_utf8_get(v_s_1616_, v_i_1618_);
v___x_1632_ = 32;
v___x_1633_ = lean_uint32_dec_eq(v___x_1625_, v___x_1632_);
if (v___x_1633_ == 0)
{
uint32_t v___x_1634_; uint8_t v___x_1635_; 
v___x_1634_ = 9;
v___x_1635_ = lean_uint32_dec_eq(v___x_1625_, v___x_1634_);
v___y_1627_ = v___x_1635_;
goto v___jp_1626_;
}
else
{
v___y_1627_ = v___x_1633_;
goto v___jp_1626_;
}
v___jp_1626_:
{
if (v___y_1627_ == 0)
{
uint32_t v___x_1628_; uint8_t v___x_1629_; 
v___x_1628_ = 13;
v___x_1629_ = lean_uint32_dec_eq(v___x_1625_, v___x_1628_);
if (v___x_1629_ == 0)
{
uint32_t v___x_1630_; uint8_t v___x_1631_; 
v___x_1630_ = 10;
v___x_1631_ = lean_uint32_dec_eq(v___x_1625_, v___x_1630_);
v___y_1623_ = v___x_1631_;
goto v___jp_1622_;
}
else
{
v___y_1623_ = v___x_1629_;
goto v___jp_1622_;
}
}
else
{
goto v___jp_1619_;
}
}
}
v___jp_1619_:
{
lean_object* v___x_1620_; 
v___x_1620_ = lean_string_utf8_next(v_s_1616_, v_i_1618_);
lean_dec(v_i_1618_);
v_i_1618_ = v___x_1620_;
goto _start;
}
v___jp_1622_:
{
if (v___y_1623_ == 0)
{
return v_i_1618_;
}
else
{
goto v___jp_1619_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0___boxed(lean_object* v_s_1636_, lean_object* v_stopPos_1637_, lean_object* v_i_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1636_, v_stopPos_1637_, v_i_1638_);
lean_dec(v_stopPos_1637_);
lean_dec_ref(v_s_1636_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(lean_object* v_s_1640_, lean_object* v_b_1641_, lean_object* v_i_1642_, lean_object* v_r_1643_, lean_object* v_ws_1644_){
_start:
{
uint8_t v___y_1654_; uint8_t v___x_1657_; 
v___x_1657_ = lean_string_utf8_at_end(v_s_1640_, v_i_1642_);
if (v___x_1657_ == 0)
{
uint32_t v___x_1658_; uint8_t v___y_1660_; uint32_t v___x_1665_; uint8_t v___x_1666_; 
v___x_1658_ = lean_string_utf8_get(v_s_1640_, v_i_1642_);
v___x_1665_ = 32;
v___x_1666_ = lean_uint32_dec_eq(v___x_1658_, v___x_1665_);
if (v___x_1666_ == 0)
{
uint32_t v___x_1667_; uint8_t v___x_1668_; 
v___x_1667_ = 9;
v___x_1668_ = lean_uint32_dec_eq(v___x_1658_, v___x_1667_);
v___y_1660_ = v___x_1668_;
goto v___jp_1659_;
}
else
{
v___y_1660_ = v___x_1666_;
goto v___jp_1659_;
}
v___jp_1659_:
{
if (v___y_1660_ == 0)
{
uint32_t v___x_1661_; uint8_t v___x_1662_; 
v___x_1661_ = 13;
v___x_1662_ = lean_uint32_dec_eq(v___x_1658_, v___x_1661_);
if (v___x_1662_ == 0)
{
uint32_t v___x_1663_; uint8_t v___x_1664_; 
v___x_1663_ = 10;
v___x_1664_ = lean_uint32_dec_eq(v___x_1658_, v___x_1663_);
v___y_1654_ = v___x_1664_;
goto v___jp_1653_;
}
else
{
v___y_1654_ = v___x_1662_;
goto v___jp_1653_;
}
}
else
{
goto v___jp_1645_;
}
}
}
else
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = lean_string_utf8_extract(v_s_1640_, v_b_1641_, v_i_1642_);
lean_dec(v_i_1642_);
lean_dec(v_b_1641_);
v___x_1670_ = lean_array_push(v_r_1643_, v___x_1669_);
v___x_1671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
lean_ctor_set(v___x_1671_, 1, v_ws_1644_);
return v___x_1671_;
}
v___jp_1645_:
{
lean_object* v___x_1646_; lean_object* v_e_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v___x_1646_ = lean_string_utf8_byte_size(v_s_1640_);
lean_inc(v_i_1642_);
v_e_1647_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1640_, v___x_1646_, v_i_1642_);
v___x_1648_ = lean_string_utf8_extract(v_s_1640_, v_b_1641_, v_i_1642_);
lean_dec(v_b_1641_);
v___x_1649_ = lean_array_push(v_r_1643_, v___x_1648_);
v___x_1650_ = lean_string_utf8_extract(v_s_1640_, v_i_1642_, v_e_1647_);
lean_dec(v_i_1642_);
v___x_1651_ = lean_array_push(v_ws_1644_, v___x_1650_);
lean_inc(v_e_1647_);
v_b_1641_ = v_e_1647_;
v_i_1642_ = v_e_1647_;
v_r_1643_ = v___x_1649_;
v_ws_1644_ = v___x_1651_;
goto _start;
}
v___jp_1653_:
{
if (v___y_1654_ == 0)
{
lean_object* v___x_1655_; 
v___x_1655_ = lean_string_utf8_next(v_s_1640_, v_i_1642_);
lean_dec(v_i_1642_);
v_i_1642_ = v___x_1655_;
goto _start;
}
else
{
goto v___jp_1645_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux___boxed(lean_object* v_s_1672_, lean_object* v_b_1673_, lean_object* v_i_1674_, lean_object* v_r_1675_, lean_object* v_ws_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1672_, v_b_1673_, v_i_1674_, v_r_1675_, v_ws_1676_);
lean_dec_ref(v_s_1672_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(lean_object* v_s_1680_){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1681_ = lean_unsigned_to_nat(0u);
v___x_1682_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_1683_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1680_, v___x_1681_, v___x_1681_, v___x_1682_, v___x_1682_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___boxed(lean_object* v_s_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_1684_);
lean_dec_ref(v_s_1684_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(size_t v_sz_1686_, size_t v_i_1687_, lean_object* v_bs_1688_){
_start:
{
uint8_t v___x_1689_; 
v___x_1689_ = lean_usize_dec_lt(v_i_1687_, v_sz_1686_);
if (v___x_1689_ == 0)
{
return v_bs_1688_;
}
else
{
lean_object* v_v_1690_; lean_object* v_fst_1691_; lean_object* v_snd_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1726_; 
v_v_1690_ = lean_array_uget(v_bs_1688_, v_i_1687_);
v_fst_1691_ = lean_ctor_get(v_v_1690_, 0);
v_snd_1692_ = lean_ctor_get(v_v_1690_, 1);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_v_1690_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1694_ = v_v_1690_;
v_isShared_1695_ = v_isSharedCheck_1726_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_snd_1692_);
lean_inc(v_fst_1691_);
lean_dec(v_v_1690_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1726_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1696_; lean_object* v_bs_x27_1697_; lean_object* v___y_1699_; lean_object* v___x_1704_; lean_object* v___x_1705_; uint8_t v___x_1706_; 
v___x_1696_ = lean_unsigned_to_nat(0u);
v_bs_x27_1697_ = lean_array_uset(v_bs_1688_, v_i_1687_, v___x_1696_);
v___x_1704_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_1705_ = lean_array_get_size(v_snd_1692_);
v___x_1706_ = lean_nat_dec_lt(v___x_1696_, v___x_1705_);
if (v___x_1706_ == 0)
{
lean_object* v___x_1708_; 
lean_dec(v_snd_1692_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 1, v___x_1704_);
v___x_1708_ = v___x_1694_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_fst_1691_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v___x_1704_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
v___y_1699_ = v___x_1708_;
goto v___jp_1698_;
}
}
else
{
uint8_t v___x_1710_; 
v___x_1710_ = lean_nat_dec_le(v___x_1705_, v___x_1705_);
if (v___x_1710_ == 0)
{
if (v___x_1706_ == 0)
{
lean_object* v___x_1712_; 
lean_dec(v_snd_1692_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 1, v___x_1704_);
v___x_1712_ = v___x_1694_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_fst_1691_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v___x_1704_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
v___y_1699_ = v___x_1712_;
goto v___jp_1698_;
}
}
else
{
size_t v___x_1714_; size_t v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1718_; 
v___x_1714_ = ((size_t)0ULL);
v___x_1715_ = lean_usize_of_nat(v___x_1705_);
v___x_1716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_1692_, v___x_1714_, v___x_1715_, v___x_1704_);
lean_dec(v_snd_1692_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 1, v___x_1716_);
v___x_1718_ = v___x_1694_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_fst_1691_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
v___y_1699_ = v___x_1718_;
goto v___jp_1698_;
}
}
}
else
{
size_t v___x_1720_; size_t v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1720_ = ((size_t)0ULL);
v___x_1721_ = lean_usize_of_nat(v___x_1705_);
v___x_1722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_1692_, v___x_1720_, v___x_1721_, v___x_1704_);
lean_dec(v_snd_1692_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 1, v___x_1722_);
v___x_1724_ = v___x_1694_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_fst_1691_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
v___y_1699_ = v___x_1724_;
goto v___jp_1698_;
}
}
}
v___jp_1698_:
{
size_t v___x_1700_; size_t v___x_1701_; lean_object* v___x_1702_; 
v___x_1700_ = ((size_t)1ULL);
v___x_1701_ = lean_usize_add(v_i_1687_, v___x_1700_);
v___x_1702_ = lean_array_uset(v_bs_x27_1697_, v_i_1687_, v___y_1699_);
v_i_1687_ = v___x_1701_;
v_bs_1688_ = v___x_1702_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0___boxed(lean_object* v_sz_1727_, lean_object* v_i_1728_, lean_object* v_bs_1729_){
_start:
{
size_t v_sz_boxed_1730_; size_t v_i_boxed_1731_; lean_object* v_res_1732_; 
v_sz_boxed_1730_ = lean_unbox_usize(v_sz_1727_);
lean_dec(v_sz_1727_);
v_i_boxed_1731_ = lean_unbox_usize(v_i_1728_);
lean_dec(v_i_1728_);
v_res_1732_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_boxed_1730_, v_i_boxed_1731_, v_bs_1729_);
return v_res_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(size_t v_sz_1733_, size_t v_i_1734_, lean_object* v_bs_1735_){
_start:
{
uint8_t v___x_1736_; 
v___x_1736_ = lean_usize_dec_lt(v_i_1734_, v_sz_1733_);
if (v___x_1736_ == 0)
{
return v_bs_1735_;
}
else
{
lean_object* v_v_1737_; lean_object* v___x_1738_; lean_object* v_bs_x27_1739_; uint8_t v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; size_t v___x_1743_; size_t v___x_1744_; lean_object* v___x_1745_; 
v_v_1737_ = lean_array_uget(v_bs_1735_, v_i_1734_);
v___x_1738_ = lean_unsigned_to_nat(0u);
v_bs_x27_1739_ = lean_array_uset(v_bs_1735_, v_i_1734_, v___x_1738_);
v___x_1740_ = 0;
v___x_1741_ = lean_box(v___x_1740_);
v___x_1742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1742_, 0, v___x_1741_);
lean_ctor_set(v___x_1742_, 1, v_v_1737_);
v___x_1743_ = ((size_t)1ULL);
v___x_1744_ = lean_usize_add(v_i_1734_, v___x_1743_);
v___x_1745_ = lean_array_uset(v_bs_x27_1739_, v_i_1734_, v___x_1742_);
v_i_1734_ = v___x_1744_;
v_bs_1735_ = v___x_1745_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8___boxed(lean_object* v_sz_1747_, lean_object* v_i_1748_, lean_object* v_bs_1749_){
_start:
{
size_t v_sz_boxed_1750_; size_t v_i_boxed_1751_; lean_object* v_res_1752_; 
v_sz_boxed_1750_ = lean_unbox_usize(v_sz_1747_);
lean_dec(v_sz_1747_);
v_i_boxed_1751_ = lean_unbox_usize(v_i_1748_);
lean_dec(v_i_1748_);
v_res_1752_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_boxed_1750_, v_i_boxed_1751_, v_bs_1749_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(lean_object* v___x_1753_, lean_object* v_original_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v_fst_1756_; lean_object* v_snd_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1776_; 
v_fst_1756_ = lean_ctor_get(v_a_1755_, 0);
v_snd_1757_ = lean_ctor_get(v_a_1755_, 1);
v_isSharedCheck_1776_ = !lean_is_exclusive(v_a_1755_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1759_ = v_a_1755_;
v_isShared_1760_ = v_isSharedCheck_1776_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_snd_1757_);
lean_inc(v_fst_1756_);
lean_dec(v_a_1755_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1776_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
uint8_t v___x_1761_; 
v___x_1761_ = lean_nat_dec_lt(v_snd_1757_, v___x_1753_);
if (v___x_1761_ == 0)
{
lean_object* v___x_1763_; 
if (v_isShared_1760_ == 0)
{
v___x_1763_ = v___x_1759_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_fst_1756_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_snd_1757_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
else
{
uint8_t v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1769_; 
v___x_1765_ = 1;
v___x_1766_ = lean_array_fget_borrowed(v_original_1754_, v_snd_1757_);
v___x_1767_ = lean_box(v___x_1765_);
lean_inc(v___x_1766_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 1, v___x_1766_);
lean_ctor_set(v___x_1759_, 0, v___x_1767_);
v___x_1769_ = v___x_1759_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v___x_1767_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v___x_1766_);
v___x_1769_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1770_ = lean_array_push(v_fst_1756_, v___x_1769_);
v___x_1771_ = lean_unsigned_to_nat(1u);
v___x_1772_ = lean_nat_add(v_snd_1757_, v___x_1771_);
lean_dec(v_snd_1757_);
v___x_1773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1773_, 0, v___x_1770_);
lean_ctor_set(v___x_1773_, 1, v___x_1772_);
v_a_1755_ = v___x_1773_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg___boxed(lean_object* v___x_1777_, lean_object* v_original_1778_, lean_object* v_a_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_1777_, v_original_1778_, v_a_1779_);
lean_dec_ref(v_original_1778_);
lean_dec(v___x_1777_);
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(lean_object* v___x_1781_, lean_object* v_edited_1782_, lean_object* v_a_1783_){
_start:
{
lean_object* v_fst_1784_; lean_object* v_snd_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1804_; 
v_fst_1784_ = lean_ctor_get(v_a_1783_, 0);
v_snd_1785_ = lean_ctor_get(v_a_1783_, 1);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_a_1783_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1787_ = v_a_1783_;
v_isShared_1788_ = v_isSharedCheck_1804_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_snd_1785_);
lean_inc(v_fst_1784_);
lean_dec(v_a_1783_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1804_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
uint8_t v___x_1789_; 
v___x_1789_ = lean_nat_dec_lt(v_snd_1785_, v___x_1781_);
if (v___x_1789_ == 0)
{
lean_object* v___x_1791_; 
if (v_isShared_1788_ == 0)
{
v___x_1791_ = v___x_1787_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_fst_1784_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_snd_1785_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
else
{
uint8_t v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1797_; 
v___x_1793_ = 0;
v___x_1794_ = lean_array_fget_borrowed(v_edited_1782_, v_snd_1785_);
v___x_1795_ = lean_box(v___x_1793_);
lean_inc(v___x_1794_);
if (v_isShared_1788_ == 0)
{
lean_ctor_set(v___x_1787_, 1, v___x_1794_);
lean_ctor_set(v___x_1787_, 0, v___x_1795_);
v___x_1797_ = v___x_1787_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1795_);
lean_ctor_set(v_reuseFailAlloc_1803_, 1, v___x_1794_);
v___x_1797_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1798_ = lean_array_push(v_fst_1784_, v___x_1797_);
v___x_1799_ = lean_unsigned_to_nat(1u);
v___x_1800_ = lean_nat_add(v_snd_1785_, v___x_1799_);
lean_dec(v_snd_1785_);
v___x_1801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1798_);
lean_ctor_set(v___x_1801_, 1, v___x_1800_);
v_a_1783_ = v___x_1801_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg___boxed(lean_object* v___x_1805_, lean_object* v_edited_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_1805_, v_edited_1806_, v_a_1807_);
lean_dec_ref(v_edited_1806_);
lean_dec(v___x_1805_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(lean_object* v_original_1809_, lean_object* v___x_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_){
_start:
{
lean_object* v_fst_1813_; lean_object* v_snd_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1839_; 
v_fst_1813_ = lean_ctor_get(v_a_1812_, 0);
v_snd_1814_ = lean_ctor_get(v_a_1812_, 1);
v_isSharedCheck_1839_ = !lean_is_exclusive(v_a_1812_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1816_ = v_a_1812_;
v_isShared_1817_ = v_isSharedCheck_1839_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_snd_1814_);
lean_inc(v_fst_1813_);
lean_dec(v_a_1812_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1839_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; uint8_t v___y_1820_; uint8_t v___x_1835_; 
v___x_1818_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_1835_ = lean_nat_dec_lt(v_snd_1814_, v___x_1810_);
if (v___x_1835_ == 0)
{
v___y_1820_ = v___x_1835_;
goto v___jp_1819_;
}
else
{
lean_object* v___x_1836_; uint8_t v___x_1837_; 
v___x_1836_ = lean_array_get_borrowed(v___x_1818_, v_original_1809_, v_snd_1814_);
v___x_1837_ = lean_string_dec_eq(v___x_1836_, v_a_1811_);
if (v___x_1837_ == 0)
{
v___y_1820_ = v___x_1835_;
goto v___jp_1819_;
}
else
{
lean_object* v___x_1838_; 
lean_del_object(v___x_1816_);
v___x_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1838_, 0, v_fst_1813_);
lean_ctor_set(v___x_1838_, 1, v_snd_1814_);
return v___x_1838_;
}
}
v___jp_1819_:
{
if (v___y_1820_ == 0)
{
lean_object* v___x_1822_; 
if (v_isShared_1817_ == 0)
{
v___x_1822_ = v___x_1816_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_fst_1813_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_snd_1814_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
else
{
uint8_t v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1824_ = 1;
v___x_1825_ = lean_array_get_borrowed(v___x_1818_, v_original_1809_, v_snd_1814_);
v___x_1826_ = lean_box(v___x_1824_);
lean_inc(v___x_1825_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 1, v___x_1825_);
lean_ctor_set(v___x_1816_, 0, v___x_1826_);
v___x_1828_ = v___x_1816_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1826_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v___x_1825_);
v___x_1828_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1829_ = lean_array_push(v_fst_1813_, v___x_1828_);
v___x_1830_ = lean_unsigned_to_nat(1u);
v___x_1831_ = lean_nat_add(v_snd_1814_, v___x_1830_);
lean_dec(v_snd_1814_);
v___x_1832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1829_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
v_a_1812_ = v___x_1832_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg___boxed(lean_object* v_original_1840_, lean_object* v___x_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v_original_1840_, v___x_1841_, v_a_1842_, v_a_1843_);
lean_dec_ref(v_a_1842_);
lean_dec(v___x_1841_);
lean_dec_ref(v_original_1840_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(lean_object* v_edited_1845_, lean_object* v___x_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v_fst_1849_; lean_object* v_snd_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1875_; 
v_fst_1849_ = lean_ctor_get(v_a_1848_, 0);
v_snd_1850_ = lean_ctor_get(v_a_1848_, 1);
v_isSharedCheck_1875_ = !lean_is_exclusive(v_a_1848_);
if (v_isSharedCheck_1875_ == 0)
{
v___x_1852_ = v_a_1848_;
v_isShared_1853_ = v_isSharedCheck_1875_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_snd_1850_);
lean_inc(v_fst_1849_);
lean_dec(v_a_1848_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1875_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; uint8_t v___y_1856_; uint8_t v___x_1871_; 
v___x_1854_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_1871_ = lean_nat_dec_lt(v_snd_1850_, v___x_1846_);
if (v___x_1871_ == 0)
{
v___y_1856_ = v___x_1871_;
goto v___jp_1855_;
}
else
{
lean_object* v___x_1872_; uint8_t v___x_1873_; 
v___x_1872_ = lean_array_get_borrowed(v___x_1854_, v_edited_1845_, v_snd_1850_);
v___x_1873_ = lean_string_dec_eq(v___x_1872_, v_a_1847_);
if (v___x_1873_ == 0)
{
v___y_1856_ = v___x_1871_;
goto v___jp_1855_;
}
else
{
lean_object* v___x_1874_; 
lean_del_object(v___x_1852_);
v___x_1874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1874_, 0, v_fst_1849_);
lean_ctor_set(v___x_1874_, 1, v_snd_1850_);
return v___x_1874_;
}
}
v___jp_1855_:
{
if (v___y_1856_ == 0)
{
lean_object* v___x_1858_; 
if (v_isShared_1853_ == 0)
{
v___x_1858_ = v___x_1852_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_fst_1849_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_snd_1850_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
else
{
uint8_t v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1864_; 
v___x_1860_ = 0;
v___x_1861_ = lean_array_get_borrowed(v___x_1854_, v_edited_1845_, v_snd_1850_);
v___x_1862_ = lean_box(v___x_1860_);
lean_inc(v___x_1861_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 1, v___x_1861_);
lean_ctor_set(v___x_1852_, 0, v___x_1862_);
v___x_1864_ = v___x_1852_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1862_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v___x_1861_);
v___x_1864_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1865_ = lean_array_push(v_fst_1849_, v___x_1864_);
v___x_1866_ = lean_unsigned_to_nat(1u);
v___x_1867_ = lean_nat_add(v_snd_1850_, v___x_1866_);
lean_dec(v_snd_1850_);
v___x_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1865_);
lean_ctor_set(v___x_1868_, 1, v___x_1867_);
v_a_1848_ = v___x_1868_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg___boxed(lean_object* v_edited_1876_, lean_object* v___x_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(v_edited_1876_, v___x_1877_, v_a_1878_, v_a_1879_);
lean_dec_ref(v_a_1878_);
lean_dec(v___x_1877_);
lean_dec_ref(v_edited_1876_);
return v_res_1880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(lean_object* v_original_1881_, lean_object* v___x_1882_, lean_object* v_edited_1883_, lean_object* v___x_1884_, lean_object* v_as_1885_, size_t v_sz_1886_, size_t v_i_1887_, lean_object* v_b_1888_){
_start:
{
uint8_t v___x_1889_; 
v___x_1889_ = lean_usize_dec_lt(v_i_1887_, v_sz_1886_);
if (v___x_1889_ == 0)
{
return v_b_1888_;
}
else
{
lean_object* v_snd_1890_; lean_object* v_fst_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1938_; 
v_snd_1890_ = lean_ctor_get(v_b_1888_, 1);
v_fst_1891_ = lean_ctor_get(v_b_1888_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_b_1888_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1893_ = v_b_1888_;
v_isShared_1894_ = v_isSharedCheck_1938_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_snd_1890_);
lean_inc(v_fst_1891_);
lean_dec(v_b_1888_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1938_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v_fst_1895_; lean_object* v_snd_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1937_; 
v_fst_1895_ = lean_ctor_get(v_snd_1890_, 0);
v_snd_1896_ = lean_ctor_get(v_snd_1890_, 1);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_snd_1890_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1898_ = v_snd_1890_;
v_isShared_1899_ = v_isSharedCheck_1937_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_snd_1896_);
lean_inc(v_fst_1895_);
lean_dec(v_snd_1890_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1937_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v_a_1900_; lean_object* v___x_1902_; 
v_a_1900_ = lean_array_uget_borrowed(v_as_1885_, v_i_1887_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 1, v_fst_1895_);
lean_ctor_set(v___x_1898_, 0, v_fst_1891_);
v___x_1902_ = v___x_1898_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_fst_1891_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_fst_1895_);
v___x_1902_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
lean_object* v___x_1903_; lean_object* v_fst_1904_; lean_object* v_snd_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1935_; 
v___x_1903_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v_original_1881_, v___x_1882_, v_a_1900_, v___x_1902_);
v_fst_1904_ = lean_ctor_get(v___x_1903_, 0);
v_snd_1905_ = lean_ctor_get(v___x_1903_, 1);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1907_ = v___x_1903_;
v_isShared_1908_ = v_isSharedCheck_1935_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_snd_1905_);
lean_inc(v_fst_1904_);
lean_dec(v___x_1903_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1935_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1910_; 
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 1, v_snd_1896_);
v___x_1910_ = v___x_1907_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_fst_1904_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_snd_1896_);
v___x_1910_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1911_; lean_object* v_fst_1912_; lean_object* v_snd_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1933_; 
v___x_1911_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(v_edited_1883_, v___x_1884_, v_a_1900_, v___x_1910_);
v_fst_1912_ = lean_ctor_get(v___x_1911_, 0);
v_snd_1913_ = lean_ctor_get(v___x_1911_, 1);
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1915_ = v___x_1911_;
v_isShared_1916_ = v_isSharedCheck_1933_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_snd_1913_);
lean_inc(v_fst_1912_);
lean_dec(v___x_1911_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1933_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
uint8_t v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1917_ = 2;
v___x_1918_ = lean_box(v___x_1917_);
lean_inc(v_a_1900_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 1, v_a_1900_);
lean_ctor_set(v___x_1915_, 0, v___x_1918_);
v___x_1920_ = v___x_1915_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1918_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_a_1900_);
v___x_1920_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1921_ = lean_array_push(v_fst_1912_, v___x_1920_);
v___x_1922_ = lean_unsigned_to_nat(1u);
v___x_1923_ = lean_nat_add(v_snd_1905_, v___x_1922_);
lean_dec(v_snd_1905_);
v___x_1924_ = lean_nat_add(v_snd_1913_, v___x_1922_);
lean_dec(v_snd_1913_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 1, v___x_1924_);
lean_ctor_set(v___x_1893_, 0, v___x_1923_);
v___x_1926_ = v___x_1893_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1923_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v___x_1924_);
v___x_1926_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1927_; size_t v___x_1928_; size_t v___x_1929_; 
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1921_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = ((size_t)1ULL);
v___x_1929_ = lean_usize_add(v_i_1887_, v___x_1928_);
v_i_1887_ = v___x_1929_;
v_b_1888_ = v___x_1927_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14___boxed(lean_object* v_original_1939_, lean_object* v___x_1940_, lean_object* v_edited_1941_, lean_object* v___x_1942_, lean_object* v_as_1943_, lean_object* v_sz_1944_, lean_object* v_i_1945_, lean_object* v_b_1946_){
_start:
{
size_t v_sz_boxed_1947_; size_t v_i_boxed_1948_; lean_object* v_res_1949_; 
v_sz_boxed_1947_ = lean_unbox_usize(v_sz_1944_);
lean_dec(v_sz_1944_);
v_i_boxed_1948_ = lean_unbox_usize(v_i_1945_);
lean_dec(v_i_1945_);
v_res_1949_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v_original_1939_, v___x_1940_, v_edited_1941_, v___x_1942_, v_as_1943_, v_sz_boxed_1947_, v_i_boxed_1948_, v_b_1946_);
lean_dec_ref(v_as_1943_);
lean_dec(v___x_1942_);
lean_dec_ref(v_edited_1941_);
lean_dec(v___x_1940_);
lean_dec_ref(v_original_1939_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(lean_object* v_edited_1950_, lean_object* v___x_1951_, lean_object* v_original_1952_, lean_object* v___x_1953_, lean_object* v_as_1954_, size_t v_sz_1955_, size_t v_i_1956_, lean_object* v_b_1957_){
_start:
{
uint8_t v___x_1958_; 
v___x_1958_ = lean_usize_dec_lt(v_i_1956_, v_sz_1955_);
if (v___x_1958_ == 0)
{
return v_b_1957_;
}
else
{
lean_object* v_snd_1959_; lean_object* v_fst_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_2007_; 
v_snd_1959_ = lean_ctor_get(v_b_1957_, 1);
v_fst_1960_ = lean_ctor_get(v_b_1957_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v_b_1957_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1962_ = v_b_1957_;
v_isShared_1963_ = v_isSharedCheck_2007_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_snd_1959_);
lean_inc(v_fst_1960_);
lean_dec(v_b_1957_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_2007_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v_fst_1964_; lean_object* v_snd_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_2006_; 
v_fst_1964_ = lean_ctor_get(v_snd_1959_, 0);
v_snd_1965_ = lean_ctor_get(v_snd_1959_, 1);
v_isSharedCheck_2006_ = !lean_is_exclusive(v_snd_1959_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_1967_ = v_snd_1959_;
v_isShared_1968_ = v_isSharedCheck_2006_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_snd_1965_);
lean_inc(v_fst_1964_);
lean_dec(v_snd_1959_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_2006_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v_a_1969_; lean_object* v___x_1971_; 
v_a_1969_ = lean_array_uget_borrowed(v_as_1954_, v_i_1956_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 1, v_fst_1964_);
lean_ctor_set(v___x_1967_, 0, v_fst_1960_);
v___x_1971_ = v___x_1967_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_fst_1960_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_fst_1964_);
v___x_1971_ = v_reuseFailAlloc_2005_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
lean_object* v___x_1972_; lean_object* v_fst_1973_; lean_object* v_snd_1974_; lean_object* v___x_1976_; uint8_t v_isShared_1977_; uint8_t v_isSharedCheck_2004_; 
v___x_1972_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v_original_1952_, v___x_1953_, v_a_1969_, v___x_1971_);
v_fst_1973_ = lean_ctor_get(v___x_1972_, 0);
v_snd_1974_ = lean_ctor_get(v___x_1972_, 1);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1976_ = v___x_1972_;
v_isShared_1977_ = v_isSharedCheck_2004_;
goto v_resetjp_1975_;
}
else
{
lean_inc(v_snd_1974_);
lean_inc(v_fst_1973_);
lean_dec(v___x_1972_);
v___x_1976_ = lean_box(0);
v_isShared_1977_ = v_isSharedCheck_2004_;
goto v_resetjp_1975_;
}
v_resetjp_1975_:
{
lean_object* v___x_1979_; 
if (v_isShared_1977_ == 0)
{
lean_ctor_set(v___x_1976_, 1, v_snd_1965_);
v___x_1979_ = v___x_1976_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_fst_1973_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_snd_1965_);
v___x_1979_ = v_reuseFailAlloc_2003_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1980_; lean_object* v_fst_1981_; lean_object* v_snd_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_2002_; 
v___x_1980_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(v_edited_1950_, v___x_1951_, v_a_1969_, v___x_1979_);
v_fst_1981_ = lean_ctor_get(v___x_1980_, 0);
v_snd_1982_ = lean_ctor_get(v___x_1980_, 1);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1984_ = v___x_1980_;
v_isShared_1985_ = v_isSharedCheck_2002_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_snd_1982_);
lean_inc(v_fst_1981_);
lean_dec(v___x_1980_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_2002_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
uint8_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1989_; 
v___x_1986_ = 2;
v___x_1987_ = lean_box(v___x_1986_);
lean_inc(v_a_1969_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 1, v_a_1969_);
lean_ctor_set(v___x_1984_, 0, v___x_1987_);
v___x_1989_ = v___x_1984_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_a_1969_);
v___x_1989_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1990_ = lean_array_push(v_fst_1981_, v___x_1989_);
v___x_1991_ = lean_unsigned_to_nat(1u);
v___x_1992_ = lean_nat_add(v_snd_1974_, v___x_1991_);
lean_dec(v_snd_1974_);
v___x_1993_ = lean_nat_add(v_snd_1982_, v___x_1991_);
lean_dec(v_snd_1982_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 1, v___x_1993_);
lean_ctor_set(v___x_1962_, 0, v___x_1992_);
v___x_1995_ = v___x_1962_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1996_; size_t v___x_1997_; size_t v___x_1998_; lean_object* v___x_1999_; 
v___x_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1990_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
v___x_1997_ = ((size_t)1ULL);
v___x_1998_ = lean_usize_add(v_i_1956_, v___x_1997_);
v___x_1999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v_original_1952_, v___x_1953_, v_edited_1950_, v___x_1951_, v_as_1954_, v_sz_1955_, v___x_1998_, v___x_1996_);
return v___x_1999_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4___boxed(lean_object* v_edited_2008_, lean_object* v___x_2009_, lean_object* v_original_2010_, lean_object* v___x_2011_, lean_object* v_as_2012_, lean_object* v_sz_2013_, lean_object* v_i_2014_, lean_object* v_b_2015_){
_start:
{
size_t v_sz_boxed_2016_; size_t v_i_boxed_2017_; lean_object* v_res_2018_; 
v_sz_boxed_2016_ = lean_unbox_usize(v_sz_2013_);
lean_dec(v_sz_2013_);
v_i_boxed_2017_ = lean_unbox_usize(v_i_2014_);
lean_dec(v_i_2014_);
v_res_2018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v_edited_2008_, v___x_2009_, v_original_2010_, v___x_2011_, v_as_2012_, v_sz_boxed_2016_, v_i_boxed_2017_, v_b_2015_);
lean_dec_ref(v_as_2012_);
lean_dec(v___x_2011_);
lean_dec_ref(v_original_2010_);
lean_dec(v___x_2009_);
lean_dec_ref(v_edited_2008_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(lean_object* v_a_2019_, lean_object* v_b_2020_){
_start:
{
lean_object* v_array_2021_; lean_object* v_start_2022_; lean_object* v_stop_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2036_; 
v_array_2021_ = lean_ctor_get(v_a_2019_, 0);
v_start_2022_ = lean_ctor_get(v_a_2019_, 1);
v_stop_2023_ = lean_ctor_get(v_a_2019_, 2);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_a_2019_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2025_ = v_a_2019_;
v_isShared_2026_ = v_isSharedCheck_2036_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_stop_2023_);
lean_inc(v_start_2022_);
lean_inc(v_array_2021_);
lean_dec(v_a_2019_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2036_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
uint8_t v___x_2027_; 
v___x_2027_ = lean_nat_dec_lt(v_start_2022_, v_stop_2023_);
if (v___x_2027_ == 0)
{
lean_del_object(v___x_2025_);
lean_dec(v_stop_2023_);
lean_dec(v_start_2022_);
lean_dec_ref(v_array_2021_);
return v_b_2020_;
}
else
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2028_ = lean_unsigned_to_nat(1u);
v___x_2029_ = lean_nat_add(v_start_2022_, v___x_2028_);
lean_inc_ref(v_array_2021_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 1, v___x_2029_);
v___x_2031_ = v___x_2025_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_array_2021_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___x_2029_);
lean_ctor_set(v_reuseFailAlloc_2035_, 2, v_stop_2023_);
v___x_2031_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = lean_array_fget(v_array_2021_, v_start_2022_);
lean_dec(v_start_2022_);
lean_dec_ref(v_array_2021_);
v___x_2033_ = lean_array_push(v_b_2020_, v___x_2032_);
v_a_2019_ = v___x_2031_;
v_b_2020_ = v___x_2033_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6(lean_object* v_left_2037_, lean_object* v_right_2038_, lean_object* v_i_2039_){
_start:
{
lean_object* v_start_2040_; lean_object* v_stop_2041_; lean_object* v___x_2042_; uint8_t v___x_2056_; 
v_start_2040_ = lean_ctor_get(v_left_2037_, 1);
v_stop_2041_ = lean_ctor_get(v_left_2037_, 2);
v___x_2042_ = lean_nat_sub(v_stop_2041_, v_start_2040_);
v___x_2056_ = lean_nat_dec_lt(v_i_2039_, v___x_2042_);
if (v___x_2056_ == 0)
{
goto v___jp_2043_;
}
else
{
lean_object* v_start_2057_; lean_object* v_stop_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v_start_2057_ = lean_ctor_get(v_right_2038_, 1);
v_stop_2058_ = lean_ctor_get(v_right_2038_, 2);
v___x_2059_ = lean_nat_sub(v_stop_2058_, v_start_2057_);
v___x_2060_ = lean_nat_dec_lt(v_i_2039_, v___x_2059_);
if (v___x_2060_ == 0)
{
lean_dec(v___x_2059_);
goto v___jp_2043_;
}
else
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; 
v___x_2061_ = lean_nat_sub(v___x_2042_, v_i_2039_);
lean_dec(v___x_2042_);
v___x_2062_ = lean_unsigned_to_nat(1u);
v___x_2063_ = lean_nat_sub(v___x_2061_, v___x_2062_);
v___x_2064_ = l_Subarray_get___redArg(v_left_2037_, v___x_2063_);
lean_dec(v___x_2063_);
v___x_2065_ = lean_nat_sub(v___x_2059_, v_i_2039_);
lean_dec(v___x_2059_);
v___x_2066_ = lean_nat_sub(v___x_2065_, v___x_2062_);
v___x_2067_ = l_Subarray_get___redArg(v_right_2038_, v___x_2066_);
lean_dec(v___x_2066_);
v___x_2068_ = lean_string_dec_eq(v___x_2064_, v___x_2067_);
lean_dec(v___x_2067_);
lean_dec(v___x_2064_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
lean_dec(v_i_2039_);
lean_inc_ref(v_left_2037_);
v___x_2069_ = l_Subarray_take___redArg(v_left_2037_, v___x_2061_);
v___x_2070_ = l_Subarray_take___redArg(v_right_2038_, v___x_2065_);
lean_dec(v___x_2065_);
v___x_2071_ = l_Subarray_drop___redArg(v_left_2037_, v___x_2061_);
lean_dec(v___x_2061_);
v___x_2072_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2073_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v___x_2071_, v___x_2072_);
v___x_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___x_2070_);
lean_ctor_set(v___x_2074_, 1, v___x_2073_);
v___x_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2069_);
lean_ctor_set(v___x_2075_, 1, v___x_2074_);
return v___x_2075_;
}
else
{
lean_object* v___x_2076_; 
lean_dec(v___x_2065_);
lean_dec(v___x_2061_);
v___x_2076_ = lean_nat_add(v_i_2039_, v___x_2062_);
lean_dec(v_i_2039_);
v_i_2039_ = v___x_2076_;
goto _start;
}
}
}
v___jp_2043_:
{
lean_object* v_start_2044_; lean_object* v_stop_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v_start_2044_ = lean_ctor_get(v_right_2038_, 1);
v_stop_2045_ = lean_ctor_get(v_right_2038_, 2);
v___x_2046_ = lean_nat_sub(v___x_2042_, v_i_2039_);
lean_dec(v___x_2042_);
lean_inc_ref(v_left_2037_);
v___x_2047_ = l_Subarray_take___redArg(v_left_2037_, v___x_2046_);
v___x_2048_ = lean_nat_sub(v_stop_2045_, v_start_2044_);
v___x_2049_ = lean_nat_sub(v___x_2048_, v_i_2039_);
lean_dec(v_i_2039_);
lean_dec(v___x_2048_);
v___x_2050_ = l_Subarray_take___redArg(v_right_2038_, v___x_2049_);
lean_dec(v___x_2049_);
v___x_2051_ = l_Subarray_drop___redArg(v_left_2037_, v___x_2046_);
lean_dec(v___x_2046_);
v___x_2052_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2053_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v___x_2051_, v___x_2052_);
v___x_2054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2050_);
lean_ctor_set(v___x_2054_, 1, v___x_2053_);
v___x_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2047_);
lean_ctor_set(v___x_2055_, 1, v___x_2054_);
return v___x_2055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3(lean_object* v_left_2078_, lean_object* v_right_2079_){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2080_ = lean_unsigned_to_nat(0u);
v___x_2081_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6(v_left_2078_, v_right_2079_, v___x_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2_spec__4(lean_object* v_left_2082_, lean_object* v_right_2083_, lean_object* v_pref_2084_){
_start:
{
lean_object* v_start_2085_; lean_object* v_stop_2086_; lean_object* v_i_2087_; lean_object* v___x_2093_; uint8_t v___x_2094_; 
v_start_2085_ = lean_ctor_get(v_left_2082_, 1);
v_stop_2086_ = lean_ctor_get(v_left_2082_, 2);
v_i_2087_ = lean_array_get_size(v_pref_2084_);
v___x_2093_ = lean_nat_sub(v_stop_2086_, v_start_2085_);
v___x_2094_ = lean_nat_dec_lt(v_i_2087_, v___x_2093_);
lean_dec(v___x_2093_);
if (v___x_2094_ == 0)
{
goto v___jp_2088_;
}
else
{
lean_object* v_start_2095_; lean_object* v_stop_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; 
v_start_2095_ = lean_ctor_get(v_right_2083_, 1);
v_stop_2096_ = lean_ctor_get(v_right_2083_, 2);
v___x_2097_ = lean_nat_sub(v_stop_2096_, v_start_2095_);
v___x_2098_ = lean_nat_dec_lt(v_i_2087_, v___x_2097_);
lean_dec(v___x_2097_);
if (v___x_2098_ == 0)
{
goto v___jp_2088_;
}
else
{
lean_object* v___x_2099_; lean_object* v___x_2100_; uint8_t v___x_2101_; 
v___x_2099_ = l_Subarray_get___redArg(v_left_2082_, v_i_2087_);
v___x_2100_ = l_Subarray_get___redArg(v_right_2083_, v_i_2087_);
v___x_2101_ = lean_string_dec_eq(v___x_2099_, v___x_2100_);
lean_dec(v___x_2100_);
if (v___x_2101_ == 0)
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
lean_dec(v___x_2099_);
v___x_2102_ = l_Subarray_drop___redArg(v_left_2082_, v_i_2087_);
v___x_2103_ = l_Subarray_drop___redArg(v_right_2083_, v_i_2087_);
v___x_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2102_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
v___x_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2105_, 0, v_pref_2084_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
return v___x_2105_;
}
else
{
lean_object* v___x_2106_; 
v___x_2106_ = lean_array_push(v_pref_2084_, v___x_2099_);
v_pref_2084_ = v___x_2106_;
goto _start;
}
}
}
v___jp_2088_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2089_ = l_Subarray_drop___redArg(v_left_2082_, v_i_2087_);
v___x_2090_ = l_Subarray_drop___redArg(v_right_2083_, v_i_2087_);
v___x_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2089_);
lean_ctor_set(v___x_2091_, 1, v___x_2090_);
v___x_2092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2092_, 0, v_pref_2084_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
return v___x_2092_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2(lean_object* v_left_2108_, lean_object* v_right_2109_){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2111_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2_spec__4(v_left_2108_, v_right_2109_, v___x_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(lean_object* v_as_x27_2112_, lean_object* v_b_2113_){
_start:
{
if (lean_obj_tag(v_as_x27_2112_) == 0)
{
return v_b_2113_;
}
else
{
lean_object* v_head_2114_; lean_object* v_snd_2115_; lean_object* v_leftIndex_2116_; 
v_head_2114_ = lean_ctor_get(v_as_x27_2112_, 0);
v_snd_2115_ = lean_ctor_get(v_head_2114_, 1);
v_leftIndex_2116_ = lean_ctor_get(v_snd_2115_, 1);
if (lean_obj_tag(v_leftIndex_2116_) == 1)
{
lean_object* v_rightIndex_2117_; 
v_rightIndex_2117_ = lean_ctor_get(v_snd_2115_, 3);
if (lean_obj_tag(v_rightIndex_2117_) == 1)
{
if (lean_obj_tag(v_b_2113_) == 0)
{
lean_object* v_tail_2118_; lean_object* v_fst_2119_; lean_object* v_leftCount_2120_; lean_object* v_rightCount_2121_; lean_object* v_val_2122_; lean_object* v_val_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v_tail_2118_ = lean_ctor_get(v_as_x27_2112_, 1);
v_fst_2119_ = lean_ctor_get(v_head_2114_, 0);
v_leftCount_2120_ = lean_ctor_get(v_snd_2115_, 0);
v_rightCount_2121_ = lean_ctor_get(v_snd_2115_, 2);
v_val_2122_ = lean_ctor_get(v_leftIndex_2116_, 0);
v_val_2123_ = lean_ctor_get(v_rightIndex_2117_, 0);
v___x_2124_ = lean_nat_add(v_leftCount_2120_, v_rightCount_2121_);
lean_inc(v_val_2123_);
lean_inc(v_val_2122_);
v___x_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2125_, 0, v_val_2122_);
lean_ctor_set(v___x_2125_, 1, v_val_2123_);
lean_inc(v_fst_2119_);
v___x_2126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2126_, 0, v_fst_2119_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2124_);
lean_ctor_set(v___x_2127_, 1, v___x_2126_);
v___x_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
v_as_x27_2112_ = v_tail_2118_;
v_b_2113_ = v___x_2128_;
goto _start;
}
else
{
lean_object* v_val_2130_; lean_object* v_tail_2131_; lean_object* v_fst_2132_; lean_object* v_leftCount_2133_; lean_object* v_rightCount_2134_; lean_object* v_val_2135_; lean_object* v_val_2136_; lean_object* v_fst_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2158_; 
v_val_2130_ = lean_ctor_get(v_b_2113_, 0);
lean_inc(v_val_2130_);
v_tail_2131_ = lean_ctor_get(v_as_x27_2112_, 1);
v_fst_2132_ = lean_ctor_get(v_head_2114_, 0);
v_leftCount_2133_ = lean_ctor_get(v_snd_2115_, 0);
v_rightCount_2134_ = lean_ctor_get(v_snd_2115_, 2);
v_val_2135_ = lean_ctor_get(v_leftIndex_2116_, 0);
v_val_2136_ = lean_ctor_get(v_rightIndex_2117_, 0);
v_fst_2137_ = lean_ctor_get(v_val_2130_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_val_2130_);
if (v_isSharedCheck_2158_ == 0)
{
lean_object* v_unused_2159_; 
v_unused_2159_ = lean_ctor_get(v_val_2130_, 1);
lean_dec(v_unused_2159_);
v___x_2139_ = v_val_2130_;
v_isShared_2140_ = v_isSharedCheck_2158_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_fst_2137_);
lean_dec(v_val_2130_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2158_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2141_ = lean_nat_add(v_leftCount_2133_, v_rightCount_2134_);
v___x_2142_ = lean_nat_dec_lt(v___x_2141_, v_fst_2137_);
lean_dec(v_fst_2137_);
if (v___x_2142_ == 0)
{
lean_dec(v___x_2141_);
lean_del_object(v___x_2139_);
v_as_x27_2112_ = v_tail_2131_;
goto _start;
}
else
{
lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2156_; 
v_isSharedCheck_2156_ = !lean_is_exclusive(v_b_2113_);
if (v_isSharedCheck_2156_ == 0)
{
lean_object* v_unused_2157_; 
v_unused_2157_ = lean_ctor_get(v_b_2113_, 0);
lean_dec(v_unused_2157_);
v___x_2145_ = v_b_2113_;
v_isShared_2146_ = v_isSharedCheck_2156_;
goto v_resetjp_2144_;
}
else
{
lean_dec(v_b_2113_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2156_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
lean_inc(v_val_2136_);
lean_inc(v_val_2135_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 1, v_val_2136_);
lean_ctor_set(v___x_2139_, 0, v_val_2135_);
v___x_2148_ = v___x_2139_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_val_2135_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_val_2136_);
v___x_2148_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2152_; 
lean_inc(v_fst_2132_);
v___x_2149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2149_, 0, v_fst_2132_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2141_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 0, v___x_2150_);
v___x_2152_ = v___x_2145_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
v_as_x27_2112_ = v_tail_2131_;
v_b_2113_ = v___x_2152_;
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
lean_object* v_tail_2160_; 
v_tail_2160_ = lean_ctor_get(v_as_x27_2112_, 1);
v_as_x27_2112_ = v_tail_2160_;
goto _start;
}
}
else
{
lean_object* v_tail_2162_; 
v_tail_2162_ = lean_ctor_get(v_as_x27_2112_, 1);
v_as_x27_2112_ = v_tail_2162_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2164_, lean_object* v_b_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(v_as_x27_2164_, v_b_2165_);
lean_dec(v_as_x27_2164_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(lean_object* v_a_2167_, lean_object* v_b_2168_, lean_object* v_x_2169_){
_start:
{
if (lean_obj_tag(v_x_2169_) == 0)
{
lean_dec(v_b_2168_);
lean_dec_ref(v_a_2167_);
return v_x_2169_;
}
else
{
lean_object* v_key_2170_; lean_object* v_value_2171_; lean_object* v_tail_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2184_; 
v_key_2170_ = lean_ctor_get(v_x_2169_, 0);
v_value_2171_ = lean_ctor_get(v_x_2169_, 1);
v_tail_2172_ = lean_ctor_get(v_x_2169_, 2);
v_isSharedCheck_2184_ = !lean_is_exclusive(v_x_2169_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2174_ = v_x_2169_;
v_isShared_2175_ = v_isSharedCheck_2184_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_tail_2172_);
lean_inc(v_value_2171_);
lean_inc(v_key_2170_);
lean_dec(v_x_2169_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2184_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
uint8_t v___x_2176_; 
v___x_2176_ = lean_string_dec_eq(v_key_2170_, v_a_2167_);
if (v___x_2176_ == 0)
{
lean_object* v___x_2177_; lean_object* v___x_2179_; 
v___x_2177_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(v_a_2167_, v_b_2168_, v_tail_2172_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 2, v___x_2177_);
v___x_2179_ = v___x_2174_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_key_2170_);
lean_ctor_set(v_reuseFailAlloc_2180_, 1, v_value_2171_);
lean_ctor_set(v_reuseFailAlloc_2180_, 2, v___x_2177_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
else
{
lean_object* v___x_2182_; 
lean_dec(v_value_2171_);
lean_dec(v_key_2170_);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 1, v_b_2168_);
lean_ctor_set(v___x_2174_, 0, v_a_2167_);
v___x_2182_ = v___x_2174_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2167_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_b_2168_);
lean_ctor_set(v_reuseFailAlloc_2183_, 2, v_tail_2172_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(lean_object* v_a_2185_, lean_object* v_x_2186_){
_start:
{
if (lean_obj_tag(v_x_2186_) == 0)
{
uint8_t v___x_2187_; 
v___x_2187_ = 0;
return v___x_2187_;
}
else
{
lean_object* v_key_2188_; lean_object* v_tail_2189_; uint8_t v___x_2190_; 
v_key_2188_ = lean_ctor_get(v_x_2186_, 0);
v_tail_2189_ = lean_ctor_get(v_x_2186_, 2);
v___x_2190_ = lean_string_dec_eq(v_key_2188_, v_a_2185_);
if (v___x_2190_ == 0)
{
v_x_2186_ = v_tail_2189_;
goto _start;
}
else
{
return v___x_2190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg___boxed(lean_object* v_a_2192_, lean_object* v_x_2193_){
_start:
{
uint8_t v_res_2194_; lean_object* v_r_2195_; 
v_res_2194_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(v_a_2192_, v_x_2193_);
lean_dec(v_x_2193_);
lean_dec_ref(v_a_2192_);
v_r_2195_ = lean_box(v_res_2194_);
return v_r_2195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29___redArg(lean_object* v_x_2196_, lean_object* v_x_2197_){
_start:
{
if (lean_obj_tag(v_x_2197_) == 0)
{
return v_x_2196_;
}
else
{
lean_object* v_key_2198_; lean_object* v_value_2199_; lean_object* v_tail_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2223_; 
v_key_2198_ = lean_ctor_get(v_x_2197_, 0);
v_value_2199_ = lean_ctor_get(v_x_2197_, 1);
v_tail_2200_ = lean_ctor_get(v_x_2197_, 2);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_x_2197_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2202_ = v_x_2197_;
v_isShared_2203_ = v_isSharedCheck_2223_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_tail_2200_);
lean_inc(v_value_2199_);
lean_inc(v_key_2198_);
lean_dec(v_x_2197_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2223_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2204_; uint64_t v___x_2205_; uint64_t v___x_2206_; uint64_t v___x_2207_; uint64_t v_fold_2208_; uint64_t v___x_2209_; uint64_t v___x_2210_; uint64_t v___x_2211_; size_t v___x_2212_; size_t v___x_2213_; size_t v___x_2214_; size_t v___x_2215_; size_t v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2219_; 
v___x_2204_ = lean_array_get_size(v_x_2196_);
v___x_2205_ = lean_string_hash(v_key_2198_);
v___x_2206_ = 32ULL;
v___x_2207_ = lean_uint64_shift_right(v___x_2205_, v___x_2206_);
v_fold_2208_ = lean_uint64_xor(v___x_2205_, v___x_2207_);
v___x_2209_ = 16ULL;
v___x_2210_ = lean_uint64_shift_right(v_fold_2208_, v___x_2209_);
v___x_2211_ = lean_uint64_xor(v_fold_2208_, v___x_2210_);
v___x_2212_ = lean_uint64_to_usize(v___x_2211_);
v___x_2213_ = lean_usize_of_nat(v___x_2204_);
v___x_2214_ = ((size_t)1ULL);
v___x_2215_ = lean_usize_sub(v___x_2213_, v___x_2214_);
v___x_2216_ = lean_usize_land(v___x_2212_, v___x_2215_);
v___x_2217_ = lean_array_uget_borrowed(v_x_2196_, v___x_2216_);
lean_inc(v___x_2217_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 2, v___x_2217_);
v___x_2219_ = v___x_2202_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_key_2198_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_value_2199_);
lean_ctor_set(v_reuseFailAlloc_2222_, 2, v___x_2217_);
v___x_2219_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
lean_object* v___x_2220_; 
v___x_2220_ = lean_array_uset(v_x_2196_, v___x_2216_, v___x_2219_);
v_x_2196_ = v___x_2220_;
v_x_2197_ = v_tail_2200_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28___redArg(lean_object* v_i_2224_, lean_object* v_source_2225_, lean_object* v_target_2226_){
_start:
{
lean_object* v___x_2227_; uint8_t v___x_2228_; 
v___x_2227_ = lean_array_get_size(v_source_2225_);
v___x_2228_ = lean_nat_dec_lt(v_i_2224_, v___x_2227_);
if (v___x_2228_ == 0)
{
lean_dec_ref(v_source_2225_);
lean_dec(v_i_2224_);
return v_target_2226_;
}
else
{
lean_object* v_es_2229_; lean_object* v___x_2230_; lean_object* v_source_2231_; lean_object* v_target_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v_es_2229_ = lean_array_fget(v_source_2225_, v_i_2224_);
v___x_2230_ = lean_box(0);
v_source_2231_ = lean_array_fset(v_source_2225_, v_i_2224_, v___x_2230_);
v_target_2232_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29___redArg(v_target_2226_, v_es_2229_);
v___x_2233_ = lean_unsigned_to_nat(1u);
v___x_2234_ = lean_nat_add(v_i_2224_, v___x_2233_);
lean_dec(v_i_2224_);
v_i_2224_ = v___x_2234_;
v_source_2225_ = v_source_2231_;
v_target_2226_ = v_target_2232_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23___redArg(lean_object* v_data_2236_){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v_nbuckets_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2237_ = lean_array_get_size(v_data_2236_);
v___x_2238_ = lean_unsigned_to_nat(2u);
v_nbuckets_2239_ = lean_nat_mul(v___x_2237_, v___x_2238_);
v___x_2240_ = lean_unsigned_to_nat(0u);
v___x_2241_ = lean_box(0);
v___x_2242_ = lean_mk_array(v_nbuckets_2239_, v___x_2241_);
v___x_2243_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28___redArg(v___x_2240_, v_data_2236_, v___x_2242_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(lean_object* v_m_2244_, lean_object* v_a_2245_, lean_object* v_b_2246_){
_start:
{
lean_object* v_size_2247_; lean_object* v_buckets_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2291_; 
v_size_2247_ = lean_ctor_get(v_m_2244_, 0);
v_buckets_2248_ = lean_ctor_get(v_m_2244_, 1);
v_isSharedCheck_2291_ = !lean_is_exclusive(v_m_2244_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2250_ = v_m_2244_;
v_isShared_2251_ = v_isSharedCheck_2291_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_buckets_2248_);
lean_inc(v_size_2247_);
lean_dec(v_m_2244_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2291_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2252_; uint64_t v___x_2253_; uint64_t v___x_2254_; uint64_t v___x_2255_; uint64_t v_fold_2256_; uint64_t v___x_2257_; uint64_t v___x_2258_; uint64_t v___x_2259_; size_t v___x_2260_; size_t v___x_2261_; size_t v___x_2262_; size_t v___x_2263_; size_t v___x_2264_; lean_object* v_bkt_2265_; uint8_t v___x_2266_; 
v___x_2252_ = lean_array_get_size(v_buckets_2248_);
v___x_2253_ = lean_string_hash(v_a_2245_);
v___x_2254_ = 32ULL;
v___x_2255_ = lean_uint64_shift_right(v___x_2253_, v___x_2254_);
v_fold_2256_ = lean_uint64_xor(v___x_2253_, v___x_2255_);
v___x_2257_ = 16ULL;
v___x_2258_ = lean_uint64_shift_right(v_fold_2256_, v___x_2257_);
v___x_2259_ = lean_uint64_xor(v_fold_2256_, v___x_2258_);
v___x_2260_ = lean_uint64_to_usize(v___x_2259_);
v___x_2261_ = lean_usize_of_nat(v___x_2252_);
v___x_2262_ = ((size_t)1ULL);
v___x_2263_ = lean_usize_sub(v___x_2261_, v___x_2262_);
v___x_2264_ = lean_usize_land(v___x_2260_, v___x_2263_);
v_bkt_2265_ = lean_array_uget_borrowed(v_buckets_2248_, v___x_2264_);
v___x_2266_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(v_a_2245_, v_bkt_2265_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2267_; lean_object* v_size_x27_2268_; lean_object* v___x_2269_; lean_object* v_buckets_x27_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; uint8_t v___x_2276_; 
v___x_2267_ = lean_unsigned_to_nat(1u);
v_size_x27_2268_ = lean_nat_add(v_size_2247_, v___x_2267_);
lean_dec(v_size_2247_);
lean_inc(v_bkt_2265_);
v___x_2269_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2269_, 0, v_a_2245_);
lean_ctor_set(v___x_2269_, 1, v_b_2246_);
lean_ctor_set(v___x_2269_, 2, v_bkt_2265_);
v_buckets_x27_2270_ = lean_array_uset(v_buckets_2248_, v___x_2264_, v___x_2269_);
v___x_2271_ = lean_unsigned_to_nat(4u);
v___x_2272_ = lean_nat_mul(v_size_x27_2268_, v___x_2271_);
v___x_2273_ = lean_unsigned_to_nat(3u);
v___x_2274_ = lean_nat_div(v___x_2272_, v___x_2273_);
lean_dec(v___x_2272_);
v___x_2275_ = lean_array_get_size(v_buckets_x27_2270_);
v___x_2276_ = lean_nat_dec_le(v___x_2274_, v___x_2275_);
lean_dec(v___x_2274_);
if (v___x_2276_ == 0)
{
lean_object* v_val_2277_; lean_object* v___x_2279_; 
v_val_2277_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23___redArg(v_buckets_x27_2270_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 1, v_val_2277_);
lean_ctor_set(v___x_2250_, 0, v_size_x27_2268_);
v___x_2279_ = v___x_2250_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_size_x27_2268_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v_val_2277_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
else
{
lean_object* v___x_2282_; 
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 1, v_buckets_x27_2270_);
lean_ctor_set(v___x_2250_, 0, v_size_x27_2268_);
v___x_2282_ = v___x_2250_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_size_x27_2268_);
lean_ctor_set(v_reuseFailAlloc_2283_, 1, v_buckets_x27_2270_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
else
{
lean_object* v___x_2284_; lean_object* v_buckets_x27_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2289_; 
lean_inc(v_bkt_2265_);
v___x_2284_ = lean_box(0);
v_buckets_x27_2285_ = lean_array_uset(v_buckets_2248_, v___x_2264_, v___x_2284_);
v___x_2286_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(v_a_2245_, v_b_2246_, v_bkt_2265_);
v___x_2287_ = lean_array_uset(v_buckets_x27_2285_, v___x_2264_, v___x_2286_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 1, v___x_2287_);
v___x_2289_ = v___x_2250_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_size_2247_);
lean_ctor_set(v_reuseFailAlloc_2290_, 1, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(lean_object* v_a_2292_, lean_object* v_x_2293_){
_start:
{
if (lean_obj_tag(v_x_2293_) == 0)
{
lean_object* v___x_2294_; 
v___x_2294_ = lean_box(0);
return v___x_2294_;
}
else
{
lean_object* v_key_2295_; lean_object* v_value_2296_; lean_object* v_tail_2297_; uint8_t v___x_2298_; 
v_key_2295_ = lean_ctor_get(v_x_2293_, 0);
v_value_2296_ = lean_ctor_get(v_x_2293_, 1);
v_tail_2297_ = lean_ctor_get(v_x_2293_, 2);
v___x_2298_ = lean_string_dec_eq(v_key_2295_, v_a_2292_);
if (v___x_2298_ == 0)
{
v_x_2293_ = v_tail_2297_;
goto _start;
}
else
{
lean_object* v___x_2300_; 
lean_inc(v_value_2296_);
v___x_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2300_, 0, v_value_2296_);
return v___x_2300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg___boxed(lean_object* v_a_2301_, lean_object* v_x_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(v_a_2301_, v_x_2302_);
lean_dec(v_x_2302_);
lean_dec_ref(v_a_2301_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(lean_object* v_m_2304_, lean_object* v_a_2305_){
_start:
{
lean_object* v_buckets_2306_; lean_object* v___x_2307_; uint64_t v___x_2308_; uint64_t v___x_2309_; uint64_t v___x_2310_; uint64_t v_fold_2311_; uint64_t v___x_2312_; uint64_t v___x_2313_; uint64_t v___x_2314_; size_t v___x_2315_; size_t v___x_2316_; size_t v___x_2317_; size_t v___x_2318_; size_t v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v_buckets_2306_ = lean_ctor_get(v_m_2304_, 1);
v___x_2307_ = lean_array_get_size(v_buckets_2306_);
v___x_2308_ = lean_string_hash(v_a_2305_);
v___x_2309_ = 32ULL;
v___x_2310_ = lean_uint64_shift_right(v___x_2308_, v___x_2309_);
v_fold_2311_ = lean_uint64_xor(v___x_2308_, v___x_2310_);
v___x_2312_ = 16ULL;
v___x_2313_ = lean_uint64_shift_right(v_fold_2311_, v___x_2312_);
v___x_2314_ = lean_uint64_xor(v_fold_2311_, v___x_2313_);
v___x_2315_ = lean_uint64_to_usize(v___x_2314_);
v___x_2316_ = lean_usize_of_nat(v___x_2307_);
v___x_2317_ = ((size_t)1ULL);
v___x_2318_ = lean_usize_sub(v___x_2316_, v___x_2317_);
v___x_2319_ = lean_usize_land(v___x_2315_, v___x_2318_);
v___x_2320_ = lean_array_uget_borrowed(v_buckets_2306_, v___x_2319_);
v___x_2321_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(v_a_2305_, v___x_2320_);
return v___x_2321_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg___boxed(lean_object* v_m_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_m_2322_, v_a_2323_);
lean_dec_ref(v_a_2323_);
lean_dec_ref(v_m_2322_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(lean_object* v_histogram_2325_, lean_object* v_index_2326_, lean_object* v_val_2327_){
_start:
{
lean_object* v___x_2328_; 
v___x_2328_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_histogram_2325_, v_val_2327_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2329_ = lean_unsigned_to_nat(1u);
v___x_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2330_, 0, v_index_2326_);
v___x_2331_ = lean_unsigned_to_nat(0u);
v___x_2332_ = lean_box(0);
v___x_2333_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2329_);
lean_ctor_set(v___x_2333_, 1, v___x_2330_);
lean_ctor_set(v___x_2333_, 2, v___x_2331_);
lean_ctor_set(v___x_2333_, 3, v___x_2332_);
v___x_2334_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2325_, v_val_2327_, v___x_2333_);
return v___x_2334_;
}
else
{
lean_object* v_val_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2356_; 
v_val_2335_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2337_ = v___x_2328_;
v_isShared_2338_ = v_isSharedCheck_2356_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_val_2335_);
lean_dec(v___x_2328_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2356_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v_leftCount_2339_; lean_object* v_rightCount_2340_; lean_object* v_rightIndex_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2354_; 
v_leftCount_2339_ = lean_ctor_get(v_val_2335_, 0);
v_rightCount_2340_ = lean_ctor_get(v_val_2335_, 2);
v_rightIndex_2341_ = lean_ctor_get(v_val_2335_, 3);
v_isSharedCheck_2354_ = !lean_is_exclusive(v_val_2335_);
if (v_isSharedCheck_2354_ == 0)
{
lean_object* v_unused_2355_; 
v_unused_2355_ = lean_ctor_get(v_val_2335_, 1);
lean_dec(v_unused_2355_);
v___x_2343_ = v_val_2335_;
v_isShared_2344_ = v_isSharedCheck_2354_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_rightIndex_2341_);
lean_inc(v_rightCount_2340_);
lean_inc(v_leftCount_2339_);
lean_dec(v_val_2335_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2354_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2348_; 
v___x_2345_ = lean_unsigned_to_nat(1u);
v___x_2346_ = lean_nat_add(v_leftCount_2339_, v___x_2345_);
lean_dec(v_leftCount_2339_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 0, v_index_2326_);
v___x_2348_ = v___x_2337_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_index_2326_);
v___x_2348_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
lean_object* v___x_2350_; 
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 1, v___x_2348_);
lean_ctor_set(v___x_2343_, 0, v___x_2346_);
v___x_2350_ = v___x_2343_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2346_);
lean_ctor_set(v_reuseFailAlloc_2352_, 1, v___x_2348_);
lean_ctor_set(v_reuseFailAlloc_2352_, 2, v_rightCount_2340_);
lean_ctor_set(v_reuseFailAlloc_2352_, 3, v_rightIndex_2341_);
v___x_2350_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
lean_object* v___x_2351_; 
v___x_2351_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2325_, v_val_2327_, v___x_2350_);
return v___x_2351_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(lean_object* v_upperBound_2357_, lean_object* v_fst_2358_, lean_object* v___x_2359_, lean_object* v_fst_2360_, lean_object* v_a_2361_, lean_object* v_b_2362_){
_start:
{
uint8_t v___x_2363_; 
v___x_2363_ = lean_nat_dec_lt(v_a_2361_, v_upperBound_2357_);
if (v___x_2363_ == 0)
{
lean_dec(v_a_2361_);
return v_b_2362_;
}
else
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2364_ = l_Subarray_get___redArg(v_fst_2360_, v_a_2361_);
lean_inc(v_a_2361_);
v___x_2365_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(v_b_2362_, v_a_2361_, v___x_2364_);
v___x_2366_ = lean_unsigned_to_nat(1u);
v___x_2367_ = lean_nat_add(v_a_2361_, v___x_2366_);
lean_dec(v_a_2361_);
v_a_2361_ = v___x_2367_;
v_b_2362_ = v___x_2365_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_upperBound_2369_, lean_object* v_fst_2370_, lean_object* v___x_2371_, lean_object* v_fst_2372_, lean_object* v_a_2373_, lean_object* v_b_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(v_upperBound_2369_, v_fst_2370_, v___x_2371_, v_fst_2372_, v_a_2373_, v_b_2374_);
lean_dec_ref(v_fst_2372_);
lean_dec(v___x_2371_);
lean_dec_ref(v_fst_2370_);
lean_dec(v_upperBound_2369_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(lean_object* v_x_2376_, lean_object* v_x_2377_){
_start:
{
if (lean_obj_tag(v_x_2377_) == 0)
{
lean_inc(v_x_2376_);
return v_x_2376_;
}
else
{
lean_object* v_key_2378_; lean_object* v_value_2379_; lean_object* v_tail_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v_key_2378_ = lean_ctor_get(v_x_2377_, 0);
v_value_2379_ = lean_ctor_get(v_x_2377_, 1);
v_tail_2380_ = lean_ctor_get(v_x_2377_, 2);
v___x_2381_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(v_x_2376_, v_tail_2380_);
lean_inc(v_value_2379_);
lean_inc(v_key_2378_);
v___x_2382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2382_, 0, v_key_2378_);
lean_ctor_set(v___x_2382_, 1, v_value_2379_);
v___x_2383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2383_, 0, v___x_2382_);
lean_ctor_set(v___x_2383_, 1, v___x_2381_);
return v___x_2383_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5___boxed(lean_object* v_x_2384_, lean_object* v_x_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(v_x_2384_, v_x_2385_);
lean_dec(v_x_2385_);
lean_dec(v_x_2384_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(lean_object* v_as_2387_, size_t v_i_2388_, size_t v_stop_2389_, lean_object* v_b_2390_){
_start:
{
uint8_t v___x_2391_; 
v___x_2391_ = lean_usize_dec_eq(v_i_2388_, v_stop_2389_);
if (v___x_2391_ == 0)
{
size_t v___x_2392_; size_t v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2392_ = ((size_t)1ULL);
v___x_2393_ = lean_usize_sub(v_i_2388_, v___x_2392_);
v___x_2394_ = lean_array_uget_borrowed(v_as_2387_, v___x_2393_);
v___x_2395_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(v_b_2390_, v___x_2394_);
lean_dec(v_b_2390_);
v_i_2388_ = v___x_2393_;
v_b_2390_ = v___x_2395_;
goto _start;
}
else
{
return v_b_2390_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6___boxed(lean_object* v_as_2397_, lean_object* v_i_2398_, lean_object* v_stop_2399_, lean_object* v_b_2400_){
_start:
{
size_t v_i_boxed_2401_; size_t v_stop_boxed_2402_; lean_object* v_res_2403_; 
v_i_boxed_2401_ = lean_unbox_usize(v_i_2398_);
lean_dec(v_i_2398_);
v_stop_boxed_2402_ = lean_unbox_usize(v_stop_2399_);
lean_dec(v_stop_2399_);
v_res_2403_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(v_as_2397_, v_i_boxed_2401_, v_stop_boxed_2402_, v_b_2400_);
lean_dec_ref(v_as_2397_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(lean_object* v_histogram_2404_, lean_object* v_index_2405_, lean_object* v_val_2406_){
_start:
{
lean_object* v___x_2407_; 
v___x_2407_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_histogram_2404_, v_val_2406_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2408_ = lean_unsigned_to_nat(0u);
v___x_2409_ = lean_box(0);
v___x_2410_ = lean_unsigned_to_nat(1u);
v___x_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2411_, 0, v_index_2405_);
v___x_2412_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2408_);
lean_ctor_set(v___x_2412_, 1, v___x_2409_);
lean_ctor_set(v___x_2412_, 2, v___x_2410_);
lean_ctor_set(v___x_2412_, 3, v___x_2411_);
v___x_2413_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2404_, v_val_2406_, v___x_2412_);
return v___x_2413_;
}
else
{
lean_object* v_val_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2435_; 
v_val_2414_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2416_ = v___x_2407_;
v_isShared_2417_ = v_isSharedCheck_2435_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_val_2414_);
lean_dec(v___x_2407_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2435_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v_leftCount_2418_; lean_object* v_leftIndex_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2432_; 
v_leftCount_2418_ = lean_ctor_get(v_val_2414_, 0);
v_leftIndex_2419_ = lean_ctor_get(v_val_2414_, 1);
v_isSharedCheck_2432_ = !lean_is_exclusive(v_val_2414_);
if (v_isSharedCheck_2432_ == 0)
{
lean_object* v_unused_2433_; lean_object* v_unused_2434_; 
v_unused_2433_ = lean_ctor_get(v_val_2414_, 3);
lean_dec(v_unused_2433_);
v_unused_2434_ = lean_ctor_get(v_val_2414_, 2);
lean_dec(v_unused_2434_);
v___x_2421_ = v_val_2414_;
v_isShared_2422_ = v_isSharedCheck_2432_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_leftIndex_2419_);
lean_inc(v_leftCount_2418_);
lean_dec(v_val_2414_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2432_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2426_; 
v___x_2423_ = lean_unsigned_to_nat(1u);
v___x_2424_ = lean_nat_add(v_leftCount_2418_, v___x_2423_);
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 0, v_index_2405_);
v___x_2426_ = v___x_2416_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_index_2405_);
v___x_2426_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
lean_object* v___x_2428_; 
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 3, v___x_2426_);
lean_ctor_set(v___x_2421_, 2, v___x_2424_);
v___x_2428_ = v___x_2421_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_leftCount_2418_);
lean_ctor_set(v_reuseFailAlloc_2430_, 1, v_leftIndex_2419_);
lean_ctor_set(v_reuseFailAlloc_2430_, 2, v___x_2424_);
lean_ctor_set(v_reuseFailAlloc_2430_, 3, v___x_2426_);
v___x_2428_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
lean_object* v___x_2429_; 
v___x_2429_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2404_, v_val_2406_, v___x_2428_);
return v___x_2429_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(lean_object* v_upperBound_2436_, lean_object* v___x_2437_, lean_object* v_fst_2438_, lean_object* v___x_2439_, lean_object* v_a_2440_, lean_object* v_b_2441_){
_start:
{
uint8_t v___x_2442_; 
v___x_2442_ = lean_nat_dec_lt(v_a_2440_, v_upperBound_2436_);
if (v___x_2442_ == 0)
{
lean_dec(v_a_2440_);
return v_b_2441_;
}
else
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2443_ = l_Subarray_get___redArg(v_fst_2438_, v_a_2440_);
lean_inc(v_a_2440_);
v___x_2444_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(v_b_2441_, v_a_2440_, v___x_2443_);
v___x_2445_ = lean_unsigned_to_nat(1u);
v___x_2446_ = lean_nat_add(v_a_2440_, v___x_2445_);
lean_dec(v_a_2440_);
v_a_2440_ = v___x_2446_;
v_b_2441_ = v___x_2444_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg___boxed(lean_object* v_upperBound_2448_, lean_object* v___x_2449_, lean_object* v_fst_2450_, lean_object* v___x_2451_, lean_object* v_a_2452_, lean_object* v_b_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(v_upperBound_2448_, v___x_2449_, v_fst_2450_, v___x_2451_, v_a_2452_, v_b_2453_);
lean_dec(v___x_2451_);
lean_dec_ref(v_fst_2450_);
lean_dec(v___x_2449_);
lean_dec(v_upperBound_2448_);
return v_res_2454_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2455_ = lean_box(0);
v___x_2456_ = lean_unsigned_to_nat(16u);
v___x_2457_ = lean_mk_array(v___x_2456_, v___x_2455_);
return v___x_2457_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v_hist_2460_; 
v___x_2458_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0);
v___x_2459_ = lean_unsigned_to_nat(0u);
v_hist_2460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_2460_, 0, v___x_2459_);
lean_ctor_set(v_hist_2460_, 1, v___x_2458_);
return v_hist_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(lean_object* v_left_2461_, lean_object* v_right_2462_){
_start:
{
lean_object* v___x_2463_; lean_object* v_snd_2464_; lean_object* v_fst_2465_; lean_object* v_fst_2466_; lean_object* v_snd_2467_; lean_object* v___x_2468_; lean_object* v_snd_2469_; lean_object* v_fst_2470_; lean_object* v_fst_2471_; lean_object* v_snd_2472_; lean_object* v_start_2473_; lean_object* v_stop_2474_; lean_object* v___x_2475_; lean_object* v_hist_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v_start_2479_; lean_object* v_stop_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v_buckets_2483_; lean_object* v___x_2484_; lean_object* v___y_2486_; lean_object* v___x_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; 
v___x_2463_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2(v_left_2461_, v_right_2462_);
v_snd_2464_ = lean_ctor_get(v___x_2463_, 1);
lean_inc(v_snd_2464_);
v_fst_2465_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_fst_2465_);
lean_dec_ref(v___x_2463_);
v_fst_2466_ = lean_ctor_get(v_snd_2464_, 0);
lean_inc(v_fst_2466_);
v_snd_2467_ = lean_ctor_get(v_snd_2464_, 1);
lean_inc(v_snd_2467_);
lean_dec(v_snd_2464_);
v___x_2468_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3(v_fst_2466_, v_snd_2467_);
v_snd_2469_ = lean_ctor_get(v___x_2468_, 1);
lean_inc(v_snd_2469_);
v_fst_2470_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_fst_2470_);
lean_dec_ref(v___x_2468_);
v_fst_2471_ = lean_ctor_get(v_snd_2469_, 0);
lean_inc(v_fst_2471_);
v_snd_2472_ = lean_ctor_get(v_snd_2469_, 1);
lean_inc(v_snd_2472_);
lean_dec(v_snd_2469_);
v_start_2473_ = lean_ctor_get(v_fst_2470_, 1);
v_stop_2474_ = lean_ctor_get(v_fst_2470_, 2);
v___x_2475_ = lean_unsigned_to_nat(0u);
v_hist_2476_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1);
v___x_2477_ = lean_nat_sub(v_stop_2474_, v_start_2473_);
v___x_2478_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(v___x_2477_, v_fst_2471_, v___x_2477_, v_fst_2470_, v___x_2475_, v_hist_2476_);
v_start_2479_ = lean_ctor_get(v_fst_2471_, 1);
v_stop_2480_ = lean_ctor_get(v_fst_2471_, 2);
v___x_2481_ = lean_nat_sub(v_stop_2480_, v_start_2479_);
v___x_2482_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(v___x_2481_, v___x_2481_, v_fst_2471_, v___x_2477_, v___x_2475_, v___x_2478_);
lean_dec(v___x_2477_);
lean_dec(v___x_2481_);
v_buckets_2483_ = lean_ctor_get(v___x_2482_, 1);
lean_inc_ref(v_buckets_2483_);
lean_dec_ref(v___x_2482_);
v___x_2484_ = lean_box(0);
v___x_2512_ = lean_box(0);
v___x_2513_ = lean_array_get_size(v_buckets_2483_);
v___x_2514_ = lean_nat_dec_lt(v___x_2475_, v___x_2513_);
if (v___x_2514_ == 0)
{
lean_dec_ref(v_buckets_2483_);
v___y_2486_ = v___x_2512_;
goto v___jp_2485_;
}
else
{
size_t v___x_2515_; size_t v___x_2516_; lean_object* v___x_2517_; 
v___x_2515_ = lean_usize_of_nat(v___x_2513_);
v___x_2516_ = ((size_t)0ULL);
v___x_2517_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(v_buckets_2483_, v___x_2515_, v___x_2516_, v___x_2512_);
lean_dec_ref(v_buckets_2483_);
v___y_2486_ = v___x_2517_;
goto v___jp_2485_;
}
v___jp_2485_:
{
lean_object* v___x_2487_; 
v___x_2487_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(v___y_2486_, v___x_2484_);
lean_dec(v___y_2486_);
if (lean_obj_tag(v___x_2487_) == 1)
{
lean_object* v_val_2488_; lean_object* v_snd_2489_; lean_object* v_snd_2490_; lean_object* v_fst_2491_; lean_object* v_fst_2492_; lean_object* v_snd_2493_; lean_object* v___x_2494_; lean_object* v_fst_2495_; lean_object* v_snd_2496_; lean_object* v___x_2497_; lean_object* v_fst_2498_; lean_object* v_snd_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v_val_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_val_2488_);
lean_dec_ref_known(v___x_2487_, 1);
v_snd_2489_ = lean_ctor_get(v_val_2488_, 1);
lean_inc(v_snd_2489_);
lean_dec(v_val_2488_);
v_snd_2490_ = lean_ctor_get(v_snd_2489_, 1);
lean_inc(v_snd_2490_);
v_fst_2491_ = lean_ctor_get(v_snd_2489_, 0);
lean_inc(v_fst_2491_);
lean_dec(v_snd_2489_);
v_fst_2492_ = lean_ctor_get(v_snd_2490_, 0);
lean_inc(v_fst_2492_);
v_snd_2493_ = lean_ctor_get(v_snd_2490_, 1);
lean_inc(v_snd_2493_);
lean_dec(v_snd_2490_);
v___x_2494_ = l_Subarray_split___redArg(v_fst_2470_, v_fst_2492_);
lean_dec(v_fst_2492_);
v_fst_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_fst_2495_);
v_snd_2496_ = lean_ctor_get(v___x_2494_, 1);
lean_inc(v_snd_2496_);
lean_dec_ref(v___x_2494_);
v___x_2497_ = l_Subarray_split___redArg(v_fst_2471_, v_snd_2493_);
lean_dec(v_snd_2493_);
v_fst_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_fst_2498_);
v_snd_2499_ = lean_ctor_get(v___x_2497_, 1);
lean_inc(v_snd_2499_);
lean_dec_ref(v___x_2497_);
v___x_2500_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v_fst_2495_, v_fst_2498_);
v___x_2501_ = l_Array_append___redArg(v_fst_2465_, v___x_2500_);
lean_dec_ref(v___x_2500_);
v___x_2502_ = lean_unsigned_to_nat(1u);
v___x_2503_ = lean_mk_empty_array_with_capacity(v___x_2502_);
v___x_2504_ = lean_array_push(v___x_2503_, v_fst_2491_);
v___x_2505_ = l_Array_append___redArg(v___x_2501_, v___x_2504_);
lean_dec_ref(v___x_2504_);
v___x_2506_ = l_Subarray_drop___redArg(v_snd_2496_, v___x_2502_);
v___x_2507_ = l_Subarray_drop___redArg(v_snd_2499_, v___x_2502_);
v___x_2508_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v___x_2506_, v___x_2507_);
v___x_2509_ = l_Array_append___redArg(v___x_2505_, v___x_2508_);
lean_dec_ref(v___x_2508_);
v___x_2510_ = l_Array_append___redArg(v___x_2509_, v_snd_2472_);
lean_dec(v_snd_2472_);
return v___x_2510_;
}
else
{
lean_object* v___x_2511_; 
lean_dec(v___x_2487_);
lean_dec(v_fst_2471_);
lean_dec(v_fst_2470_);
v___x_2511_ = l_Array_append___redArg(v_fst_2465_, v_snd_2472_);
lean_dec(v_snd_2472_);
return v___x_2511_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(size_t v_sz_2518_, size_t v_i_2519_, lean_object* v_bs_2520_){
_start:
{
uint8_t v___x_2521_; 
v___x_2521_ = lean_usize_dec_lt(v_i_2519_, v_sz_2518_);
if (v___x_2521_ == 0)
{
return v_bs_2520_;
}
else
{
lean_object* v_v_2522_; lean_object* v___x_2523_; lean_object* v_bs_x27_2524_; uint8_t v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; size_t v___x_2528_; size_t v___x_2529_; lean_object* v___x_2530_; 
v_v_2522_ = lean_array_uget(v_bs_2520_, v_i_2519_);
v___x_2523_ = lean_unsigned_to_nat(0u);
v_bs_x27_2524_ = lean_array_uset(v_bs_2520_, v_i_2519_, v___x_2523_);
v___x_2525_ = 1;
v___x_2526_ = lean_box(v___x_2525_);
v___x_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
lean_ctor_set(v___x_2527_, 1, v_v_2522_);
v___x_2528_ = ((size_t)1ULL);
v___x_2529_ = lean_usize_add(v_i_2519_, v___x_2528_);
v___x_2530_ = lean_array_uset(v_bs_x27_2524_, v_i_2519_, v___x_2527_);
v_i_2519_ = v___x_2529_;
v_bs_2520_ = v___x_2530_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7___boxed(lean_object* v_sz_2532_, lean_object* v_i_2533_, lean_object* v_bs_2534_){
_start:
{
size_t v_sz_boxed_2535_; size_t v_i_boxed_2536_; lean_object* v_res_2537_; 
v_sz_boxed_2535_ = lean_unbox_usize(v_sz_2532_);
lean_dec(v_sz_2532_);
v_i_boxed_2536_ = lean_unbox_usize(v_i_2533_);
lean_dec(v_i_2533_);
v_res_2537_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_boxed_2535_, v_i_boxed_2536_, v_bs_2534_);
return v_res_2537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(lean_object* v_original_2543_, lean_object* v_edited_2544_){
_start:
{
lean_object* v_i_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; 
v_i_2545_ = lean_unsigned_to_nat(0u);
v___x_2546_ = lean_array_get_size(v_original_2543_);
v___x_2547_ = lean_nat_dec_lt(v_i_2545_, v___x_2546_);
if (v___x_2547_ == 0)
{
size_t v_sz_2548_; size_t v___x_2549_; lean_object* v___x_2550_; 
lean_dec_ref(v_original_2543_);
v_sz_2548_ = lean_array_size(v_edited_2544_);
v___x_2549_ = ((size_t)0ULL);
v___x_2550_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_2548_, v___x_2549_, v_edited_2544_);
return v___x_2550_;
}
else
{
lean_object* v___x_2551_; uint8_t v___x_2552_; 
v___x_2551_ = lean_array_get_size(v_edited_2544_);
v___x_2552_ = lean_nat_dec_lt(v_i_2545_, v___x_2551_);
if (v___x_2552_ == 0)
{
size_t v_sz_2553_; size_t v___x_2554_; lean_object* v___x_2555_; 
lean_dec_ref(v_edited_2544_);
v_sz_2553_ = lean_array_size(v_original_2543_);
v___x_2554_ = ((size_t)0ULL);
v___x_2555_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_2553_, v___x_2554_, v_original_2543_);
return v___x_2555_;
}
else
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v_ds_2558_; lean_object* v___x_2559_; size_t v_sz_2560_; size_t v___x_2561_; lean_object* v___x_2562_; lean_object* v_snd_2563_; lean_object* v_fst_2564_; lean_object* v_fst_2565_; lean_object* v_snd_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2585_; 
lean_inc_ref(v_original_2543_);
v___x_2556_ = l_Array_toSubarray___redArg(v_original_2543_, v_i_2545_, v___x_2546_);
lean_inc_ref(v_edited_2544_);
v___x_2557_ = l_Array_toSubarray___redArg(v_edited_2544_, v_i_2545_, v___x_2551_);
v_ds_2558_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v___x_2556_, v___x_2557_);
v___x_2559_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__1));
v_sz_2560_ = lean_array_size(v_ds_2558_);
v___x_2561_ = ((size_t)0ULL);
v___x_2562_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v_edited_2544_, v___x_2551_, v_original_2543_, v___x_2546_, v_ds_2558_, v_sz_2560_, v___x_2561_, v___x_2559_);
lean_dec_ref(v_ds_2558_);
v_snd_2563_ = lean_ctor_get(v___x_2562_, 1);
lean_inc(v_snd_2563_);
v_fst_2564_ = lean_ctor_get(v___x_2562_, 0);
lean_inc(v_fst_2564_);
lean_dec_ref(v___x_2562_);
v_fst_2565_ = lean_ctor_get(v_snd_2563_, 0);
v_snd_2566_ = lean_ctor_get(v_snd_2563_, 1);
v_isSharedCheck_2585_ = !lean_is_exclusive(v_snd_2563_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2568_ = v_snd_2563_;
v_isShared_2569_ = v_isSharedCheck_2585_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_snd_2566_);
lean_inc(v_fst_2565_);
lean_dec(v_snd_2563_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2585_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 1, v_fst_2565_);
lean_ctor_set(v___x_2568_, 0, v_fst_2564_);
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_fst_2564_);
lean_ctor_set(v_reuseFailAlloc_2584_, 1, v_fst_2565_);
v___x_2571_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
lean_object* v___x_2572_; lean_object* v_fst_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2582_; 
v___x_2572_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2546_, v_original_2543_, v___x_2571_);
lean_dec_ref(v_original_2543_);
v_fst_2573_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2582_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2582_ == 0)
{
lean_object* v_unused_2583_; 
v_unused_2583_ = lean_ctor_get(v___x_2572_, 1);
lean_dec(v_unused_2583_);
v___x_2575_ = v___x_2572_;
v_isShared_2576_ = v_isSharedCheck_2582_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_fst_2573_);
lean_dec(v___x_2572_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2582_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2578_; 
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 1, v_snd_2566_);
v___x_2578_ = v___x_2575_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2581_; 
v_reuseFailAlloc_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2581_, 0, v_fst_2573_);
lean_ctor_set(v_reuseFailAlloc_2581_, 1, v_snd_2566_);
v___x_2578_ = v_reuseFailAlloc_2581_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
lean_object* v___x_2579_; lean_object* v_fst_2580_; 
v___x_2579_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2551_, v_edited_2544_, v___x_2578_);
lean_dec_ref(v_edited_2544_);
v_fst_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_fst_2580_);
lean_dec_ref(v___x_2579_);
return v_fst_2580_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(lean_object* v___x_2586_, uint8_t v_inSubst_2587_, lean_object* v___x_2588_, lean_object* v_____r_2589_, lean_object* v_wssIdx_2590_){
_start:
{
lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2591_ = lean_box(v_inSubst_2587_);
v___x_2592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2586_);
lean_ctor_set(v___x_2592_, 1, v___x_2591_);
v___x_2593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2593_, 0, v_wssIdx_2590_);
lean_ctor_set(v___x_2593_, 1, v___x_2592_);
v___x_2594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2594_, 0, v___x_2588_);
lean_ctor_set(v___x_2594_, 1, v___x_2593_);
v___x_2595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1___boxed(lean_object* v___x_2596_, lean_object* v_inSubst_2597_, lean_object* v___x_2598_, lean_object* v_____r_2599_, lean_object* v_wssIdx_2600_){
_start:
{
uint8_t v_inSubst_boxed_2601_; lean_object* v_res_2602_; 
v_inSubst_boxed_2601_ = lean_unbox(v_inSubst_2597_);
v_res_2602_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2596_, v_inSubst_boxed_2601_, v___x_2598_, v_____r_2599_, v_wssIdx_2600_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(lean_object* v_fst_2603_, uint8_t v___x_2604_, lean_object* v_fst_2605_, lean_object* v___x_2606_, lean_object* v_00___2607_){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2608_ = lean_box(v___x_2604_);
v___x_2609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2609_, 0, v_fst_2603_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
v___x_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2610_, 0, v_fst_2605_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
v___x_2611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2606_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
v___x_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
return v___x_2612_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0___boxed(lean_object* v_fst_2613_, lean_object* v___x_2614_, lean_object* v_fst_2615_, lean_object* v___x_2616_, lean_object* v_00___2617_){
_start:
{
uint8_t v___x_9180__boxed_2618_; lean_object* v_res_2619_; 
v___x_9180__boxed_2618_ = lean_unbox(v___x_2614_);
v_res_2619_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2613_, v___x_9180__boxed_2618_, v_fst_2615_, v___x_2616_, v_00___2617_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(uint8_t v_inSubst_2620_, lean_object* v_snd_2621_, lean_object* v_fst_2622_, lean_object* v_____r_2623_, lean_object* v_withWs_2624_, lean_object* v_wssIdx_2625_){
_start:
{
lean_object* v_wss_x27Idx_2627_; uint8_t v___x_2633_; 
v___x_2633_ = lean_unbox(v_snd_2621_);
if (v___x_2633_ == 0)
{
v_wss_x27Idx_2627_ = v_fst_2622_;
goto v___jp_2626_;
}
else
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
v___x_2634_ = lean_unsigned_to_nat(1u);
v___x_2635_ = lean_nat_add(v_fst_2622_, v___x_2634_);
lean_dec(v_fst_2622_);
v_wss_x27Idx_2627_ = v___x_2635_;
goto v___jp_2626_;
}
v___jp_2626_:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
v___x_2628_ = lean_box(v_inSubst_2620_);
v___x_2629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2629_, 0, v_wss_x27Idx_2627_);
lean_ctor_set(v___x_2629_, 1, v___x_2628_);
v___x_2630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2630_, 0, v_wssIdx_2625_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
v___x_2631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2631_, 0, v_withWs_2624_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
v___x_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2631_);
return v___x_2632_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2___boxed(lean_object* v_inSubst_2636_, lean_object* v_snd_2637_, lean_object* v_fst_2638_, lean_object* v_____r_2639_, lean_object* v_withWs_2640_, lean_object* v_wssIdx_2641_){
_start:
{
uint8_t v_inSubst_boxed_2642_; lean_object* v_res_2643_; 
v_inSubst_boxed_2642_ = lean_unbox(v_inSubst_2636_);
v_res_2643_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_boxed_2642_, v_snd_2637_, v_fst_2638_, v_____r_2639_, v_withWs_2640_, v_wssIdx_2641_);
lean_dec(v_snd_2637_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(lean_object* v_upperBound_2644_, lean_object* v_diff_2645_, lean_object* v_snd_2646_, lean_object* v_snd_2647_, lean_object* v_a_2648_, lean_object* v_b_2649_){
_start:
{
lean_object* v_a_2651_; lean_object* v___y_2656_; uint8_t v___x_2659_; 
v___x_2659_ = lean_nat_dec_lt(v_a_2648_, v_upperBound_2644_);
if (v___x_2659_ == 0)
{
lean_dec(v_a_2648_);
return v_b_2649_;
}
else
{
lean_object* v___x_2660_; lean_object* v_snd_2661_; lean_object* v_snd_2662_; lean_object* v_fst_2663_; lean_object* v_fst_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2804_; 
v___x_2660_ = lean_array_fget_borrowed(v_diff_2645_, v_a_2648_);
v_snd_2661_ = lean_ctor_get(v_b_2649_, 1);
lean_inc(v_snd_2661_);
v_snd_2662_ = lean_ctor_get(v_snd_2661_, 1);
lean_inc(v_snd_2662_);
v_fst_2663_ = lean_ctor_get(v___x_2660_, 0);
v_fst_2664_ = lean_ctor_get(v_b_2649_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v_b_2649_);
if (v_isSharedCheck_2804_ == 0)
{
lean_object* v_unused_2805_; 
v_unused_2805_ = lean_ctor_get(v_b_2649_, 1);
lean_dec(v_unused_2805_);
v___x_2666_ = v_b_2649_;
v_isShared_2667_ = v_isSharedCheck_2804_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_fst_2664_);
lean_dec(v_b_2649_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2804_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v_fst_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2802_; 
v_fst_2668_ = lean_ctor_get(v_snd_2661_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v_snd_2661_);
if (v_isSharedCheck_2802_ == 0)
{
lean_object* v_unused_2803_; 
v_unused_2803_ = lean_ctor_get(v_snd_2661_, 1);
lean_dec(v_unused_2803_);
v___x_2670_ = v_snd_2661_;
v_isShared_2671_ = v_isSharedCheck_2802_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_fst_2668_);
lean_dec(v_snd_2661_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2802_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v_fst_2672_; lean_object* v_snd_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2801_; 
v_fst_2672_ = lean_ctor_get(v_snd_2662_, 0);
v_snd_2673_ = lean_ctor_get(v_snd_2662_, 1);
v_isSharedCheck_2801_ = !lean_is_exclusive(v_snd_2662_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2675_ = v_snd_2662_;
v_isShared_2676_ = v_isSharedCheck_2801_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_snd_2673_);
lean_inc(v_fst_2672_);
lean_dec(v_snd_2662_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2801_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2677_; lean_object* v___y_2679_; lean_object* v___y_2694_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; uint8_t v___x_2705_; 
lean_inc(v___x_2660_);
v___x_2677_ = lean_array_push(v_fst_2664_, v___x_2660_);
v___x_2702_ = lean_unsigned_to_nat(1u);
v___x_2703_ = lean_nat_add(v_a_2648_, v___x_2702_);
v___x_2704_ = lean_array_get_size(v_diff_2645_);
v___x_2705_ = lean_nat_dec_lt(v___x_2703_, v___x_2704_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
lean_dec(v___x_2703_);
lean_del_object(v___x_2675_);
lean_del_object(v___x_2670_);
lean_del_object(v___x_2666_);
v___x_2706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2706_, 0, v_fst_2672_);
lean_ctor_set(v___x_2706_, 1, v_snd_2673_);
v___x_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2707_, 0, v_fst_2668_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
v___x_2708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2677_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v_a_2651_ = v___x_2708_;
goto v___jp_2650_;
}
else
{
lean_object* v___x_2709_; lean_object* v_fst_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2799_; 
v___x_2709_ = lean_array_fget(v_diff_2645_, v___x_2703_);
lean_dec(v___x_2703_);
v_fst_2710_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2799_ == 0)
{
lean_object* v_unused_2800_; 
v_unused_2800_ = lean_ctor_get(v___x_2709_, 1);
lean_dec(v_unused_2800_);
v___x_2712_ = v___x_2709_;
v_isShared_2713_ = v_isSharedCheck_2799_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_fst_2710_);
lean_dec(v___x_2709_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2799_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
uint8_t v_inSubst_2714_; lean_object* v___y_2716_; lean_object* v___x_2725_; uint8_t v___x_2726_; 
v_inSubst_2714_ = 0;
v___x_2725_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2726_ = lean_unbox(v_fst_2663_);
switch(v___x_2726_)
{
case 0:
{
uint8_t v___x_2727_; 
lean_del_object(v___x_2675_);
lean_del_object(v___x_2670_);
lean_del_object(v___x_2666_);
v___x_2727_ = lean_unbox(v_fst_2710_);
switch(v___x_2727_)
{
case 0:
{
lean_object* v___x_2728_; lean_object* v___x_2730_; 
v___x_2728_ = lean_array_get_borrowed(v___x_2725_, v_snd_2646_, v_fst_2672_);
lean_inc(v___x_2728_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 1, v___x_2728_);
v___x_2730_ = v___x_2712_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_fst_2710_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v___x_2728_);
v___x_2730_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2731_ = lean_array_push(v___x_2677_, v___x_2730_);
v___x_2732_ = lean_nat_add(v_fst_2672_, v___x_2702_);
lean_dec(v_fst_2672_);
v___x_2733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
lean_ctor_set(v___x_2733_, 1, v_snd_2673_);
v___x_2734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2734_, 0, v_fst_2668_);
lean_ctor_set(v___x_2734_, 1, v___x_2733_);
v___x_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2731_);
lean_ctor_set(v___x_2735_, 1, v___x_2734_);
v_a_2651_ = v___x_2735_;
goto v___jp_2650_;
}
}
case 1:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
lean_del_object(v___x_2712_);
lean_dec(v_fst_2710_);
lean_dec(v_snd_2673_);
v___x_2737_ = lean_box(0);
v___x_2738_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2672_, v___x_2659_, v_fst_2668_, v___x_2677_, v___x_2737_);
v___y_2656_ = v___x_2738_;
goto v___jp_2655_;
}
default: 
{
lean_object* v___x_2739_; uint8_t v___x_2740_; 
lean_dec(v_fst_2710_);
v___x_2739_ = lean_array_get_borrowed(v___x_2725_, v_snd_2646_, v_fst_2672_);
v___x_2740_ = lean_unbox(v_snd_2673_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2742_; 
lean_inc(v___x_2739_);
lean_inc(v_fst_2663_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 1, v___x_2739_);
lean_ctor_set(v___x_2712_, 0, v_fst_2663_);
v___x_2742_ = v___x_2712_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_fst_2663_);
lean_ctor_set(v_reuseFailAlloc_2745_, 1, v___x_2739_);
v___x_2742_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2743_ = lean_mk_empty_array_with_capacity(v___x_2702_);
v___x_2744_ = lean_array_push(v___x_2743_, v___x_2742_);
v___y_2716_ = v___x_2744_;
goto v___jp_2715_;
}
}
else
{
lean_object* v___x_2746_; lean_object* v___x_2747_; 
lean_del_object(v___x_2712_);
v___x_2746_ = lean_array_get_borrowed(v___x_2725_, v_snd_2647_, v_fst_2668_);
lean_inc(v___x_2739_);
lean_inc(v___x_2746_);
v___x_2747_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2746_, v___x_2739_);
v___y_2716_ = v___x_2747_;
goto v___jp_2715_;
}
}
}
}
case 1:
{
uint8_t v___x_2748_; 
lean_del_object(v___x_2675_);
lean_del_object(v___x_2670_);
lean_del_object(v___x_2666_);
v___x_2748_ = lean_unbox(v_fst_2710_);
switch(v___x_2748_)
{
case 0:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
lean_del_object(v___x_2712_);
lean_dec(v_fst_2710_);
lean_dec(v_snd_2673_);
v___x_2749_ = lean_box(0);
v___x_2750_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2672_, v___x_2659_, v_fst_2668_, v___x_2677_, v___x_2749_);
v___y_2656_ = v___x_2750_;
goto v___jp_2655_;
}
case 1:
{
lean_object* v___x_2751_; lean_object* v___x_2753_; 
v___x_2751_ = lean_array_get_borrowed(v___x_2725_, v_snd_2647_, v_fst_2668_);
lean_inc(v___x_2751_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 1, v___x_2751_);
v___x_2753_ = v___x_2712_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_fst_2710_);
lean_ctor_set(v_reuseFailAlloc_2759_, 1, v___x_2751_);
v___x_2753_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2754_ = lean_array_push(v___x_2677_, v___x_2753_);
v___x_2755_ = lean_nat_add(v_fst_2668_, v___x_2702_);
lean_dec(v_fst_2668_);
v___x_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2756_, 0, v_fst_2672_);
lean_ctor_set(v___x_2756_, 1, v_snd_2673_);
v___x_2757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2755_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2758_, 0, v___x_2754_);
lean_ctor_set(v___x_2758_, 1, v___x_2757_);
v_a_2651_ = v___x_2758_;
goto v___jp_2650_;
}
}
default: 
{
uint8_t v___x_2763_; 
lean_dec(v_fst_2710_);
v___x_2763_ = lean_unbox(v_snd_2673_);
if (v___x_2763_ == 0)
{
lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; 
v___x_2764_ = lean_array_get_borrowed(v___x_2725_, v_snd_2647_, v_fst_2668_);
v___x_2765_ = lean_unsigned_to_nat(0u);
v___x_2766_ = lean_string_utf8_byte_size(v___x_2764_);
lean_inc(v___x_2764_);
v___x_2767_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2764_);
lean_ctor_set(v___x_2767_, 1, v___x_2765_);
lean_ctor_set(v___x_2767_, 2, v___x_2766_);
v___x_2768_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_2767_);
lean_dec_ref_known(v___x_2767_, 3);
if (v___x_2768_ == 0)
{
lean_object* v___x_2770_; 
lean_inc(v___x_2764_);
lean_inc(v_fst_2663_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 1, v___x_2764_);
lean_ctor_set(v___x_2712_, 0, v_fst_2663_);
v___x_2770_ = v___x_2712_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_fst_2663_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v___x_2764_);
v___x_2770_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2771_ = lean_array_push(v___x_2677_, v___x_2770_);
v___x_2772_ = lean_nat_add(v_fst_2668_, v___x_2702_);
lean_dec(v_fst_2668_);
v___x_2773_ = lean_box(0);
v___x_2774_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2714_, v_snd_2673_, v_fst_2672_, v___x_2773_, v___x_2771_, v___x_2772_);
lean_dec(v_snd_2673_);
v___y_2656_ = v___x_2774_;
goto v___jp_2655_;
}
}
else
{
lean_del_object(v___x_2712_);
goto v___jp_2760_;
}
}
else
{
lean_del_object(v___x_2712_);
goto v___jp_2760_;
}
v___jp_2760_:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2761_ = lean_box(0);
v___x_2762_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2714_, v_snd_2673_, v_fst_2672_, v___x_2761_, v___x_2677_, v_fst_2668_);
lean_dec(v_snd_2673_);
v___y_2656_ = v___x_2762_;
goto v___jp_2655_;
}
}
}
}
default: 
{
uint8_t v___x_2776_; 
v___x_2776_ = lean_unbox(v_fst_2710_);
if (v___x_2776_ == 1)
{
lean_object* v___x_2777_; lean_object* v___x_2778_; uint8_t v___x_2779_; 
v___x_2777_ = lean_array_get_borrowed(v___x_2725_, v_snd_2647_, v_fst_2668_);
v___x_2778_ = lean_array_get_size(v_snd_2646_);
v___x_2779_ = lean_nat_dec_lt(v_fst_2672_, v___x_2778_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2781_; 
lean_inc(v___x_2777_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 1, v___x_2777_);
v___x_2781_ = v___x_2712_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_fst_2710_);
lean_ctor_set(v_reuseFailAlloc_2784_, 1, v___x_2777_);
v___x_2781_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = lean_mk_empty_array_with_capacity(v___x_2702_);
v___x_2783_ = lean_array_push(v___x_2782_, v___x_2781_);
v___y_2679_ = v___x_2783_;
goto v___jp_2678_;
}
}
else
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_del_object(v___x_2712_);
lean_dec(v_fst_2710_);
v___x_2785_ = lean_array_fget_borrowed(v_snd_2646_, v_fst_2672_);
lean_inc(v___x_2785_);
lean_inc(v___x_2777_);
v___x_2786_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2777_, v___x_2785_);
v___y_2679_ = v___x_2786_;
goto v___jp_2678_;
}
}
else
{
lean_object* v___x_2787_; lean_object* v___x_2788_; uint8_t v___x_2789_; 
lean_dec(v_fst_2710_);
lean_del_object(v___x_2675_);
lean_del_object(v___x_2670_);
lean_del_object(v___x_2666_);
v___x_2787_ = lean_array_get_borrowed(v___x_2725_, v_snd_2646_, v_fst_2672_);
v___x_2788_ = lean_array_get_size(v_snd_2647_);
v___x_2789_ = lean_nat_dec_lt(v_fst_2668_, v___x_2788_);
if (v___x_2789_ == 0)
{
uint8_t v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2793_; 
v___x_2790_ = 0;
v___x_2791_ = lean_box(v___x_2790_);
lean_inc(v___x_2787_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 1, v___x_2787_);
lean_ctor_set(v___x_2712_, 0, v___x_2791_);
v___x_2793_ = v___x_2712_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v___x_2791_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v___x_2787_);
v___x_2793_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = lean_mk_empty_array_with_capacity(v___x_2702_);
v___x_2795_ = lean_array_push(v___x_2794_, v___x_2793_);
v___y_2694_ = v___x_2795_;
goto v___jp_2693_;
}
}
else
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
lean_del_object(v___x_2712_);
v___x_2797_ = lean_array_fget_borrowed(v_snd_2647_, v_fst_2668_);
lean_inc(v___x_2787_);
lean_inc(v___x_2797_);
v___x_2798_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2797_, v___x_2787_);
v___y_2694_ = v___x_2798_;
goto v___jp_2693_;
}
}
}
}
v___jp_2715_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; uint8_t v___x_2719_; 
v___x_2717_ = l_Array_append___redArg(v___x_2677_, v___y_2716_);
lean_dec_ref(v___y_2716_);
v___x_2718_ = lean_nat_add(v_fst_2672_, v___x_2702_);
lean_dec(v_fst_2672_);
v___x_2719_ = lean_unbox(v_snd_2673_);
lean_dec(v_snd_2673_);
if (v___x_2719_ == 0)
{
lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2720_ = lean_box(0);
v___x_2721_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2718_, v_inSubst_2714_, v___x_2717_, v___x_2720_, v_fst_2668_);
v___y_2656_ = v___x_2721_;
goto v___jp_2655_;
}
else
{
lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2722_ = lean_nat_add(v_fst_2668_, v___x_2702_);
lean_dec(v_fst_2668_);
v___x_2723_ = lean_box(0);
v___x_2724_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2718_, v_inSubst_2714_, v___x_2717_, v___x_2723_, v___x_2722_);
v___y_2656_ = v___x_2724_;
goto v___jp_2655_;
}
}
}
}
v___jp_2678_:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2685_; 
v___x_2680_ = l_Array_append___redArg(v___x_2677_, v___y_2679_);
lean_dec_ref(v___y_2679_);
v___x_2681_ = lean_unsigned_to_nat(1u);
v___x_2682_ = lean_nat_add(v_fst_2668_, v___x_2681_);
lean_dec(v_fst_2668_);
v___x_2683_ = lean_nat_add(v_fst_2672_, v___x_2681_);
lean_dec(v_fst_2672_);
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 0, v___x_2683_);
v___x_2685_ = v___x_2675_;
goto v_reusejp_2684_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v___x_2683_);
lean_ctor_set(v_reuseFailAlloc_2692_, 1, v_snd_2673_);
v___x_2685_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2684_;
}
v_reusejp_2684_:
{
lean_object* v___x_2687_; 
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 1, v___x_2685_);
lean_ctor_set(v___x_2670_, 0, v___x_2682_);
v___x_2687_ = v___x_2670_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2682_);
lean_ctor_set(v_reuseFailAlloc_2691_, 1, v___x_2685_);
v___x_2687_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
lean_object* v___x_2689_; 
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 1, v___x_2687_);
lean_ctor_set(v___x_2666_, 0, v___x_2680_);
v___x_2689_ = v___x_2666_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2680_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v___x_2687_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
v_a_2651_ = v___x_2689_;
goto v___jp_2650_;
}
}
}
}
v___jp_2693_:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2695_ = l_Array_append___redArg(v___x_2677_, v___y_2694_);
lean_dec_ref(v___y_2694_);
v___x_2696_ = lean_unsigned_to_nat(1u);
v___x_2697_ = lean_nat_add(v_fst_2668_, v___x_2696_);
lean_dec(v_fst_2668_);
v___x_2698_ = lean_nat_add(v_fst_2672_, v___x_2696_);
lean_dec(v_fst_2672_);
v___x_2699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
lean_ctor_set(v___x_2699_, 1, v_snd_2673_);
v___x_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2697_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2695_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v_a_2651_ = v___x_2701_;
goto v___jp_2650_;
}
}
}
}
}
v___jp_2650_:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2652_ = lean_unsigned_to_nat(1u);
v___x_2653_ = lean_nat_add(v_a_2648_, v___x_2652_);
lean_dec(v_a_2648_);
v_a_2648_ = v___x_2653_;
v_b_2649_ = v_a_2651_;
goto _start;
}
v___jp_2655_:
{
if (lean_obj_tag(v___y_2656_) == 0)
{
lean_object* v_a_2657_; 
lean_dec(v_a_2648_);
v_a_2657_ = lean_ctor_get(v___y_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___y_2656_, 1);
return v_a_2657_;
}
else
{
lean_object* v_a_2658_; 
v_a_2658_ = lean_ctor_get(v___y_2656_, 0);
lean_inc(v_a_2658_);
lean_dec_ref_known(v___y_2656_, 1);
v_a_2651_ = v_a_2658_;
goto v___jp_2650_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___boxed(lean_object* v_upperBound_2806_, lean_object* v_diff_2807_, lean_object* v_snd_2808_, lean_object* v_snd_2809_, lean_object* v_a_2810_, lean_object* v_b_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2806_, v_diff_2807_, v_snd_2808_, v_snd_2809_, v_a_2810_, v_b_2811_);
lean_dec_ref(v_snd_2809_);
lean_dec_ref(v_snd_2808_);
lean_dec_ref(v_diff_2807_);
lean_dec(v_upperBound_2806_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(lean_object* v_s_2823_, lean_object* v_s_x27_2824_){
_start:
{
lean_object* v___x_2825_; lean_object* v_fst_2826_; lean_object* v_snd_2827_; lean_object* v___x_2828_; lean_object* v_fst_2829_; lean_object* v_snd_2830_; lean_object* v_diff_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v_fst_2836_; lean_object* v___x_2837_; size_t v_sz_2838_; size_t v___x_2839_; lean_object* v___x_2840_; 
v___x_2825_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_2823_);
v_fst_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_fst_2826_);
v_snd_2827_ = lean_ctor_get(v___x_2825_, 1);
lean_inc(v_snd_2827_);
lean_dec_ref(v___x_2825_);
v___x_2828_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_x27_2824_);
v_fst_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_fst_2829_);
v_snd_2830_ = lean_ctor_get(v___x_2828_, 1);
lean_inc(v_snd_2830_);
lean_dec_ref(v___x_2828_);
v_diff_2831_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(v_fst_2826_, v_fst_2829_);
v___x_2832_ = lean_unsigned_to_nat(0u);
v___x_2833_ = lean_array_get_size(v_diff_2831_);
v___x_2834_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__2));
v___x_2835_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v___x_2833_, v_diff_2831_, v_snd_2830_, v_snd_2827_, v___x_2832_, v___x_2834_);
lean_dec(v_snd_2827_);
lean_dec(v_snd_2830_);
lean_dec_ref(v_diff_2831_);
v_fst_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_fst_2836_);
lean_dec_ref(v___x_2835_);
v___x_2837_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_fst_2836_);
lean_dec(v_fst_2836_);
v_sz_2838_ = lean_array_size(v___x_2837_);
v___x_2839_ = ((size_t)0ULL);
v___x_2840_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_2838_, v___x_2839_, v___x_2837_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___boxed(lean_object* v_s_2841_, lean_object* v_s_x27_2842_){
_start:
{
lean_object* v_res_2843_; 
v_res_2843_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_2841_, v_s_x27_2842_);
lean_dec_ref(v_s_x27_2842_);
lean_dec_ref(v_s_2841_);
return v_res_2843_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(lean_object* v_upperBound_2844_, lean_object* v_diff_2845_, lean_object* v_snd_2846_, lean_object* v_snd_2847_, lean_object* v_inst_2848_, lean_object* v_R_2849_, lean_object* v_a_2850_, lean_object* v_b_2851_, lean_object* v_c_2852_){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2844_, v_diff_2845_, v_snd_2846_, v_snd_2847_, v_a_2850_, v_b_2851_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___boxed(lean_object* v_upperBound_2854_, lean_object* v_diff_2855_, lean_object* v_snd_2856_, lean_object* v_snd_2857_, lean_object* v_inst_2858_, lean_object* v_R_2859_, lean_object* v_a_2860_, lean_object* v_b_2861_, lean_object* v_c_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(v_upperBound_2854_, v_diff_2855_, v_snd_2856_, v_snd_2857_, v_inst_2858_, v_R_2859_, v_a_2860_, v_b_2861_, v_c_2862_);
lean_dec_ref(v_snd_2857_);
lean_dec_ref(v_snd_2856_);
lean_dec_ref(v_diff_2855_);
lean_dec(v_upperBound_2854_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(lean_object* v_original_2864_, lean_object* v___x_2865_, lean_object* v_a_2866_, lean_object* v_inst_2867_, lean_object* v_a_2868_){
_start:
{
lean_object* v___x_2869_; 
v___x_2869_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v_original_2864_, v___x_2865_, v_a_2866_, v_a_2868_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___boxed(lean_object* v_original_2870_, lean_object* v___x_2871_, lean_object* v_a_2872_, lean_object* v_inst_2873_, lean_object* v_a_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(v_original_2870_, v___x_2871_, v_a_2872_, v_inst_2873_, v_a_2874_);
lean_dec_ref(v_a_2872_);
lean_dec(v___x_2871_);
lean_dec_ref(v_original_2870_);
return v_res_2875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(lean_object* v_edited_2876_, lean_object* v___x_2877_, lean_object* v_a_2878_, lean_object* v_inst_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v___x_2881_; 
v___x_2881_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(v_edited_2876_, v___x_2877_, v_a_2878_, v_a_2880_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___boxed(lean_object* v_edited_2882_, lean_object* v___x_2883_, lean_object* v_a_2884_, lean_object* v_inst_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v_edited_2882_, v___x_2883_, v_a_2884_, v_inst_2885_, v_a_2886_);
lean_dec_ref(v_a_2884_);
lean_dec(v___x_2883_);
lean_dec_ref(v_edited_2882_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(lean_object* v___x_2888_, lean_object* v_original_2889_, lean_object* v_inst_2890_, lean_object* v_a_2891_){
_start:
{
lean_object* v___x_2892_; 
v___x_2892_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2888_, v_original_2889_, v_a_2891_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___boxed(lean_object* v___x_2893_, lean_object* v_original_2894_, lean_object* v_inst_2895_, lean_object* v_a_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(v___x_2893_, v_original_2894_, v_inst_2895_, v_a_2896_);
lean_dec_ref(v_original_2894_);
lean_dec(v___x_2893_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(lean_object* v___x_2898_, lean_object* v_edited_2899_, lean_object* v_inst_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2898_, v_edited_2899_, v_a_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___boxed(lean_object* v___x_2903_, lean_object* v_edited_2904_, lean_object* v_inst_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(v___x_2903_, v_edited_2904_, v_inst_2905_, v_a_2906_);
lean_dec_ref(v_edited_2904_);
lean_dec(v___x_2903_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4(lean_object* v_as_2908_, lean_object* v_as_x27_2909_, lean_object* v_b_2910_, lean_object* v_a_2911_){
_start:
{
lean_object* v___x_2912_; 
v___x_2912_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(v_as_x27_2909_, v_b_2910_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___boxed(lean_object* v_as_2913_, lean_object* v_as_x27_2914_, lean_object* v_b_2915_, lean_object* v_a_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4(v_as_2913_, v_as_x27_2914_, v_b_2915_, v_a_2916_);
lean_dec(v_as_x27_2914_);
lean_dec(v_as_2913_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7(lean_object* v_lsize_2918_, lean_object* v_rsize_2919_, lean_object* v_histogram_2920_, lean_object* v_index_2921_, lean_object* v_val_2922_){
_start:
{
lean_object* v___x_2923_; 
v___x_2923_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(v_histogram_2920_, v_index_2921_, v_val_2922_);
return v___x_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___boxed(lean_object* v_lsize_2924_, lean_object* v_rsize_2925_, lean_object* v_histogram_2926_, lean_object* v_index_2927_, lean_object* v_val_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7(v_lsize_2924_, v_rsize_2925_, v_histogram_2926_, v_index_2927_, v_val_2928_);
lean_dec(v_rsize_2925_);
lean_dec(v_lsize_2924_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8(lean_object* v_upperBound_2930_, lean_object* v___x_2931_, lean_object* v_fst_2932_, lean_object* v___x_2933_, lean_object* v_inst_2934_, lean_object* v_R_2935_, lean_object* v_a_2936_, lean_object* v_b_2937_, lean_object* v_c_2938_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(v_upperBound_2930_, v___x_2931_, v_fst_2932_, v___x_2933_, v_a_2936_, v_b_2937_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___boxed(lean_object* v_upperBound_2940_, lean_object* v___x_2941_, lean_object* v_fst_2942_, lean_object* v___x_2943_, lean_object* v_inst_2944_, lean_object* v_R_2945_, lean_object* v_a_2946_, lean_object* v_b_2947_, lean_object* v_c_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8(v_upperBound_2940_, v___x_2941_, v_fst_2942_, v___x_2943_, v_inst_2944_, v_R_2945_, v_a_2946_, v_b_2947_, v_c_2948_);
lean_dec(v___x_2943_);
lean_dec_ref(v_fst_2942_);
lean_dec(v___x_2941_);
lean_dec(v_upperBound_2940_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9(lean_object* v_lsize_2950_, lean_object* v_rsize_2951_, lean_object* v_histogram_2952_, lean_object* v_index_2953_, lean_object* v_val_2954_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(v_histogram_2952_, v_index_2953_, v_val_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___boxed(lean_object* v_lsize_2956_, lean_object* v_rsize_2957_, lean_object* v_histogram_2958_, lean_object* v_index_2959_, lean_object* v_val_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9(v_lsize_2956_, v_rsize_2957_, v_histogram_2958_, v_index_2959_, v_val_2960_);
lean_dec(v_rsize_2957_);
lean_dec(v_lsize_2956_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10(lean_object* v_upperBound_2962_, lean_object* v_fst_2963_, lean_object* v___x_2964_, lean_object* v_fst_2965_, lean_object* v_inst_2966_, lean_object* v_R_2967_, lean_object* v_a_2968_, lean_object* v_b_2969_, lean_object* v_c_2970_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(v_upperBound_2962_, v_fst_2963_, v___x_2964_, v_fst_2965_, v_a_2968_, v_b_2969_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___boxed(lean_object* v_upperBound_2972_, lean_object* v_fst_2973_, lean_object* v___x_2974_, lean_object* v_fst_2975_, lean_object* v_inst_2976_, lean_object* v_R_2977_, lean_object* v_a_2978_, lean_object* v_b_2979_, lean_object* v_c_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10(v_upperBound_2972_, v_fst_2973_, v___x_2974_, v_fst_2975_, v_inst_2976_, v_R_2977_, v_a_2978_, v_b_2979_, v_c_2980_);
lean_dec_ref(v_fst_2975_);
lean_dec(v___x_2974_);
lean_dec_ref(v_fst_2973_);
lean_dec(v_upperBound_2972_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11(lean_object* v_00_u03b2_2982_, lean_object* v_m_2983_, lean_object* v_a_2984_){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_m_2983_, v_a_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___boxed(lean_object* v_00_u03b2_2986_, lean_object* v_m_2987_, lean_object* v_a_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11(v_00_u03b2_2986_, v_m_2987_, v_a_2988_);
lean_dec_ref(v_a_2988_);
lean_dec_ref(v_m_2987_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12(lean_object* v_00_u03b2_2990_, lean_object* v_m_2991_, lean_object* v_a_2992_, lean_object* v_b_2993_){
_start:
{
lean_object* v___x_2994_; 
v___x_2994_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_m_2991_, v_a_2992_, v_b_2993_);
return v___x_2994_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14(lean_object* v_inst_2995_, lean_object* v_R_2996_, lean_object* v_a_2997_, lean_object* v_b_2998_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v_a_2997_, v_b_2998_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20(lean_object* v_00_u03b2_3000_, lean_object* v_a_3001_, lean_object* v_x_3002_){
_start:
{
lean_object* v___x_3003_; 
v___x_3003_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(v_a_3001_, v_x_3002_);
return v___x_3003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___boxed(lean_object* v_00_u03b2_3004_, lean_object* v_a_3005_, lean_object* v_x_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20(v_00_u03b2_3004_, v_a_3005_, v_x_3006_);
lean_dec(v_x_3006_);
lean_dec_ref(v_a_3005_);
return v_res_3007_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22(lean_object* v_00_u03b2_3008_, lean_object* v_a_3009_, lean_object* v_x_3010_){
_start:
{
uint8_t v___x_3011_; 
v___x_3011_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(v_a_3009_, v_x_3010_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___boxed(lean_object* v_00_u03b2_3012_, lean_object* v_a_3013_, lean_object* v_x_3014_){
_start:
{
uint8_t v_res_3015_; lean_object* v_r_3016_; 
v_res_3015_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22(v_00_u03b2_3012_, v_a_3013_, v_x_3014_);
lean_dec(v_x_3014_);
lean_dec_ref(v_a_3013_);
v_r_3016_ = lean_box(v_res_3015_);
return v_r_3016_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23(lean_object* v_00_u03b2_3017_, lean_object* v_data_3018_){
_start:
{
lean_object* v___x_3019_; 
v___x_3019_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23___redArg(v_data_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24(lean_object* v_00_u03b2_3020_, lean_object* v_a_3021_, lean_object* v_b_3022_, lean_object* v_x_3023_){
_start:
{
lean_object* v___x_3024_; 
v___x_3024_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(v_a_3021_, v_b_3022_, v_x_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28(lean_object* v_00_u03b2_3025_, lean_object* v_i_3026_, lean_object* v_source_3027_, lean_object* v_target_3028_){
_start:
{
lean_object* v___x_3029_; 
v___x_3029_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28___redArg(v_i_3026_, v_source_3027_, v_target_3028_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_3030_, lean_object* v_x_3031_, lean_object* v_x_3032_){
_start:
{
lean_object* v___x_3033_; 
v___x_3033_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29___redArg(v_x_3031_, v_x_3032_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(lean_object* v_s_3034_){
_start:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; 
v___x_3035_ = lean_string_data(v_s_3034_);
v___x_3036_ = lean_array_mk(v___x_3035_);
return v___x_3036_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(lean_object* v_s_3037_, lean_object* v_s_x27_3038_){
_start:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3039_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3037_);
v___x_3040_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3038_);
v___x_3041_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3039_, v___x_3040_);
v___x_3042_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_3041_);
lean_dec_ref(v___x_3041_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(lean_object* v_s_3043_, lean_object* v_s_x27_3044_){
_start:
{
uint8_t v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; uint8_t v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3045_ = 1;
v___x_3046_ = lean_box(v___x_3045_);
v___x_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3046_);
lean_ctor_set(v___x_3047_, 1, v_s_3043_);
v___x_3048_ = 0;
v___x_3049_ = lean_box(v___x_3048_);
v___x_3050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3049_);
lean_ctor_set(v___x_3050_, 1, v_s_x27_3044_);
v___x_3051_ = lean_unsigned_to_nat(2u);
v___x_3052_ = lean_mk_empty_array_with_capacity(v___x_3051_);
v___x_3053_ = lean_array_push(v___x_3052_, v___x_3047_);
v___x_3054_ = lean_array_push(v___x_3053_, v___x_3050_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(lean_object* v_as_3055_, size_t v_i_3056_, size_t v_stop_3057_, lean_object* v_b_3058_){
_start:
{
lean_object* v___y_3060_; uint8_t v___x_3064_; 
v___x_3064_ = lean_usize_dec_eq(v_i_3056_, v_stop_3057_);
if (v___x_3064_ == 0)
{
lean_object* v___x_3065_; lean_object* v_fst_3066_; uint8_t v___x_3067_; uint8_t v___x_3068_; uint8_t v___x_3069_; 
v___x_3065_ = lean_array_uget_borrowed(v_as_3055_, v_i_3056_);
v_fst_3066_ = lean_ctor_get(v___x_3065_, 0);
v___x_3067_ = 2;
v___x_3068_ = lean_unbox(v_fst_3066_);
v___x_3069_ = l_Lean_Diff_instBEqAction_beq(v___x_3068_, v___x_3067_);
if (v___x_3069_ == 0)
{
lean_object* v___x_3070_; 
lean_inc(v___x_3065_);
v___x_3070_ = lean_array_push(v_b_3058_, v___x_3065_);
v___y_3060_ = v___x_3070_;
goto v___jp_3059_;
}
else
{
v___y_3060_ = v_b_3058_;
goto v___jp_3059_;
}
}
else
{
return v_b_3058_;
}
v___jp_3059_:
{
size_t v___x_3061_; size_t v___x_3062_; 
v___x_3061_ = ((size_t)1ULL);
v___x_3062_ = lean_usize_add(v_i_3056_, v___x_3061_);
v_i_3056_ = v___x_3062_;
v_b_3058_ = v___y_3060_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0___boxed(lean_object* v_as_3071_, lean_object* v_i_3072_, lean_object* v_stop_3073_, lean_object* v_b_3074_){
_start:
{
size_t v_i_boxed_3075_; size_t v_stop_boxed_3076_; lean_object* v_res_3077_; 
v_i_boxed_3075_ = lean_unbox_usize(v_i_3072_);
lean_dec(v_i_3072_);
v_stop_boxed_3076_ = lean_unbox_usize(v_stop_3073_);
lean_dec(v_stop_3073_);
v_res_3077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_as_3071_, v_i_boxed_3075_, v_stop_boxed_3076_, v_b_3074_);
lean_dec_ref(v_as_3071_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff(lean_object* v_s_3078_, lean_object* v_s_x27_3079_, uint8_t v_granularity_3080_){
_start:
{
lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; uint8_t v___y_3085_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; 
switch(v_granularity_3080_)
{
case 0:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___y_3127_; uint8_t v___x_3133_; 
v___x_3124_ = lean_string_length(v_s_3078_);
v___x_3125_ = lean_string_length(v_s_x27_3079_);
v___x_3133_ = lean_nat_dec_le(v___x_3124_, v___x_3125_);
if (v___x_3133_ == 0)
{
v___y_3127_ = v___x_3125_;
goto v___jp_3126_;
}
else
{
v___y_3127_ = v___x_3124_;
goto v___jp_3126_;
}
v___jp_3126_:
{
lean_object* v___x_3128_; lean_object* v_maxCharDiffDistance_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; uint8_t v___x_3132_; 
v___x_3128_ = lean_unsigned_to_nat(5u);
v_maxCharDiffDistance_3129_ = lean_nat_div(v___y_3127_, v___x_3128_);
v___x_3130_ = lean_unsigned_to_nat(1u);
v___x_3131_ = lean_nat_shiftr(v___y_3127_, v___x_3130_);
lean_dec(v___y_3127_);
v___x_3132_ = lean_nat_dec_le(v___x_3124_, v___x_3125_);
if (v___x_3132_ == 0)
{
v___y_3104_ = v_maxCharDiffDistance_3129_;
v___y_3105_ = v___x_3131_;
v___y_3106_ = v___x_3130_;
v___y_3107_ = v___x_3124_;
goto v___jp_3103_;
}
else
{
v___y_3104_ = v_maxCharDiffDistance_3129_;
v___y_3105_ = v___x_3131_;
v___y_3106_ = v___x_3130_;
v___y_3107_ = v___x_3125_;
goto v___jp_3103_;
}
}
}
case 1:
{
lean_object* v___x_3134_; 
v___x_3134_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(v_s_3078_, v_s_x27_3079_);
return v___x_3134_;
}
case 2:
{
lean_object* v___x_3135_; 
v___x_3135_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3078_, v_s_x27_3079_);
lean_dec_ref(v_s_x27_3079_);
lean_dec_ref(v_s_3078_);
return v___x_3135_;
}
case 3:
{
lean_object* v___x_3136_; 
v___x_3136_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3078_, v_s_x27_3079_);
return v___x_3136_;
}
default: 
{
uint8_t v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
lean_dec_ref(v_s_3078_);
v___x_3137_ = 0;
v___x_3138_ = lean_box(v___x_3137_);
v___x_3139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3139_, 0, v___x_3138_);
lean_ctor_set(v___x_3139_, 1, v_s_x27_3079_);
v___x_3140_ = lean_unsigned_to_nat(1u);
v___x_3141_ = lean_mk_empty_array_with_capacity(v___x_3140_);
v___x_3142_ = lean_array_push(v___x_3141_, v___x_3139_);
return v___x_3142_;
}
}
v___jp_3081_:
{
if (v___y_3085_ == 0)
{
uint8_t v___x_3086_; 
lean_dec_ref(v___y_3084_);
v___x_3086_ = lean_nat_dec_le(v___y_3083_, v___y_3082_);
lean_dec(v___y_3082_);
lean_dec(v___y_3083_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3087_; 
v___x_3087_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3078_, v_s_x27_3079_);
return v___x_3087_;
}
else
{
lean_object* v___x_3088_; 
v___x_3088_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3078_, v_s_x27_3079_);
lean_dec_ref(v_s_x27_3079_);
lean_dec_ref(v_s_3078_);
return v___x_3088_;
}
}
else
{
size_t v_sz_3089_; size_t v___x_3090_; lean_object* v___x_3091_; 
lean_dec(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v_s_x27_3079_);
lean_dec_ref(v_s_3078_);
v_sz_3089_ = lean_array_size(v___y_3084_);
v___x_3090_ = ((size_t)0ULL);
v___x_3091_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_3089_, v___x_3090_, v___y_3084_);
return v___x_3091_;
}
}
v___jp_3092_:
{
lean_object* v_approxEditDistance_3097_; lean_object* v_charArrDiff_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; uint8_t v___x_3101_; 
v_approxEditDistance_3097_ = lean_array_get_size(v___y_3096_);
lean_dec_ref(v___y_3096_);
v_charArrDiff_3098_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v___y_3094_);
lean_dec_ref(v___y_3094_);
v___x_3099_ = lean_array_get_size(v_charArrDiff_3098_);
v___x_3100_ = lean_unsigned_to_nat(3u);
v___x_3101_ = lean_nat_dec_le(v___x_3099_, v___x_3100_);
if (v___x_3101_ == 0)
{
uint8_t v___x_3102_; 
v___x_3102_ = lean_nat_dec_le(v_approxEditDistance_3097_, v___y_3095_);
lean_dec(v___y_3095_);
v___y_3082_ = v___y_3093_;
v___y_3083_ = v_approxEditDistance_3097_;
v___y_3084_ = v_charArrDiff_3098_;
v___y_3085_ = v___x_3102_;
goto v___jp_3081_;
}
else
{
lean_dec(v___y_3095_);
v___y_3082_ = v___y_3093_;
v___y_3083_ = v_approxEditDistance_3097_;
v___y_3084_ = v_charArrDiff_3098_;
v___y_3085_ = v___x_3101_;
goto v___jp_3081_;
}
}
v___jp_3103_:
{
lean_object* v___x_3108_; lean_object* v_maxWordDiffDistance_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v_charDiffRaw_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; uint8_t v___x_3116_; 
v___x_3108_ = lean_nat_shiftr(v___y_3107_, v___y_3106_);
lean_dec(v___y_3107_);
v_maxWordDiffDistance_3109_ = lean_nat_add(v___y_3105_, v___x_3108_);
lean_dec(v___x_3108_);
lean_dec(v___y_3105_);
lean_inc_ref(v_s_3078_);
v___x_3110_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3078_);
lean_inc_ref(v_s_x27_3079_);
v___x_3111_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3079_);
v_charDiffRaw_3112_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3110_, v___x_3111_);
v___x_3113_ = lean_unsigned_to_nat(0u);
v___x_3114_ = lean_array_get_size(v_charDiffRaw_3112_);
v___x_3115_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0));
v___x_3116_ = lean_nat_dec_lt(v___x_3113_, v___x_3114_);
if (v___x_3116_ == 0)
{
v___y_3093_ = v_maxWordDiffDistance_3109_;
v___y_3094_ = v_charDiffRaw_3112_;
v___y_3095_ = v___y_3104_;
v___y_3096_ = v___x_3115_;
goto v___jp_3092_;
}
else
{
uint8_t v___x_3117_; 
v___x_3117_ = lean_nat_dec_le(v___x_3114_, v___x_3114_);
if (v___x_3117_ == 0)
{
if (v___x_3116_ == 0)
{
v___y_3093_ = v_maxWordDiffDistance_3109_;
v___y_3094_ = v_charDiffRaw_3112_;
v___y_3095_ = v___y_3104_;
v___y_3096_ = v___x_3115_;
goto v___jp_3092_;
}
else
{
size_t v___x_3118_; size_t v___x_3119_; lean_object* v___x_3120_; 
v___x_3118_ = ((size_t)0ULL);
v___x_3119_ = lean_usize_of_nat(v___x_3114_);
v___x_3120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3112_, v___x_3118_, v___x_3119_, v___x_3115_);
v___y_3093_ = v_maxWordDiffDistance_3109_;
v___y_3094_ = v_charDiffRaw_3112_;
v___y_3095_ = v___y_3104_;
v___y_3096_ = v___x_3120_;
goto v___jp_3092_;
}
}
else
{
size_t v___x_3121_; size_t v___x_3122_; lean_object* v___x_3123_; 
v___x_3121_ = ((size_t)0ULL);
v___x_3122_ = lean_usize_of_nat(v___x_3114_);
v___x_3123_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3112_, v___x_3121_, v___x_3122_, v___x_3115_);
v___y_3093_ = v_maxWordDiffDistance_3109_;
v___y_3094_ = v_charDiffRaw_3112_;
v___y_3095_ = v___y_3104_;
v___y_3096_ = v___x_3123_;
goto v___jp_3092_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff___boxed(lean_object* v_s_3143_, lean_object* v_s_x27_3144_, lean_object* v_granularity_3145_){
_start:
{
uint8_t v_granularity_boxed_3146_; lean_object* v_res_3147_; 
v_granularity_boxed_3146_ = lean_unbox(v_granularity_3145_);
v_res_3147_ = l_Lean_Meta_Hint_readableDiff(v_s_3143_, v_s_x27_3144_, v_granularity_boxed_3146_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(lean_object* v_as_3148_, size_t v_i_3149_, size_t v_stop_3150_, lean_object* v_b_3151_){
_start:
{
uint8_t v___x_3152_; 
v___x_3152_ = lean_usize_dec_eq(v_i_3149_, v_stop_3150_);
if (v___x_3152_ == 0)
{
lean_object* v___x_3153_; lean_object* v_snd_3154_; lean_object* v___x_3155_; size_t v___x_3156_; size_t v___x_3157_; 
v___x_3153_ = lean_array_uget_borrowed(v_as_3148_, v_i_3149_);
v_snd_3154_ = lean_ctor_get(v___x_3153_, 1);
v___x_3155_ = lean_string_append(v_b_3151_, v_snd_3154_);
v___x_3156_ = ((size_t)1ULL);
v___x_3157_ = lean_usize_add(v_i_3149_, v___x_3156_);
v_i_3149_ = v___x_3157_;
v_b_3151_ = v___x_3155_;
goto _start;
}
else
{
return v_b_3151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0___boxed(lean_object* v_as_3159_, lean_object* v_i_3160_, lean_object* v_stop_3161_, lean_object* v_b_3162_){
_start:
{
size_t v_i_boxed_3163_; size_t v_stop_boxed_3164_; lean_object* v_res_3165_; 
v_i_boxed_3163_ = lean_unbox_usize(v_i_3160_);
lean_dec(v_i_3160_);
v_stop_boxed_3164_ = lean_unbox_usize(v_stop_3161_);
lean_dec(v_stop_3161_);
v_res_3165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v_as_3159_, v_i_boxed_3163_, v_stop_boxed_3164_, v_b_3162_);
lean_dec_ref(v_as_3159_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(lean_object* v_t_3166_, lean_object* v___y_3167_){
_start:
{
lean_object* v___x_3169_; lean_object* v_infoState_3170_; uint8_t v_enabled_3171_; 
v___x_3169_ = lean_st_ref_get(v___y_3167_);
v_infoState_3170_ = lean_ctor_get(v___x_3169_, 7);
lean_inc_ref(v_infoState_3170_);
lean_dec(v___x_3169_);
v_enabled_3171_ = lean_ctor_get_uint8(v_infoState_3170_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3170_);
if (v_enabled_3171_ == 0)
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
lean_dec_ref(v_t_3166_);
v___x_3172_ = lean_box(0);
v___x_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
return v___x_3173_;
}
else
{
lean_object* v___x_3174_; lean_object* v_infoState_3175_; lean_object* v_env_3176_; lean_object* v_nextMacroScope_3177_; lean_object* v_ngen_3178_; lean_object* v_auxDeclNGen_3179_; lean_object* v_traceState_3180_; lean_object* v_cache_3181_; lean_object* v_messages_3182_; lean_object* v_snapshotTasks_3183_; lean_object* v___x_3185_; uint8_t v_isShared_3186_; uint8_t v_isSharedCheck_3205_; 
v___x_3174_ = lean_st_ref_take(v___y_3167_);
v_infoState_3175_ = lean_ctor_get(v___x_3174_, 7);
v_env_3176_ = lean_ctor_get(v___x_3174_, 0);
v_nextMacroScope_3177_ = lean_ctor_get(v___x_3174_, 1);
v_ngen_3178_ = lean_ctor_get(v___x_3174_, 2);
v_auxDeclNGen_3179_ = lean_ctor_get(v___x_3174_, 3);
v_traceState_3180_ = lean_ctor_get(v___x_3174_, 4);
v_cache_3181_ = lean_ctor_get(v___x_3174_, 5);
v_messages_3182_ = lean_ctor_get(v___x_3174_, 6);
v_snapshotTasks_3183_ = lean_ctor_get(v___x_3174_, 8);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3185_ = v___x_3174_;
v_isShared_3186_ = v_isSharedCheck_3205_;
goto v_resetjp_3184_;
}
else
{
lean_inc(v_snapshotTasks_3183_);
lean_inc(v_infoState_3175_);
lean_inc(v_messages_3182_);
lean_inc(v_cache_3181_);
lean_inc(v_traceState_3180_);
lean_inc(v_auxDeclNGen_3179_);
lean_inc(v_ngen_3178_);
lean_inc(v_nextMacroScope_3177_);
lean_inc(v_env_3176_);
lean_dec(v___x_3174_);
v___x_3185_ = lean_box(0);
v_isShared_3186_ = v_isSharedCheck_3205_;
goto v_resetjp_3184_;
}
v_resetjp_3184_:
{
uint8_t v_enabled_3187_; lean_object* v_assignment_3188_; lean_object* v_lazyAssignment_3189_; lean_object* v_trees_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3204_; 
v_enabled_3187_ = lean_ctor_get_uint8(v_infoState_3175_, sizeof(void*)*3);
v_assignment_3188_ = lean_ctor_get(v_infoState_3175_, 0);
v_lazyAssignment_3189_ = lean_ctor_get(v_infoState_3175_, 1);
v_trees_3190_ = lean_ctor_get(v_infoState_3175_, 2);
v_isSharedCheck_3204_ = !lean_is_exclusive(v_infoState_3175_);
if (v_isSharedCheck_3204_ == 0)
{
v___x_3192_ = v_infoState_3175_;
v_isShared_3193_ = v_isSharedCheck_3204_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_trees_3190_);
lean_inc(v_lazyAssignment_3189_);
lean_inc(v_assignment_3188_);
lean_dec(v_infoState_3175_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3204_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3194_; lean_object* v___x_3196_; 
v___x_3194_ = l_Lean_PersistentArray_push___redArg(v_trees_3190_, v_t_3166_);
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 2, v___x_3194_);
v___x_3196_ = v___x_3192_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v_assignment_3188_);
lean_ctor_set(v_reuseFailAlloc_3203_, 1, v_lazyAssignment_3189_);
lean_ctor_set(v_reuseFailAlloc_3203_, 2, v___x_3194_);
lean_ctor_set_uint8(v_reuseFailAlloc_3203_, sizeof(void*)*3, v_enabled_3187_);
v___x_3196_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
lean_object* v___x_3198_; 
if (v_isShared_3186_ == 0)
{
lean_ctor_set(v___x_3185_, 7, v___x_3196_);
v___x_3198_ = v___x_3185_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_env_3176_);
lean_ctor_set(v_reuseFailAlloc_3202_, 1, v_nextMacroScope_3177_);
lean_ctor_set(v_reuseFailAlloc_3202_, 2, v_ngen_3178_);
lean_ctor_set(v_reuseFailAlloc_3202_, 3, v_auxDeclNGen_3179_);
lean_ctor_set(v_reuseFailAlloc_3202_, 4, v_traceState_3180_);
lean_ctor_set(v_reuseFailAlloc_3202_, 5, v_cache_3181_);
lean_ctor_set(v_reuseFailAlloc_3202_, 6, v_messages_3182_);
lean_ctor_set(v_reuseFailAlloc_3202_, 7, v___x_3196_);
lean_ctor_set(v_reuseFailAlloc_3202_, 8, v_snapshotTasks_3183_);
v___x_3198_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3199_ = lean_st_ref_set(v___y_3167_, v___x_3198_);
v___x_3200_ = lean_box(0);
v___x_3201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3200_);
return v___x_3201_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg___boxed(lean_object* v_t_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3206_, v___y_3207_);
lean_dec(v___y_3207_);
return v_res_3209_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3210_ = lean_unsigned_to_nat(32u);
v___x_3211_ = lean_mk_empty_array_with_capacity(v___x_3210_);
v___x_3212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
return v___x_3212_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1(void){
_start:
{
size_t v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3213_ = ((size_t)5ULL);
v___x_3214_ = lean_unsigned_to_nat(0u);
v___x_3215_ = lean_unsigned_to_nat(32u);
v___x_3216_ = lean_mk_empty_array_with_capacity(v___x_3215_);
v___x_3217_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0);
v___x_3218_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3218_, 0, v___x_3217_);
lean_ctor_set(v___x_3218_, 1, v___x_3216_);
lean_ctor_set(v___x_3218_, 2, v___x_3214_);
lean_ctor_set(v___x_3218_, 3, v___x_3214_);
lean_ctor_set_usize(v___x_3218_, 4, v___x_3213_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(lean_object* v_t_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
lean_object* v___x_3223_; lean_object* v_infoState_3224_; uint8_t v_enabled_3225_; 
v___x_3223_ = lean_st_ref_get(v___y_3221_);
v_infoState_3224_ = lean_ctor_get(v___x_3223_, 7);
lean_inc_ref(v_infoState_3224_);
lean_dec(v___x_3223_);
v_enabled_3225_ = lean_ctor_get_uint8(v_infoState_3224_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3224_);
if (v_enabled_3225_ == 0)
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
lean_dec_ref(v_t_3219_);
v___x_3226_ = lean_box(0);
v___x_3227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3227_, 0, v___x_3226_);
return v___x_3227_;
}
else
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3228_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1);
v___x_3229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3229_, 0, v_t_3219_);
lean_ctor_set(v___x_3229_, 1, v___x_3228_);
v___x_3230_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v___x_3229_, v___y_3221_);
return v___x_3230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___boxed(lean_object* v_t_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_){
_start:
{
lean_object* v_res_3235_; 
v_res_3235_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v_t_3231_, v___y_3232_, v___y_3233_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
return v_res_3235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0(lean_object* v___x_3236_, lean_object* v___y_3237_){
_start:
{
lean_object* v___x_3238_; 
v___x_3238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3236_);
lean_ctor_set(v___x_3238_, 1, v___y_3237_);
return v___x_3238_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3240_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__0));
v___x_3241_ = l_Lean_stringToMessageData(v___x_3240_);
return v___x_3241_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__2));
v___x_3244_ = l_Lean_stringToMessageData(v___x_3243_);
return v___x_3244_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29(void){
_start:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__28));
v___x_3294_ = l_Lean_Json_mkObj(v___x_3293_);
return v___x_3294_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30(void){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v___x_3295_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29);
v___x_3296_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__19));
v___x_3297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3296_);
lean_ctor_set(v___x_3297_, 1, v___x_3295_);
return v___x_3297_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31(void){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3298_ = lean_box(0);
v___x_3299_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30);
v___x_3300_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3299_);
lean_ctor_set(v___x_3300_, 1, v___x_3298_);
return v___x_3300_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33(void){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3303_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__32));
v___x_3304_ = l_Lean_MessageData_ofFormat(v___x_3303_);
return v___x_3304_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35(void){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3306_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__34));
v___x_3307_ = l_Lean_stringToMessageData(v___x_3306_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(lean_object* v_suggestions_3309_, uint8_t v_forceList_3310_, lean_object* v_codeActionPrefix_x3f_3311_, lean_object* v_ref_3312_, lean_object* v_as_3313_, size_t v_sz_3314_, size_t v_i_3315_, lean_object* v_b_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
lean_object* v_a_3321_; lean_object* v___y_3326_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3337_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; uint8_t v___x_3365_; 
v___x_3365_ = lean_usize_dec_lt(v_i_3315_, v_sz_3314_);
if (v___x_3365_ == 0)
{
lean_object* v___x_3366_; 
lean_dec(v_ref_3312_);
lean_dec(v_codeActionPrefix_x3f_3311_);
v___x_3366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3366_, 0, v_b_3316_);
return v___x_3366_;
}
else
{
lean_object* v_a_3367_; lean_object* v_span_x3f_3368_; lean_object* v___x_3369_; lean_object* v___y_3371_; lean_object* v___y_3372_; uint8_t v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; uint8_t v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; uint8_t v___y_3457_; lean_object* v___y_3460_; uint8_t v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; uint8_t v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3470_; lean_object* v_postInfo_x3f_3471_; uint8_t v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; uint8_t v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; uint8_t v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; uint8_t v___y_3485_; lean_object* v___y_3486_; lean_object* v_edits_3487_; lean_object* v___y_3493_; lean_object* v___y_3494_; uint8_t v___y_3495_; lean_object* v_stop_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; uint8_t v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v_edits_3502_; lean_object* v___y_3511_; lean_object* v___y_3512_; uint8_t v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; uint8_t v___y_3517_; lean_object* v___y_3518_; lean_object* v___y_3519_; lean_object* v_edits_3520_; lean_object* v___y_3521_; lean_object* v___x_3545_; lean_object* v___y_3547_; uint8_t v___y_3548_; lean_object* v___y_3549_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; uint8_t v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3592_; lean_object* v___y_3593_; uint8_t v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; uint8_t v___y_3598_; lean_object* v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3610_; 
v_a_3367_ = lean_array_uget_borrowed(v_as_3313_, v_i_3315_);
v_span_x3f_3368_ = lean_ctor_get(v_a_3367_, 1);
v___x_3369_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_3545_ = l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_;
if (lean_obj_tag(v_span_x3f_3368_) == 0)
{
lean_inc(v_ref_3312_);
v___y_3610_ = v_ref_3312_;
goto v___jp_3609_;
}
else
{
lean_object* v_val_3631_; 
v_val_3631_ = lean_ctor_get(v_span_x3f_3368_, 0);
lean_inc(v_val_3631_);
v___y_3610_ = v_val_3631_;
goto v___jp_3609_;
}
v___jp_3370_:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___f_3391_; 
lean_inc_ref(v___y_3372_);
v___x_3377_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson(v___y_3372_);
v___x_3378_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__9));
v___x_3379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3378_);
lean_ctor_set(v___x_3379_, 1, v___x_3377_);
v___x_3380_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3381_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3381_, 0, v___y_3376_);
v___x_3382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3380_);
lean_ctor_set(v___x_3382_, 1, v___x_3381_);
v___x_3383_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3384_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3374_);
v___x_3385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3383_);
lean_ctor_set(v___x_3385_, 1, v___x_3384_);
v___x_3386_ = lean_box(0);
v___x_3387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3385_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
v___x_3388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3382_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
v___x_3389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3379_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
v___x_3390_ = l_Lean_Json_mkObj(v___x_3389_);
lean_dec_ref_known(v___x_3389_, 2);
v___f_3391_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3391_, 0, v___x_3390_);
if (v___y_3373_ == 0)
{
lean_object* v___x_3392_; 
v___x_3392_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString(v___y_3372_);
v___y_3345_ = v___y_3371_;
v___y_3346_ = v___f_3391_;
v___y_3347_ = v___y_3375_;
v___y_3348_ = v___x_3392_;
goto v___jp_3344_;
}
else
{
lean_object* v___x_3393_; lean_object* v___x_3394_; uint8_t v___x_3395_; 
v___x_3393_ = lean_unsigned_to_nat(0u);
v___x_3394_ = lean_array_get_size(v___y_3372_);
v___x_3395_ = lean_nat_dec_lt(v___x_3393_, v___x_3394_);
if (v___x_3395_ == 0)
{
lean_dec_ref(v___y_3372_);
v___y_3345_ = v___y_3371_;
v___y_3346_ = v___f_3391_;
v___y_3347_ = v___y_3375_;
v___y_3348_ = v___x_3369_;
goto v___jp_3344_;
}
else
{
uint8_t v___x_3396_; 
v___x_3396_ = lean_nat_dec_le(v___x_3394_, v___x_3394_);
if (v___x_3396_ == 0)
{
if (v___x_3395_ == 0)
{
lean_dec_ref(v___y_3372_);
v___y_3345_ = v___y_3371_;
v___y_3346_ = v___f_3391_;
v___y_3347_ = v___y_3375_;
v___y_3348_ = v___x_3369_;
goto v___jp_3344_;
}
else
{
size_t v___x_3397_; size_t v___x_3398_; lean_object* v___x_3399_; 
v___x_3397_ = ((size_t)0ULL);
v___x_3398_ = lean_usize_of_nat(v___x_3394_);
v___x_3399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3372_, v___x_3397_, v___x_3398_, v___x_3369_);
lean_dec_ref(v___y_3372_);
v___y_3345_ = v___y_3371_;
v___y_3346_ = v___f_3391_;
v___y_3347_ = v___y_3375_;
v___y_3348_ = v___x_3399_;
goto v___jp_3344_;
}
}
else
{
size_t v___x_3400_; size_t v___x_3401_; lean_object* v___x_3402_; 
v___x_3400_ = ((size_t)0ULL);
v___x_3401_ = lean_usize_of_nat(v___x_3394_);
v___x_3402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3372_, v___x_3400_, v___x_3401_, v___x_3369_);
lean_dec_ref(v___y_3372_);
v___y_3345_ = v___y_3371_;
v___y_3346_ = v___f_3391_;
v___y_3347_ = v___y_3375_;
v___y_3348_ = v___x_3402_;
goto v___jp_3344_;
}
}
}
}
v___jp_3403_:
{
if (lean_obj_tag(v___y_3408_) == 0)
{
lean_object* v___x_3412_; uint64_t v_javascriptHash_3413_; lean_object* v_suggestion_3414_; lean_object* v_messageData_x3f_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___f_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
lean_dec_ref(v___y_3406_);
v___x_3412_ = l_Lean_Meta_Hint_textInsertionWidget;
v_javascriptHash_3413_ = lean_ctor_get_uint64(v___x_3412_, sizeof(void*)*1);
v_suggestion_3414_ = lean_ctor_get(v___y_3405_, 0);
lean_inc_ref(v_suggestion_3414_);
v_messageData_x3f_3415_ = lean_ctor_get(v___y_3405_, 4);
lean_inc(v_messageData_x3f_3415_);
lean_dec_ref(v___y_3405_);
v___x_3416_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18));
v___x_3417_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3418_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3409_);
v___x_3419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3417_);
lean_ctor_set(v___x_3419_, 1, v___x_3418_);
v___x_3420_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3421_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3421_, 0, v___y_3411_);
v___x_3422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3420_);
lean_ctor_set(v___x_3422_, 1, v___x_3421_);
v___x_3423_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31);
v___x_3424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3422_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
v___x_3425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3419_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
v___x_3426_ = l_Lean_Json_mkObj(v___x_3425_);
lean_dec_ref_known(v___x_3425_, 2);
v___f_3427_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3427_, 0, v___x_3426_);
v___x_3428_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3428_, 0, v___x_3416_);
lean_ctor_set(v___x_3428_, 1, v___f_3427_);
lean_ctor_set_uint64(v___x_3428_, sizeof(void*)*2, v_javascriptHash_3413_);
v___x_3429_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33);
v___x_3430_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3428_);
lean_ctor_set(v___x_3430_, 1, v___x_3429_);
v___x_3431_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3431_);
lean_ctor_set(v___x_3432_, 1, v___x_3430_);
v___x_3433_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35);
v___x_3434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3432_);
lean_ctor_set(v___x_3434_, 1, v___x_3433_);
v___x_3435_ = l_Lean_stringToMessageData(v___y_3404_);
v___x_3436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3434_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
if (lean_obj_tag(v_messageData_x3f_3415_) == 0)
{
if (lean_obj_tag(v_suggestion_3414_) == 0)
{
lean_object* v_a_3437_; lean_object* v___x_3438_; 
v_a_3437_ = lean_ctor_get(v_suggestion_3414_, 1);
lean_inc(v_a_3437_);
lean_dec_ref_known(v_suggestion_3414_, 2);
v___x_3438_ = l_Lean_MessageData_ofSyntax(v_a_3437_);
v___y_3330_ = v___y_3410_;
v___y_3331_ = v___x_3436_;
v___y_3332_ = v___x_3438_;
goto v___jp_3329_;
}
else
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3447_; 
v_a_3439_ = lean_ctor_get(v_suggestion_3414_, 0);
v_isSharedCheck_3447_ = !lean_is_exclusive(v_suggestion_3414_);
if (v_isSharedCheck_3447_ == 0)
{
v___x_3441_ = v_suggestion_3414_;
v_isShared_3442_ = v_isSharedCheck_3447_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v_suggestion_3414_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3447_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3444_; 
if (v_isShared_3442_ == 0)
{
lean_ctor_set_tag(v___x_3441_, 3);
v___x_3444_ = v___x_3441_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v_a_3439_);
v___x_3444_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
lean_object* v___x_3445_; 
v___x_3445_ = l_Lean_MessageData_ofFormat(v___x_3444_);
v___y_3330_ = v___y_3410_;
v___y_3331_ = v___x_3436_;
v___y_3332_ = v___x_3445_;
goto v___jp_3329_;
}
}
}
}
else
{
lean_object* v_val_3448_; 
lean_dec_ref(v_suggestion_3414_);
v_val_3448_ = lean_ctor_get(v_messageData_x3f_3415_, 0);
lean_inc(v_val_3448_);
lean_dec_ref_known(v_messageData_x3f_3415_, 1);
v___y_3330_ = v___y_3410_;
v___y_3331_ = v___x_3436_;
v___y_3332_ = v_val_3448_;
goto v___jp_3329_;
}
}
else
{
lean_dec_ref_known(v___y_3408_, 1);
lean_dec_ref(v___y_3405_);
v___y_3371_ = v___y_3404_;
v___y_3372_ = v___y_3406_;
v___y_3373_ = v___y_3407_;
v___y_3374_ = v___y_3409_;
v___y_3375_ = v___y_3410_;
v___y_3376_ = v___y_3411_;
goto v___jp_3370_;
}
}
v___jp_3449_:
{
if (v___y_3457_ == 0)
{
lean_object* v_messageData_x3f_3458_; 
v_messageData_x3f_3458_ = lean_ctor_get(v___y_3451_, 4);
if (lean_obj_tag(v_messageData_x3f_3458_) == 0)
{
lean_dec(v___y_3453_);
lean_dec_ref(v___y_3451_);
v___y_3371_ = v___y_3450_;
v___y_3372_ = v___y_3452_;
v___y_3373_ = v___y_3457_;
v___y_3374_ = v___y_3454_;
v___y_3375_ = v___y_3455_;
v___y_3376_ = v___y_3456_;
goto v___jp_3370_;
}
else
{
v___y_3404_ = v___y_3450_;
v___y_3405_ = v___y_3451_;
v___y_3406_ = v___y_3452_;
v___y_3407_ = v___y_3457_;
v___y_3408_ = v___y_3453_;
v___y_3409_ = v___y_3454_;
v___y_3410_ = v___y_3455_;
v___y_3411_ = v___y_3456_;
goto v___jp_3403_;
}
}
else
{
v___y_3404_ = v___y_3450_;
v___y_3405_ = v___y_3451_;
v___y_3406_ = v___y_3452_;
v___y_3407_ = v___y_3457_;
v___y_3408_ = v___y_3453_;
v___y_3409_ = v___y_3454_;
v___y_3410_ = v___y_3455_;
v___y_3411_ = v___y_3456_;
goto v___jp_3403_;
}
}
v___jp_3459_:
{
if (v___y_3461_ == 4)
{
v___y_3450_ = v___y_3460_;
v___y_3451_ = v___y_3462_;
v___y_3452_ = v___y_3463_;
v___y_3453_ = v___y_3464_;
v___y_3454_ = v___y_3465_;
v___y_3455_ = v___y_3468_;
v___y_3456_ = v___y_3467_;
v___y_3457_ = v___x_3365_;
goto v___jp_3449_;
}
else
{
v___y_3450_ = v___y_3460_;
v___y_3451_ = v___y_3462_;
v___y_3452_ = v___y_3463_;
v___y_3453_ = v___y_3464_;
v___y_3454_ = v___y_3465_;
v___y_3455_ = v___y_3468_;
v___y_3456_ = v___y_3467_;
v___y_3457_ = v___y_3466_;
goto v___jp_3449_;
}
}
v___jp_3469_:
{
if (lean_obj_tag(v_postInfo_x3f_3471_) == 0)
{
v___y_3460_ = v___y_3478_;
v___y_3461_ = v___y_3472_;
v___y_3462_ = v___y_3470_;
v___y_3463_ = v___y_3473_;
v___y_3464_ = v___y_3474_;
v___y_3465_ = v___y_3475_;
v___y_3466_ = v___y_3476_;
v___y_3467_ = v___y_3477_;
v___y_3468_ = v___x_3369_;
goto v___jp_3459_;
}
else
{
lean_object* v_val_3479_; 
v_val_3479_ = lean_ctor_get(v_postInfo_x3f_3471_, 0);
lean_inc(v_val_3479_);
lean_dec_ref_known(v_postInfo_x3f_3471_, 1);
v___y_3460_ = v___y_3478_;
v___y_3461_ = v___y_3472_;
v___y_3462_ = v___y_3470_;
v___y_3463_ = v___y_3473_;
v___y_3464_ = v___y_3474_;
v___y_3465_ = v___y_3475_;
v___y_3466_ = v___y_3476_;
v___y_3467_ = v___y_3477_;
v___y_3468_ = v_val_3479_;
goto v___jp_3459_;
}
}
v___jp_3480_:
{
lean_object* v_preInfo_x3f_3488_; 
v_preInfo_x3f_3488_ = lean_ctor_get(v___y_3482_, 1);
if (lean_obj_tag(v_preInfo_x3f_3488_) == 0)
{
lean_object* v_postInfo_x3f_3489_; 
v_postInfo_x3f_3489_ = lean_ctor_get(v___y_3482_, 2);
lean_inc(v_postInfo_x3f_3489_);
v___y_3470_ = v___y_3482_;
v_postInfo_x3f_3471_ = v_postInfo_x3f_3489_;
v___y_3472_ = v___y_3481_;
v___y_3473_ = v_edits_3487_;
v___y_3474_ = v___y_3483_;
v___y_3475_ = v___y_3484_;
v___y_3476_ = v___y_3485_;
v___y_3477_ = v___y_3486_;
v___y_3478_ = v___x_3369_;
goto v___jp_3469_;
}
else
{
lean_object* v_postInfo_x3f_3490_; lean_object* v_val_3491_; 
v_postInfo_x3f_3490_ = lean_ctor_get(v___y_3482_, 2);
lean_inc(v_postInfo_x3f_3490_);
v_val_3491_ = lean_ctor_get(v_preInfo_x3f_3488_, 0);
lean_inc(v_val_3491_);
v___y_3470_ = v___y_3482_;
v_postInfo_x3f_3471_ = v_postInfo_x3f_3490_;
v___y_3472_ = v___y_3481_;
v___y_3473_ = v_edits_3487_;
v___y_3474_ = v___y_3483_;
v___y_3475_ = v___y_3484_;
v___y_3476_ = v___y_3485_;
v___y_3477_ = v___y_3486_;
v___y_3478_ = v_val_3491_;
goto v___jp_3469_;
}
}
v___jp_3492_:
{
uint8_t v___x_3503_; 
v___x_3503_ = lean_nat_dec_lt(v___y_3500_, v_stop_3496_);
if (v___x_3503_ == 0)
{
lean_dec(v___y_3500_);
lean_dec(v_stop_3496_);
v___y_3481_ = v___y_3495_;
v___y_3482_ = v___y_3494_;
v___y_3483_ = v___y_3497_;
v___y_3484_ = v___y_3498_;
v___y_3485_ = v___y_3499_;
v___y_3486_ = v___y_3501_;
v_edits_3487_ = v_edits_3502_;
goto v___jp_3480_;
}
else
{
lean_object* v_source_3504_; uint8_t v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; 
v_source_3504_ = lean_ctor_get(v___y_3493_, 0);
v___x_3505_ = 2;
v___x_3506_ = lean_string_utf8_extract(v_source_3504_, v___y_3500_, v_stop_3496_);
lean_dec(v_stop_3496_);
lean_dec(v___y_3500_);
v___x_3507_ = lean_box(v___x_3505_);
v___x_3508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3507_);
lean_ctor_set(v___x_3508_, 1, v___x_3506_);
v___x_3509_ = lean_array_push(v_edits_3502_, v___x_3508_);
v___y_3481_ = v___y_3495_;
v___y_3482_ = v___y_3494_;
v___y_3483_ = v___y_3497_;
v___y_3484_ = v___y_3498_;
v___y_3485_ = v___y_3499_;
v___y_3486_ = v___y_3501_;
v_edits_3487_ = v___x_3509_;
goto v___jp_3480_;
}
}
v___jp_3510_:
{
if (lean_obj_tag(v___y_3514_) == 0)
{
lean_dec(v___y_3518_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3511_);
v___y_3481_ = v___y_3513_;
v___y_3482_ = v___y_3512_;
v___y_3483_ = v___y_3514_;
v___y_3484_ = v___y_3516_;
v___y_3485_ = v___y_3517_;
v___y_3486_ = v___y_3519_;
v_edits_3487_ = v_edits_3520_;
goto v___jp_3480_;
}
else
{
lean_object* v_val_3522_; lean_object* v___x_3523_; 
v_val_3522_ = lean_ctor_get(v___y_3514_, 0);
v___x_3523_ = l_Lean_Syntax_getRange_x3f(v_val_3522_, v___y_3517_);
if (lean_obj_tag(v___x_3523_) == 1)
{
lean_object* v_val_3524_; uint8_t v___x_3525_; 
v_val_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_val_3524_);
lean_dec_ref_known(v___x_3523_, 1);
v___x_3525_ = l_Lean_Syntax_Range_includes(v_val_3524_, v___y_3511_, v___y_3517_, v___y_3517_);
lean_dec_ref(v___y_3511_);
if (v___x_3525_ == 0)
{
lean_dec(v_val_3524_);
lean_dec(v___y_3518_);
lean_dec(v___y_3515_);
v___y_3481_ = v___y_3513_;
v___y_3482_ = v___y_3512_;
v___y_3483_ = v___y_3514_;
v___y_3484_ = v___y_3516_;
v___y_3485_ = v___y_3517_;
v___y_3486_ = v___y_3519_;
v_edits_3487_ = v_edits_3520_;
goto v___jp_3480_;
}
else
{
lean_object* v_fileMap_3526_; lean_object* v_start_3527_; lean_object* v_stop_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3544_; 
v_fileMap_3526_ = lean_ctor_get(v___y_3521_, 1);
v_start_3527_ = lean_ctor_get(v_val_3524_, 0);
v_stop_3528_ = lean_ctor_get(v_val_3524_, 1);
v_isSharedCheck_3544_ = !lean_is_exclusive(v_val_3524_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3530_ = v_val_3524_;
v_isShared_3531_ = v_isSharedCheck_3544_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_stop_3528_);
lean_inc(v_start_3527_);
lean_dec(v_val_3524_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3544_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
uint8_t v___x_3532_; 
v___x_3532_ = lean_nat_dec_lt(v_start_3527_, v___y_3515_);
if (v___x_3532_ == 0)
{
lean_del_object(v___x_3530_);
lean_dec(v_start_3527_);
lean_dec(v___y_3515_);
v___y_3493_ = v_fileMap_3526_;
v___y_3494_ = v___y_3512_;
v___y_3495_ = v___y_3513_;
v_stop_3496_ = v_stop_3528_;
v___y_3497_ = v___y_3514_;
v___y_3498_ = v___y_3516_;
v___y_3499_ = v___y_3517_;
v___y_3500_ = v___y_3518_;
v___y_3501_ = v___y_3519_;
v_edits_3502_ = v_edits_3520_;
goto v___jp_3492_;
}
else
{
lean_object* v_source_3533_; uint8_t v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3538_; 
v_source_3533_ = lean_ctor_get(v_fileMap_3526_, 0);
v___x_3534_ = 2;
v___x_3535_ = lean_string_utf8_extract(v_source_3533_, v_start_3527_, v___y_3515_);
lean_dec(v___y_3515_);
lean_dec(v_start_3527_);
v___x_3536_ = lean_box(v___x_3534_);
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 1, v___x_3535_);
lean_ctor_set(v___x_3530_, 0, v___x_3536_);
v___x_3538_ = v___x_3530_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v___x_3536_);
lean_ctor_set(v_reuseFailAlloc_3543_, 1, v___x_3535_);
v___x_3538_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3539_ = lean_unsigned_to_nat(1u);
v___x_3540_ = lean_mk_empty_array_with_capacity(v___x_3539_);
v___x_3541_ = lean_array_push(v___x_3540_, v___x_3538_);
v___x_3542_ = l_Array_append___redArg(v___x_3541_, v_edits_3520_);
lean_dec_ref(v_edits_3520_);
v___y_3493_ = v_fileMap_3526_;
v___y_3494_ = v___y_3512_;
v___y_3495_ = v___y_3513_;
v_stop_3496_ = v_stop_3528_;
v___y_3497_ = v___y_3514_;
v___y_3498_ = v___y_3516_;
v___y_3499_ = v___y_3517_;
v___y_3500_ = v___y_3518_;
v___y_3501_ = v___y_3519_;
v_edits_3502_ = v___x_3542_;
goto v___jp_3492_;
}
}
}
}
}
else
{
lean_dec(v___x_3523_);
lean_dec(v___y_3518_);
lean_dec(v___y_3515_);
lean_dec_ref(v___y_3511_);
v___y_3481_ = v___y_3513_;
v___y_3482_ = v___y_3512_;
v___y_3483_ = v___y_3514_;
v___y_3484_ = v___y_3516_;
v___y_3485_ = v___y_3517_;
v___y_3486_ = v___y_3519_;
v_edits_3487_ = v_edits_3520_;
goto v___jp_3480_;
}
}
}
v___jp_3546_:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; 
lean_inc_ref(v___y_3549_);
v___x_3557_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3557_, 0, v___y_3553_);
lean_ctor_set(v___x_3557_, 1, v___y_3556_);
lean_ctor_set(v___x_3557_, 2, v___y_3549_);
v___x_3558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3545_);
lean_ctor_set(v___x_3558_, 1, v___x_3557_);
v___x_3559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3559_, 0, v___y_3552_);
lean_ctor_set(v___x_3559_, 1, v___x_3558_);
v___x_3560_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3559_);
v___x_3561_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v___x_3560_, v___y_3317_, v___y_3318_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v_messageData_x3f_3562_; 
lean_dec_ref_known(v___x_3561_, 1);
v_messageData_x3f_3562_ = lean_ctor_get(v___y_3549_, 4);
if (lean_obj_tag(v_messageData_x3f_3562_) == 1)
{
lean_object* v_start_3563_; lean_object* v_stop_3564_; lean_object* v_val_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; uint8_t v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v_start_3563_ = lean_ctor_get(v___y_3547_, 0);
lean_inc(v_start_3563_);
v_stop_3564_ = lean_ctor_get(v___y_3547_, 1);
lean_inc(v_stop_3564_);
v_val_3565_ = lean_ctor_get(v_messageData_x3f_3562_, 0);
v___x_3566_ = lean_box(0);
lean_inc(v_val_3565_);
v___x_3567_ = l_Lean_MessageData_format(v_val_3565_, v___x_3566_);
v___x_3568_ = 0;
v___x_3569_ = l_Std_Format_defWidth;
v___x_3570_ = lean_unsigned_to_nat(0u);
v___x_3571_ = l_Std_Format_pretty(v___x_3567_, v___x_3569_, v___x_3570_, v___x_3570_);
v___x_3572_ = lean_box(v___x_3568_);
v___x_3573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3572_);
lean_ctor_set(v___x_3573_, 1, v___x_3571_);
v___x_3574_ = lean_unsigned_to_nat(1u);
v___x_3575_ = lean_mk_empty_array_with_capacity(v___x_3574_);
v___x_3576_ = lean_array_push(v___x_3575_, v___x_3573_);
v___y_3511_ = v___y_3547_;
v___y_3512_ = v___y_3549_;
v___y_3513_ = v___y_3548_;
v___y_3514_ = v___y_3550_;
v___y_3515_ = v_start_3563_;
v___y_3516_ = v___y_3551_;
v___y_3517_ = v___y_3554_;
v___y_3518_ = v_stop_3564_;
v___y_3519_ = v___y_3555_;
v_edits_3520_ = v___x_3576_;
v___y_3521_ = v___y_3317_;
goto v___jp_3510_;
}
else
{
lean_object* v_fileMap_3577_; lean_object* v_start_3578_; lean_object* v_stop_3579_; lean_object* v_source_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
v_fileMap_3577_ = lean_ctor_get(v___y_3317_, 1);
v_start_3578_ = lean_ctor_get(v___y_3547_, 0);
lean_inc(v_start_3578_);
v_stop_3579_ = lean_ctor_get(v___y_3547_, 1);
lean_inc(v_stop_3579_);
v_source_3580_ = lean_ctor_get(v_fileMap_3577_, 0);
v___x_3581_ = lean_string_utf8_extract(v_source_3580_, v_start_3578_, v_stop_3579_);
lean_inc_ref(v___y_3555_);
v___x_3582_ = l_Lean_Meta_Hint_readableDiff(v___x_3581_, v___y_3555_, v___y_3548_);
v___y_3511_ = v___y_3547_;
v___y_3512_ = v___y_3549_;
v___y_3513_ = v___y_3548_;
v___y_3514_ = v___y_3550_;
v___y_3515_ = v_start_3578_;
v___y_3516_ = v___y_3551_;
v___y_3517_ = v___y_3554_;
v___y_3518_ = v_stop_3579_;
v___y_3519_ = v___y_3555_;
v_edits_3520_ = v___x_3582_;
v___y_3521_ = v___y_3317_;
goto v___jp_3510_;
}
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
lean_dec_ref(v___y_3555_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec_ref(v___y_3547_);
lean_dec_ref(v_b_3316_);
lean_dec(v_ref_3312_);
lean_dec(v_codeActionPrefix_x3f_3311_);
v_a_3583_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3561_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3561_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3583_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
v___jp_3591_:
{
lean_object* v_toCodeActionTitle_x3f_3601_; lean_object* v___x_3602_; 
v_toCodeActionTitle_x3f_3601_ = lean_ctor_get(v___y_3593_, 5);
v___x_3602_ = l_Lean_Syntax_ofRange(v___y_3600_, v___x_3365_);
if (lean_obj_tag(v_toCodeActionTitle_x3f_3601_) == 0)
{
if (lean_obj_tag(v_codeActionPrefix_x3f_3311_) == 0)
{
lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3603_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__36));
v___x_3604_ = lean_string_append(v___x_3603_, v___y_3599_);
v___y_3547_ = v___y_3592_;
v___y_3548_ = v___y_3594_;
v___y_3549_ = v___y_3593_;
v___y_3550_ = v___y_3595_;
v___y_3551_ = v___y_3596_;
v___y_3552_ = v___x_3602_;
v___y_3553_ = v___y_3597_;
v___y_3554_ = v___y_3598_;
v___y_3555_ = v___y_3599_;
v___y_3556_ = v___x_3604_;
goto v___jp_3546_;
}
else
{
lean_object* v_val_3605_; lean_object* v___x_3606_; 
v_val_3605_ = lean_ctor_get(v_codeActionPrefix_x3f_3311_, 0);
lean_inc(v_val_3605_);
v___x_3606_ = lean_string_append(v_val_3605_, v___y_3599_);
v___y_3547_ = v___y_3592_;
v___y_3548_ = v___y_3594_;
v___y_3549_ = v___y_3593_;
v___y_3550_ = v___y_3595_;
v___y_3551_ = v___y_3596_;
v___y_3552_ = v___x_3602_;
v___y_3553_ = v___y_3597_;
v___y_3554_ = v___y_3598_;
v___y_3555_ = v___y_3599_;
v___y_3556_ = v___x_3606_;
goto v___jp_3546_;
}
}
else
{
lean_object* v_val_3607_; lean_object* v___x_3608_; 
v_val_3607_ = lean_ctor_get(v_toCodeActionTitle_x3f_3601_, 0);
lean_inc(v_val_3607_);
lean_inc_ref(v___y_3599_);
v___x_3608_ = lean_apply_1(v_val_3607_, v___y_3599_);
v___y_3547_ = v___y_3592_;
v___y_3548_ = v___y_3594_;
v___y_3549_ = v___y_3593_;
v___y_3550_ = v___y_3595_;
v___y_3551_ = v___y_3596_;
v___y_3552_ = v___x_3602_;
v___y_3553_ = v___y_3597_;
v___y_3554_ = v___y_3598_;
v___y_3555_ = v___y_3599_;
v___y_3556_ = v___x_3608_;
goto v___jp_3546_;
}
}
v___jp_3609_:
{
uint8_t v___x_3611_; lean_object* v___x_3612_; 
v___x_3611_ = 0;
v___x_3612_ = l_Lean_Syntax_getRange_x3f(v___y_3610_, v___x_3611_);
lean_dec(v___y_3610_);
if (lean_obj_tag(v___x_3612_) == 1)
{
lean_object* v_val_3613_; lean_object* v_toTryThisSuggestion_3614_; lean_object* v_previewSpan_x3f_3615_; uint8_t v_diffGranularity_3616_; lean_object* v___x_3617_; 
v_val_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc_n(v_val_3613_, 2);
lean_dec_ref_known(v___x_3612_, 1);
v_toTryThisSuggestion_3614_ = lean_ctor_get(v_a_3367_, 0);
v_previewSpan_x3f_3615_ = lean_ctor_get(v_a_3367_, 2);
v_diffGranularity_3616_ = lean_ctor_get_uint8(v_a_3367_, sizeof(void*)*3);
lean_inc_ref(v_toTryThisSuggestion_3614_);
v___x_3617_ = l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(v_toTryThisSuggestion_3614_, v_val_3613_, v___y_3317_, v___y_3318_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; lean_object* v_range_3619_; lean_object* v_newText_3620_; lean_object* v___x_3621_; 
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_a_3618_);
lean_dec_ref_known(v___x_3617_, 1);
v_range_3619_ = lean_ctor_get(v_a_3618_, 0);
lean_inc_ref(v_range_3619_);
v_newText_3620_ = lean_ctor_get(v_a_3618_, 1);
lean_inc_ref(v_newText_3620_);
v___x_3621_ = l_Lean_Syntax_getRange_x3f(v_ref_3312_, v___x_3611_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_inc(v_previewSpan_x3f_3615_);
lean_inc_ref(v_toTryThisSuggestion_3614_);
lean_inc(v_val_3613_);
v___y_3592_ = v_val_3613_;
v___y_3593_ = v_toTryThisSuggestion_3614_;
v___y_3594_ = v_diffGranularity_3616_;
v___y_3595_ = v_previewSpan_x3f_3615_;
v___y_3596_ = v_range_3619_;
v___y_3597_ = v_a_3618_;
v___y_3598_ = v___x_3611_;
v___y_3599_ = v_newText_3620_;
v___y_3600_ = v_val_3613_;
goto v___jp_3591_;
}
else
{
lean_object* v_val_3622_; 
v_val_3622_ = lean_ctor_get(v___x_3621_, 0);
lean_inc(v_val_3622_);
lean_dec_ref_known(v___x_3621_, 1);
lean_inc(v_previewSpan_x3f_3615_);
lean_inc_ref(v_toTryThisSuggestion_3614_);
v___y_3592_ = v_val_3613_;
v___y_3593_ = v_toTryThisSuggestion_3614_;
v___y_3594_ = v_diffGranularity_3616_;
v___y_3595_ = v_previewSpan_x3f_3615_;
v___y_3596_ = v_range_3619_;
v___y_3597_ = v_a_3618_;
v___y_3598_ = v___x_3611_;
v___y_3599_ = v_newText_3620_;
v___y_3600_ = v_val_3622_;
goto v___jp_3591_;
}
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_dec(v_val_3613_);
lean_dec_ref(v_b_3316_);
lean_dec(v_ref_3312_);
lean_dec(v_codeActionPrefix_x3f_3311_);
v_a_3623_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3617_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3617_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3623_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
else
{
lean_dec(v___x_3612_);
v_a_3321_ = v_b_3316_;
goto v___jp_3320_;
}
}
}
v___jp_3320_:
{
size_t v___x_3322_; size_t v___x_3323_; 
v___x_3322_ = ((size_t)1ULL);
v___x_3323_ = lean_usize_add(v_i_3315_, v___x_3322_);
v_i_3315_ = v___x_3323_;
v_b_3316_ = v_a_3321_;
goto _start;
}
v___jp_3325_:
{
lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3327_ = l_Lean_MessageData_nestD(v___y_3326_);
v___x_3328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3328_, 0, v_b_3316_);
lean_ctor_set(v___x_3328_, 1, v___x_3327_);
v_a_3321_ = v___x_3328_;
goto v___jp_3320_;
}
v___jp_3329_:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3333_, 0, v___y_3331_);
lean_ctor_set(v___x_3333_, 1, v___y_3332_);
v___x_3334_ = l_Lean_stringToMessageData(v___y_3330_);
v___x_3335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3333_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
v___y_3326_ = v___x_3335_;
goto v___jp_3325_;
}
v___jp_3336_:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v___x_3338_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3339_ = lean_unsigned_to_nat(2u);
v___x_3340_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3);
v___x_3341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3340_);
lean_ctor_set(v___x_3341_, 1, v___y_3337_);
v___x_3342_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3339_);
lean_ctor_set(v___x_3342_, 1, v___x_3341_);
v___x_3343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3338_);
lean_ctor_set(v___x_3343_, 1, v___x_3342_);
v___y_3326_ = v___x_3343_;
goto v___jp_3325_;
}
v___jp_3344_:
{
lean_object* v___x_3349_; uint64_t v_javascriptHash_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; uint8_t v___x_3362_; 
v___x_3349_ = l_Lean_Meta_Hint_tryThisDiffWidget;
v_javascriptHash_3350_ = lean_ctor_get_uint64(v___x_3349_, sizeof(void*)*1);
v___x_3351_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8));
v___x_3352_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3352_, 0, v___x_3351_);
lean_ctor_set(v___x_3352_, 1, v___y_3346_);
lean_ctor_set_uint64(v___x_3352_, sizeof(void*)*2, v_javascriptHash_3350_);
v___x_3353_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3353_, 0, v___y_3348_);
v___x_3354_ = l_Lean_MessageData_ofFormat(v___x_3353_);
v___x_3355_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3352_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
v___x_3356_ = l_Lean_stringToMessageData(v___y_3345_);
v___x_3357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3356_);
lean_ctor_set(v___x_3357_, 1, v___x_3355_);
v___x_3358_ = l_Lean_stringToMessageData(v___y_3347_);
v___x_3359_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3357_);
lean_ctor_set(v___x_3359_, 1, v___x_3358_);
v___x_3360_ = lean_array_get_size(v_suggestions_3309_);
v___x_3361_ = lean_unsigned_to_nat(1u);
v___x_3362_ = lean_nat_dec_eq(v___x_3360_, v___x_3361_);
if (v___x_3362_ == 0)
{
v___y_3337_ = v___x_3359_;
goto v___jp_3336_;
}
else
{
if (v_forceList_3310_ == 0)
{
if (v___x_3362_ == 0)
{
v___y_3337_ = v___x_3359_;
goto v___jp_3336_;
}
else
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3363_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
lean_ctor_set(v___x_3364_, 1, v___x_3359_);
v___y_3326_ = v___x_3364_;
goto v___jp_3325_;
}
}
else
{
v___y_3337_ = v___x_3359_;
goto v___jp_3336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___boxed(lean_object* v_suggestions_3632_, lean_object* v_forceList_3633_, lean_object* v_codeActionPrefix_x3f_3634_, lean_object* v_ref_3635_, lean_object* v_as_3636_, lean_object* v_sz_3637_, lean_object* v_i_3638_, lean_object* v_b_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
uint8_t v_forceList_boxed_3643_; size_t v_sz_boxed_3644_; size_t v_i_boxed_3645_; lean_object* v_res_3646_; 
v_forceList_boxed_3643_ = lean_unbox(v_forceList_3633_);
v_sz_boxed_3644_ = lean_unbox_usize(v_sz_3637_);
lean_dec(v_sz_3637_);
v_i_boxed_3645_ = lean_unbox_usize(v_i_3638_);
lean_dec(v_i_3638_);
v_res_3646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3632_, v_forceList_boxed_3643_, v_codeActionPrefix_x3f_3634_, v_ref_3635_, v_as_3636_, v_sz_boxed_3644_, v_i_boxed_3645_, v_b_3639_, v___y_3640_, v___y_3641_);
lean_dec(v___y_3641_);
lean_dec_ref(v___y_3640_);
lean_dec_ref(v_as_3636_);
lean_dec_ref(v_suggestions_3632_);
return v_res_3646_;
}
}
static lean_object* _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0(void){
_start:
{
lean_object* v___x_3647_; lean_object* v_msg_3648_; 
v___x_3647_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v_msg_3648_ = l_Lean_stringToMessageData(v___x_3647_);
return v_msg_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage(lean_object* v_suggestions_3649_, lean_object* v_ref_3650_, lean_object* v_codeActionPrefix_x3f_3651_, uint8_t v_forceList_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_){
_start:
{
lean_object* v_msg_3656_; size_t v_sz_3657_; size_t v___x_3658_; lean_object* v___x_3659_; 
v_msg_3656_ = lean_obj_once(&l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0, &l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0_once, _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0);
v_sz_3657_ = lean_array_size(v_suggestions_3649_);
v___x_3658_ = ((size_t)0ULL);
v___x_3659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3649_, v_forceList_3652_, v_codeActionPrefix_x3f_3651_, v_ref_3650_, v_suggestions_3649_, v_sz_3657_, v___x_3658_, v_msg_3656_, v_a_3653_, v_a_3654_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage___boxed(lean_object* v_suggestions_3660_, lean_object* v_ref_3661_, lean_object* v_codeActionPrefix_x3f_3662_, lean_object* v_forceList_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_){
_start:
{
uint8_t v_forceList_boxed_3667_; lean_object* v_res_3668_; 
v_forceList_boxed_3667_ = lean_unbox(v_forceList_3663_);
v_res_3668_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3660_, v_ref_3661_, v_codeActionPrefix_x3f_3662_, v_forceList_boxed_3667_, v_a_3664_, v_a_3665_);
lean_dec(v_a_3665_);
lean_dec_ref(v_a_3664_);
lean_dec_ref(v_suggestions_3660_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(lean_object* v_t_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
lean_object* v___x_3673_; 
v___x_3673_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3669_, v___y_3671_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___boxed(lean_object* v_t_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
lean_object* v_res_3678_; 
v_res_3678_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(v_t_3674_, v___y_3675_, v___y_3676_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
return v_res_3678_;
}
}
static lean_object* _init_l_Lean_MessageData_hint___closed__3(void){
_start:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3683_ = ((lean_object*)(l_Lean_MessageData_hint___closed__2));
v___x_3684_ = l_Lean_stringToMessageData(v___x_3683_);
return v___x_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint(lean_object* v_hint_3685_, lean_object* v_suggestions_3686_, lean_object* v_ref_x3f_3687_, lean_object* v_codeActionPrefix_x3f_3688_, uint8_t v_forceList_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_){
_start:
{
lean_object* v___y_3694_; 
if (lean_obj_tag(v_ref_x3f_3687_) == 0)
{
lean_object* v_ref_3709_; 
v_ref_3709_ = lean_ctor_get(v_a_3690_, 5);
lean_inc(v_ref_3709_);
v___y_3694_ = v_ref_3709_;
goto v___jp_3693_;
}
else
{
lean_object* v_val_3710_; 
v_val_3710_ = lean_ctor_get(v_ref_x3f_3687_, 0);
lean_inc(v_val_3710_);
lean_dec_ref_known(v_ref_x3f_3687_, 1);
v___y_3694_ = v_val_3710_;
goto v___jp_3693_;
}
v___jp_3693_:
{
lean_object* v___x_3695_; 
v___x_3695_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3686_, v___y_3694_, v_codeActionPrefix_x3f_3688_, v_forceList_3689_, v_a_3690_, v_a_3691_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3708_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3698_ = v___x_3695_;
v_isShared_3699_ = v_isSharedCheck_3708_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3695_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3708_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3706_; 
v___x_3700_ = ((lean_object*)(l_Lean_MessageData_hint___closed__1));
v___x_3701_ = lean_obj_once(&l_Lean_MessageData_hint___closed__3, &l_Lean_MessageData_hint___closed__3_once, _init_l_Lean_MessageData_hint___closed__3);
v___x_3702_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3701_);
lean_ctor_set(v___x_3702_, 1, v_hint_3685_);
v___x_3703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3702_);
lean_ctor_set(v___x_3703_, 1, v_a_3696_);
v___x_3704_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3700_);
lean_ctor_set(v___x_3704_, 1, v___x_3703_);
if (v_isShared_3699_ == 0)
{
lean_ctor_set(v___x_3698_, 0, v___x_3704_);
v___x_3706_ = v___x_3698_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3704_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
else
{
lean_dec_ref(v_hint_3685_);
return v___x_3695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint___boxed(lean_object* v_hint_3711_, lean_object* v_suggestions_3712_, lean_object* v_ref_x3f_3713_, lean_object* v_codeActionPrefix_x3f_3714_, lean_object* v_forceList_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_){
_start:
{
uint8_t v_forceList_boxed_3719_; lean_object* v_res_3720_; 
v_forceList_boxed_3719_ = lean_unbox(v_forceList_3715_);
v_res_3720_ = l_Lean_MessageData_hint(v_hint_3711_, v_suggestions_3712_, v_ref_x3f_3713_, v_codeActionPrefix_x3f_3714_, v_forceList_boxed_3719_, v_a_3716_, v_a_3717_);
lean_dec(v_a_3717_);
lean_dec_ref(v_a_3716_);
lean_dec_ref(v_suggestions_3712_);
return v_res_3720_;
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
