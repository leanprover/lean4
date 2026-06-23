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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_toCtorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1(size_t v_sz_15_, size_t v_i_16_, lean_object* v_bs_17_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1___boxed(lean_object* v_sz_26_, lean_object* v_i_27_, lean_object* v_bs_28_){
_start:
{
size_t v_sz_boxed_29_; size_t v_i_boxed_30_; lean_object* v_res_31_; 
v_sz_boxed_29_ = lean_unbox_usize(v_sz_26_);
lean_dec(v_sz_26_);
v_i_boxed_30_ = lean_unbox_usize(v_i_27_);
lean_dec(v_i_27_);
v_res_31_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1(v_sz_boxed_29_, v_i_boxed_30_, v_bs_28_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1(lean_object* v_a_32_){
_start:
{
size_t v_sz_33_; size_t v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v_sz_33_ = lean_array_size(v_a_32_);
v___x_34_ = ((size_t)0ULL);
v___x_35_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1(v_sz_33_, v___x_34_, v_a_32_);
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
v___x_117_ = l_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1(v___x_116_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_toCtorIdx(uint8_t v_x_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_Meta_Hint_DiffGranularity_ctorIdx(v_x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_toCtorIdx___boxed(lean_object* v_x_232_){
_start:
{
uint8_t v_x_4__boxed_233_; lean_object* v_res_234_; 
v_x_4__boxed_233_ = lean_unbox(v_x_232_);
v_res_234_ = l_Lean_Meta_Hint_DiffGranularity_toCtorIdx(v_x_4__boxed_233_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim___redArg(lean_object* v_k_235_){
_start:
{
lean_inc(v_k_235_);
return v_k_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim___redArg___boxed(lean_object* v_k_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_Meta_Hint_DiffGranularity_ctorElim___redArg(v_k_236_);
lean_dec(v_k_236_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim(lean_object* v_motive_238_, lean_object* v_ctorIdx_239_, uint8_t v_t_240_, lean_object* v_h_241_, lean_object* v_k_242_){
_start:
{
lean_inc(v_k_242_);
return v_k_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim___boxed(lean_object* v_motive_243_, lean_object* v_ctorIdx_244_, lean_object* v_t_245_, lean_object* v_h_246_, lean_object* v_k_247_){
_start:
{
uint8_t v_t_boxed_248_; lean_object* v_res_249_; 
v_t_boxed_248_ = lean_unbox(v_t_245_);
v_res_249_ = l_Lean_Meta_Hint_DiffGranularity_ctorElim(v_motive_243_, v_ctorIdx_244_, v_t_boxed_248_, v_h_246_, v_k_247_);
lean_dec(v_k_247_);
lean_dec(v_ctorIdx_244_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim___redArg(lean_object* v_auto_250_){
_start:
{
lean_inc(v_auto_250_);
return v_auto_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim___redArg___boxed(lean_object* v_auto_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Meta_Hint_DiffGranularity_auto_elim___redArg(v_auto_251_);
lean_dec(v_auto_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim(lean_object* v_motive_253_, uint8_t v_t_254_, lean_object* v_h_255_, lean_object* v_auto_256_){
_start:
{
lean_inc(v_auto_256_);
return v_auto_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim___boxed(lean_object* v_motive_257_, lean_object* v_t_258_, lean_object* v_h_259_, lean_object* v_auto_260_){
_start:
{
uint8_t v_t_boxed_261_; lean_object* v_res_262_; 
v_t_boxed_261_ = lean_unbox(v_t_258_);
v_res_262_ = l_Lean_Meta_Hint_DiffGranularity_auto_elim(v_motive_257_, v_t_boxed_261_, v_h_259_, v_auto_260_);
lean_dec(v_auto_260_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim___redArg(lean_object* v_char_263_){
_start:
{
lean_inc(v_char_263_);
return v_char_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim___redArg___boxed(lean_object* v_char_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_Meta_Hint_DiffGranularity_char_elim___redArg(v_char_264_);
lean_dec(v_char_264_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim(lean_object* v_motive_266_, uint8_t v_t_267_, lean_object* v_h_268_, lean_object* v_char_269_){
_start:
{
lean_inc(v_char_269_);
return v_char_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim___boxed(lean_object* v_motive_270_, lean_object* v_t_271_, lean_object* v_h_272_, lean_object* v_char_273_){
_start:
{
uint8_t v_t_boxed_274_; lean_object* v_res_275_; 
v_t_boxed_274_ = lean_unbox(v_t_271_);
v_res_275_ = l_Lean_Meta_Hint_DiffGranularity_char_elim(v_motive_270_, v_t_boxed_274_, v_h_272_, v_char_273_);
lean_dec(v_char_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim___redArg(lean_object* v_word_276_){
_start:
{
lean_inc(v_word_276_);
return v_word_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim___redArg___boxed(lean_object* v_word_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l_Lean_Meta_Hint_DiffGranularity_word_elim___redArg(v_word_277_);
lean_dec(v_word_277_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim(lean_object* v_motive_279_, uint8_t v_t_280_, lean_object* v_h_281_, lean_object* v_word_282_){
_start:
{
lean_inc(v_word_282_);
return v_word_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim___boxed(lean_object* v_motive_283_, lean_object* v_t_284_, lean_object* v_h_285_, lean_object* v_word_286_){
_start:
{
uint8_t v_t_boxed_287_; lean_object* v_res_288_; 
v_t_boxed_287_ = lean_unbox(v_t_284_);
v_res_288_ = l_Lean_Meta_Hint_DiffGranularity_word_elim(v_motive_283_, v_t_boxed_287_, v_h_285_, v_word_286_);
lean_dec(v_word_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim___redArg(lean_object* v_all_289_){
_start:
{
lean_inc(v_all_289_);
return v_all_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim___redArg___boxed(lean_object* v_all_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Lean_Meta_Hint_DiffGranularity_all_elim___redArg(v_all_290_);
lean_dec(v_all_290_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim(lean_object* v_motive_292_, uint8_t v_t_293_, lean_object* v_h_294_, lean_object* v_all_295_){
_start:
{
lean_inc(v_all_295_);
return v_all_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim___boxed(lean_object* v_motive_296_, lean_object* v_t_297_, lean_object* v_h_298_, lean_object* v_all_299_){
_start:
{
uint8_t v_t_boxed_300_; lean_object* v_res_301_; 
v_t_boxed_300_ = lean_unbox(v_t_297_);
v_res_301_ = l_Lean_Meta_Hint_DiffGranularity_all_elim(v_motive_296_, v_t_boxed_300_, v_h_298_, v_all_299_);
lean_dec(v_all_299_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim___redArg(lean_object* v_none_302_){
_start:
{
lean_inc(v_none_302_);
return v_none_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim___redArg___boxed(lean_object* v_none_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_Meta_Hint_DiffGranularity_none_elim___redArg(v_none_303_);
lean_dec(v_none_303_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim(lean_object* v_motive_305_, uint8_t v_t_306_, lean_object* v_h_307_, lean_object* v_none_308_){
_start:
{
lean_inc(v_none_308_);
return v_none_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim___boxed(lean_object* v_motive_309_, lean_object* v_t_310_, lean_object* v_h_311_, lean_object* v_none_312_){
_start:
{
uint8_t v_t_boxed_313_; lean_object* v_res_314_; 
v_t_boxed_313_ = lean_unbox(v_t_310_);
v_res_314_ = l_Lean_Meta_Hint_DiffGranularity_none_elim(v_motive_309_, v_t_boxed_313_, v_h_311_, v_none_312_);
lean_dec(v_none_312_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_instCoeSuggestionTextSuggestion___lam__0(lean_object* v_t_315_){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; lean_object* v___x_319_; 
v___x_316_ = lean_box(0);
v___x_317_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_317_, 0, v_t_315_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
lean_ctor_set(v___x_317_, 2, v___x_316_);
lean_ctor_set(v___x_317_, 3, v___x_316_);
lean_ctor_set(v___x_317_, 4, v___x_316_);
lean_ctor_set(v___x_317_, 5, v___x_316_);
v___x_318_ = 0;
v___x_319_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_319_, 0, v___x_317_);
lean_ctor_set(v___x_319_, 1, v___x_316_);
lean_ctor_set(v___x_319_, 2, v___x_316_);
lean_ctor_set_uint8(v___x_319_, sizeof(void*)*3, v___x_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_instToMessageDataSuggestion___lam__0(lean_object* v_s_322_){
_start:
{
lean_object* v_toTryThisSuggestion_323_; lean_object* v_messageData_x3f_324_; 
v_toTryThisSuggestion_323_ = lean_ctor_get(v_s_322_, 0);
lean_inc_ref(v_toTryThisSuggestion_323_);
lean_dec_ref(v_s_322_);
v_messageData_x3f_324_ = lean_ctor_get(v_toTryThisSuggestion_323_, 4);
if (lean_obj_tag(v_messageData_x3f_324_) == 0)
{
lean_object* v_suggestion_325_; 
v_suggestion_325_ = lean_ctor_get(v_toTryThisSuggestion_323_, 0);
lean_inc_ref(v_suggestion_325_);
lean_dec_ref(v_toTryThisSuggestion_323_);
if (lean_obj_tag(v_suggestion_325_) == 0)
{
lean_object* v_a_326_; lean_object* v___x_327_; 
v_a_326_ = lean_ctor_get(v_suggestion_325_, 1);
lean_inc(v_a_326_);
lean_dec_ref_known(v_suggestion_325_, 2);
v___x_327_ = l_Lean_MessageData_ofSyntax(v_a_326_);
return v___x_327_;
}
else
{
lean_object* v_a_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_336_; 
v_a_328_ = lean_ctor_get(v_suggestion_325_, 0);
v_isSharedCheck_336_ = !lean_is_exclusive(v_suggestion_325_);
if (v_isSharedCheck_336_ == 0)
{
v___x_330_ = v_suggestion_325_;
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_a_328_);
lean_dec(v_suggestion_325_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_336_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
lean_object* v___x_333_; 
if (v_isShared_331_ == 0)
{
lean_ctor_set_tag(v___x_330_, 3);
v___x_333_ = v___x_330_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_335_; 
v_reuseFailAlloc_335_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_335_, 0, v_a_328_);
v___x_333_ = v_reuseFailAlloc_335_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_334_; 
v___x_334_ = l_Lean_MessageData_ofFormat(v___x_333_);
return v___x_334_;
}
}
}
}
else
{
lean_object* v_val_337_; 
lean_inc_ref(v_messageData_x3f_324_);
lean_dec_ref(v_toTryThisSuggestion_323_);
v_val_337_ = lean_ctor_get(v_messageData_x3f_324_, 0);
lean_inc(v_val_337_);
lean_dec_ref_known(v_messageData_x3f_324_, 1);
return v_val_337_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(lean_object* v_as_340_, size_t v_i_341_, size_t v_stop_342_, lean_object* v_b_343_){
_start:
{
lean_object* v___y_345_; uint8_t v___x_349_; 
v___x_349_ = lean_usize_dec_eq(v_i_341_, v_stop_342_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v_fst_351_; lean_object* v_snd_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_389_; 
v___x_350_ = lean_array_uget(v_as_340_, v_i_341_);
v_fst_351_ = lean_ctor_get(v___x_350_, 0);
v_snd_352_ = lean_ctor_get(v___x_350_, 1);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_389_ == 0)
{
v___x_354_ = v___x_350_;
v_isShared_355_ = v_isSharedCheck_389_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_snd_352_);
lean_inc(v_fst_351_);
lean_dec(v___x_350_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_389_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; lean_object* v___x_357_; uint8_t v___x_358_; 
v___x_356_ = lean_array_get_size(v_b_343_);
v___x_357_ = lean_unsigned_to_nat(0u);
v___x_358_ = lean_nat_dec_eq(v___x_356_, v___x_357_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v_fst_362_; lean_object* v_snd_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_381_; 
lean_del_object(v___x_354_);
v___x_359_ = lean_unsigned_to_nat(1u);
v___x_360_ = lean_nat_sub(v___x_356_, v___x_359_);
v___x_361_ = lean_array_fget(v_b_343_, v___x_360_);
v_fst_362_ = lean_ctor_get(v___x_361_, 0);
v_snd_363_ = lean_ctor_get(v___x_361_, 1);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_361_);
if (v_isSharedCheck_381_ == 0)
{
v___x_365_ = v___x_361_;
v_isShared_366_ = v_isSharedCheck_381_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_snd_363_);
lean_inc(v_fst_362_);
lean_dec(v___x_361_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_381_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
uint8_t v___x_367_; uint8_t v___x_368_; uint8_t v___x_369_; 
v___x_367_ = lean_unbox(v_fst_351_);
v___x_368_ = lean_unbox(v_fst_362_);
lean_dec(v_fst_362_);
v___x_369_ = l_Lean_Diff_instBEqAction_beq(v___x_367_, v___x_368_);
if (v___x_369_ == 0)
{
lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
lean_dec(v_snd_363_);
lean_dec(v___x_360_);
v___x_370_ = lean_mk_empty_array_with_capacity(v___x_359_);
v___x_371_ = lean_array_push(v___x_370_, v_snd_352_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 1, v___x_371_);
lean_ctor_set(v___x_365_, 0, v_fst_351_);
v___x_373_ = v___x_365_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_fst_351_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v___x_371_);
v___x_373_ = v_reuseFailAlloc_375_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; 
v___x_374_ = lean_array_push(v_b_343_, v___x_373_);
v___y_345_ = v___x_374_;
goto v___jp_344_;
}
}
else
{
lean_object* v___x_376_; lean_object* v___x_378_; 
v___x_376_ = lean_array_push(v_snd_363_, v_snd_352_);
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 1, v___x_376_);
lean_ctor_set(v___x_365_, 0, v_fst_351_);
v___x_378_ = v___x_365_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_fst_351_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v___x_376_);
v___x_378_ = v_reuseFailAlloc_380_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_379_; 
v___x_379_ = lean_array_fset(v_b_343_, v___x_360_, v___x_378_);
lean_dec(v___x_360_);
v___y_345_ = v___x_379_;
goto v___jp_344_;
}
}
}
}
else
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
lean_dec_ref(v_b_343_);
v___x_382_ = lean_unsigned_to_nat(1u);
v___x_383_ = lean_mk_empty_array_with_capacity(v___x_382_);
lean_inc_ref(v___x_383_);
v___x_384_ = lean_array_push(v___x_383_, v_snd_352_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 1, v___x_384_);
v___x_386_ = v___x_354_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_fst_351_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v___x_384_);
v___x_386_ = v_reuseFailAlloc_388_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_387_; 
v___x_387_ = lean_array_push(v___x_383_, v___x_386_);
v___y_345_ = v___x_387_;
goto v___jp_344_;
}
}
}
}
else
{
return v_b_343_;
}
v___jp_344_:
{
size_t v___x_346_; size_t v___x_347_; 
v___x_346_ = ((size_t)1ULL);
v___x_347_ = lean_usize_add(v_i_341_, v___x_346_);
v_i_341_ = v___x_347_;
v_b_343_ = v___y_345_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg___boxed(lean_object* v_as_390_, lean_object* v_i_391_, lean_object* v_stop_392_, lean_object* v_b_393_){
_start:
{
size_t v_i_boxed_394_; size_t v_stop_boxed_395_; lean_object* v_res_396_; 
v_i_boxed_394_ = lean_unbox_usize(v_i_391_);
lean_dec(v_i_391_);
v_stop_boxed_395_ = lean_unbox_usize(v_stop_392_);
lean_dec(v_stop_392_);
v_res_396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_as_390_, v_i_boxed_394_, v_stop_boxed_395_, v_b_393_);
lean_dec_ref(v_as_390_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(lean_object* v_ds_399_){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
v___x_400_ = lean_unsigned_to_nat(0u);
v___x_401_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg___closed__0));
v___x_402_ = lean_array_get_size(v_ds_399_);
v___x_403_ = lean_nat_dec_lt(v___x_400_, v___x_402_);
if (v___x_403_ == 0)
{
return v___x_401_;
}
else
{
uint8_t v___x_404_; 
v___x_404_ = lean_nat_dec_le(v___x_402_, v___x_402_);
if (v___x_404_ == 0)
{
if (v___x_403_ == 0)
{
return v___x_401_;
}
else
{
size_t v___x_405_; size_t v___x_406_; lean_object* v___x_407_; 
v___x_405_ = ((size_t)0ULL);
v___x_406_ = lean_usize_of_nat(v___x_402_);
v___x_407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_ds_399_, v___x_405_, v___x_406_, v___x_401_);
return v___x_407_;
}
}
else
{
size_t v___x_408_; size_t v___x_409_; lean_object* v___x_410_; 
v___x_408_ = ((size_t)0ULL);
v___x_409_ = lean_usize_of_nat(v___x_402_);
v___x_410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_ds_399_, v___x_408_, v___x_409_, v___x_401_);
return v___x_410_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg___boxed(lean_object* v_ds_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_ds_411_);
lean_dec_ref(v_ds_411_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits(lean_object* v_00_u03b1_413_, lean_object* v_ds_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_ds_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___boxed(lean_object* v_00_u03b1_416_, lean_object* v_ds_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits(v_00_u03b1_416_, v_ds_417_);
lean_dec_ref(v_ds_417_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0(lean_object* v_00_u03b1_419_, lean_object* v_as_420_, size_t v_i_421_, size_t v_stop_422_, lean_object* v_b_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_as_420_, v_i_421_, v_stop_422_, v_b_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___boxed(lean_object* v_00_u03b1_425_, lean_object* v_as_426_, lean_object* v_i_427_, lean_object* v_stop_428_, lean_object* v_b_429_){
_start:
{
size_t v_i_boxed_430_; size_t v_stop_boxed_431_; lean_object* v_res_432_; 
v_i_boxed_430_ = lean_unbox_usize(v_i_427_);
lean_dec(v_i_427_);
v_stop_boxed_431_ = lean_unbox_usize(v_stop_428_);
lean_dec(v_stop_428_);
v_res_432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0(v_00_u03b1_425_, v_as_426_, v_i_boxed_430_, v_stop_boxed_431_, v_b_429_);
lean_dec_ref(v_as_426_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(size_t v_sz_433_, size_t v_i_434_, lean_object* v_bs_435_){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = lean_usize_dec_lt(v_i_434_, v_sz_433_);
if (v___x_436_ == 0)
{
return v_bs_435_;
}
else
{
lean_object* v_v_437_; lean_object* v_fst_438_; lean_object* v_snd_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_454_; 
v_v_437_ = lean_array_uget(v_bs_435_, v_i_434_);
v_fst_438_ = lean_ctor_get(v_v_437_, 0);
v_snd_439_ = lean_ctor_get(v_v_437_, 1);
v_isSharedCheck_454_ = !lean_is_exclusive(v_v_437_);
if (v_isSharedCheck_454_ == 0)
{
v___x_441_ = v_v_437_;
v_isShared_442_ = v_isSharedCheck_454_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_snd_439_);
lean_inc(v_fst_438_);
lean_dec(v_v_437_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_454_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v_bs_x27_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_443_ = lean_unsigned_to_nat(0u);
v_bs_x27_444_ = lean_array_uset(v_bs_435_, v_i_434_, v___x_443_);
v___x_445_ = lean_array_to_list(v_snd_439_);
v___x_446_ = lean_string_mk(v___x_445_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 1, v___x_446_);
v___x_448_ = v___x_441_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_fst_438_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v___x_446_);
v___x_448_ = v_reuseFailAlloc_453_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
size_t v___x_449_; size_t v___x_450_; lean_object* v___x_451_; 
v___x_449_ = ((size_t)1ULL);
v___x_450_ = lean_usize_add(v_i_434_, v___x_449_);
v___x_451_ = lean_array_uset(v_bs_x27_444_, v_i_434_, v___x_448_);
v_i_434_ = v___x_450_;
v_bs_435_ = v___x_451_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0___boxed(lean_object* v_sz_455_, lean_object* v_i_456_, lean_object* v_bs_457_){
_start:
{
size_t v_sz_boxed_458_; size_t v_i_boxed_459_; lean_object* v_res_460_; 
v_sz_boxed_458_ = lean_unbox_usize(v_sz_455_);
lean_dec(v_sz_455_);
v_i_boxed_459_ = lean_unbox_usize(v_i_456_);
lean_dec(v_i_456_);
v_res_460_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_boxed_458_, v_i_boxed_459_, v_bs_457_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(lean_object* v_d_461_){
_start:
{
lean_object* v___x_462_; size_t v_sz_463_; size_t v___x_464_; lean_object* v___x_465_; 
v___x_462_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_d_461_);
v_sz_463_ = lean_array_size(v___x_462_);
v___x_464_ = ((size_t)0ULL);
v___x_465_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_463_, v___x_464_, v___x_462_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff___boxed(lean_object* v_d_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v_d_466_);
lean_dec_ref(v_d_466_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(size_t v_sz_468_, size_t v_i_469_, lean_object* v_bs_470_){
_start:
{
uint8_t v___x_471_; 
v___x_471_ = lean_usize_dec_lt(v_i_469_, v_sz_468_);
if (v___x_471_ == 0)
{
return v_bs_470_;
}
else
{
lean_object* v_v_472_; lean_object* v___x_473_; lean_object* v_bs_x27_474_; uint8_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; size_t v___x_478_; size_t v___x_479_; lean_object* v___x_480_; 
v_v_472_ = lean_array_uget(v_bs_470_, v_i_469_);
v___x_473_ = lean_unsigned_to_nat(0u);
v_bs_x27_474_ = lean_array_uset(v_bs_470_, v_i_469_, v___x_473_);
v___x_475_ = 0;
v___x_476_ = lean_box(v___x_475_);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v_v_472_);
v___x_478_ = ((size_t)1ULL);
v___x_479_ = lean_usize_add(v_i_469_, v___x_478_);
v___x_480_ = lean_array_uset(v_bs_x27_474_, v_i_469_, v___x_477_);
v_i_469_ = v___x_479_;
v_bs_470_ = v___x_480_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9___boxed(lean_object* v_sz_482_, lean_object* v_i_483_, lean_object* v_bs_484_){
_start:
{
size_t v_sz_boxed_485_; size_t v_i_boxed_486_; lean_object* v_res_487_; 
v_sz_boxed_485_ = lean_unbox_usize(v_sz_482_);
lean_dec(v_sz_482_);
v_i_boxed_486_ = lean_unbox_usize(v_i_483_);
lean_dec(v_i_483_);
v_res_487_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(v_sz_boxed_485_, v_i_boxed_486_, v_bs_484_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(lean_object* v___x_488_, lean_object* v_original_489_, lean_object* v_a_490_){
_start:
{
lean_object* v_fst_491_; lean_object* v_snd_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_511_; 
v_fst_491_ = lean_ctor_get(v_a_490_, 0);
v_snd_492_ = lean_ctor_get(v_a_490_, 1);
v_isSharedCheck_511_ = !lean_is_exclusive(v_a_490_);
if (v_isSharedCheck_511_ == 0)
{
v___x_494_ = v_a_490_;
v_isShared_495_ = v_isSharedCheck_511_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_snd_492_);
lean_inc(v_fst_491_);
lean_dec(v_a_490_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_511_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
uint8_t v___x_496_; 
v___x_496_ = lean_nat_dec_lt(v_snd_492_, v___x_488_);
if (v___x_496_ == 0)
{
lean_object* v___x_498_; 
if (v_isShared_495_ == 0)
{
v___x_498_ = v___x_494_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_fst_491_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_snd_492_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
else
{
uint8_t v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_500_ = 1;
v___x_501_ = lean_array_fget_borrowed(v_original_489_, v_snd_492_);
v___x_502_ = lean_box(v___x_500_);
lean_inc(v___x_501_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 1, v___x_501_);
lean_ctor_set(v___x_494_, 0, v___x_502_);
v___x_504_ = v___x_494_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v___x_501_);
v___x_504_ = v_reuseFailAlloc_510_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_505_ = lean_array_push(v_fst_491_, v___x_504_);
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = lean_nat_add(v_snd_492_, v___x_506_);
lean_dec(v_snd_492_);
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_505_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
v_a_490_ = v___x_508_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg___boxed(lean_object* v___x_512_, lean_object* v_original_513_, lean_object* v_a_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_512_, v_original_513_, v_a_514_);
lean_dec_ref(v_original_513_);
lean_dec(v___x_512_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg(uint32_t v_a_516_, lean_object* v_x_517_){
_start:
{
if (lean_obj_tag(v_x_517_) == 0)
{
lean_object* v___x_518_; 
v___x_518_ = lean_box(0);
return v___x_518_;
}
else
{
lean_object* v_key_519_; lean_object* v_value_520_; lean_object* v_tail_521_; uint32_t v___x_522_; uint8_t v___x_523_; 
v_key_519_ = lean_ctor_get(v_x_517_, 0);
v_value_520_ = lean_ctor_get(v_x_517_, 1);
v_tail_521_ = lean_ctor_get(v_x_517_, 2);
v___x_522_ = lean_unbox_uint32(v_key_519_);
v___x_523_ = lean_uint32_dec_eq(v___x_522_, v_a_516_);
if (v___x_523_ == 0)
{
v_x_517_ = v_tail_521_;
goto _start;
}
else
{
lean_object* v___x_525_; 
lean_inc(v_value_520_);
v___x_525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_525_, 0, v_value_520_);
return v___x_525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg___boxed(lean_object* v_a_526_, lean_object* v_x_527_){
_start:
{
uint32_t v_a_boxed_528_; lean_object* v_res_529_; 
v_a_boxed_528_ = lean_unbox_uint32(v_a_526_);
lean_dec(v_a_526_);
v_res_529_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg(v_a_boxed_528_, v_x_527_);
lean_dec(v_x_527_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(lean_object* v_m_530_, uint32_t v_a_531_){
_start:
{
lean_object* v_buckets_532_; lean_object* v___x_533_; uint64_t v___x_534_; uint64_t v___x_535_; uint64_t v___x_536_; uint64_t v_fold_537_; uint64_t v___x_538_; uint64_t v___x_539_; uint64_t v___x_540_; size_t v___x_541_; size_t v___x_542_; size_t v___x_543_; size_t v___x_544_; size_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_buckets_532_ = lean_ctor_get(v_m_530_, 1);
v___x_533_ = lean_array_get_size(v_buckets_532_);
v___x_534_ = lean_uint32_to_uint64(v_a_531_);
v___x_535_ = 32ULL;
v___x_536_ = lean_uint64_shift_right(v___x_534_, v___x_535_);
v_fold_537_ = lean_uint64_xor(v___x_534_, v___x_536_);
v___x_538_ = 16ULL;
v___x_539_ = lean_uint64_shift_right(v_fold_537_, v___x_538_);
v___x_540_ = lean_uint64_xor(v_fold_537_, v___x_539_);
v___x_541_ = lean_uint64_to_usize(v___x_540_);
v___x_542_ = lean_usize_of_nat(v___x_533_);
v___x_543_ = ((size_t)1ULL);
v___x_544_ = lean_usize_sub(v___x_542_, v___x_543_);
v___x_545_ = lean_usize_land(v___x_541_, v___x_544_);
v___x_546_ = lean_array_uget_borrowed(v_buckets_532_, v___x_545_);
v___x_547_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg(v_a_531_, v___x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg___boxed(lean_object* v_m_548_, lean_object* v_a_549_){
_start:
{
uint32_t v_a_boxed_550_; lean_object* v_res_551_; 
v_a_boxed_550_ = lean_unbox_uint32(v_a_549_);
lean_dec(v_a_549_);
v_res_551_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(v_m_548_, v_a_boxed_550_);
lean_dec_ref(v_m_548_);
return v_res_551_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg(uint32_t v_a_552_, lean_object* v_x_553_){
_start:
{
if (lean_obj_tag(v_x_553_) == 0)
{
uint8_t v___x_554_; 
v___x_554_ = 0;
return v___x_554_;
}
else
{
lean_object* v_key_555_; lean_object* v_tail_556_; uint32_t v___x_557_; uint8_t v___x_558_; 
v_key_555_ = lean_ctor_get(v_x_553_, 0);
v_tail_556_ = lean_ctor_get(v_x_553_, 2);
v___x_557_ = lean_unbox_uint32(v_key_555_);
v___x_558_ = lean_uint32_dec_eq(v___x_557_, v_a_552_);
if (v___x_558_ == 0)
{
v_x_553_ = v_tail_556_;
goto _start;
}
else
{
return v___x_558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg___boxed(lean_object* v_a_560_, lean_object* v_x_561_){
_start:
{
uint32_t v_a_boxed_562_; uint8_t v_res_563_; lean_object* v_r_564_; 
v_a_boxed_562_ = lean_unbox_uint32(v_a_560_);
lean_dec(v_a_560_);
v_res_563_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg(v_a_boxed_562_, v_x_561_);
lean_dec(v_x_561_);
v_r_564_ = lean_box(v_res_563_);
return v_r_564_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(uint32_t v_a_565_, lean_object* v_b_566_, lean_object* v_x_567_){
_start:
{
if (lean_obj_tag(v_x_567_) == 0)
{
lean_dec(v_b_566_);
return v_x_567_;
}
else
{
lean_object* v_key_568_; lean_object* v_value_569_; lean_object* v_tail_570_; lean_object* v___x_572_; uint8_t v_isShared_573_; uint8_t v_isSharedCheck_584_; 
v_key_568_ = lean_ctor_get(v_x_567_, 0);
v_value_569_ = lean_ctor_get(v_x_567_, 1);
v_tail_570_ = lean_ctor_get(v_x_567_, 2);
v_isSharedCheck_584_ = !lean_is_exclusive(v_x_567_);
if (v_isSharedCheck_584_ == 0)
{
v___x_572_ = v_x_567_;
v_isShared_573_ = v_isSharedCheck_584_;
goto v_resetjp_571_;
}
else
{
lean_inc(v_tail_570_);
lean_inc(v_value_569_);
lean_inc(v_key_568_);
lean_dec(v_x_567_);
v___x_572_ = lean_box(0);
v_isShared_573_ = v_isSharedCheck_584_;
goto v_resetjp_571_;
}
v_resetjp_571_:
{
uint32_t v___x_574_; uint8_t v___x_575_; 
v___x_574_ = lean_unbox_uint32(v_key_568_);
v___x_575_ = lean_uint32_dec_eq(v___x_574_, v_a_565_);
if (v___x_575_ == 0)
{
lean_object* v___x_576_; lean_object* v___x_578_; 
v___x_576_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(v_a_565_, v_b_566_, v_tail_570_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 2, v___x_576_);
v___x_578_ = v___x_572_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v_key_568_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_value_569_);
lean_ctor_set(v_reuseFailAlloc_579_, 2, v___x_576_);
v___x_578_ = v_reuseFailAlloc_579_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
return v___x_578_;
}
}
else
{
lean_object* v___x_580_; lean_object* v___x_582_; 
lean_dec(v_value_569_);
lean_dec(v_key_568_);
v___x_580_ = lean_box_uint32(v_a_565_);
if (v_isShared_573_ == 0)
{
lean_ctor_set(v___x_572_, 1, v_b_566_);
lean_ctor_set(v___x_572_, 0, v___x_580_);
v___x_582_ = v___x_572_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_583_, 1, v_b_566_);
lean_ctor_set(v_reuseFailAlloc_583_, 2, v_tail_570_);
v___x_582_ = v_reuseFailAlloc_583_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
return v___x_582_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg___boxed(lean_object* v_a_585_, lean_object* v_b_586_, lean_object* v_x_587_){
_start:
{
uint32_t v_a_boxed_588_; lean_object* v_res_589_; 
v_a_boxed_588_ = lean_unbox_uint32(v_a_585_);
lean_dec(v_a_585_);
v_res_589_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(v_a_boxed_588_, v_b_586_, v_x_587_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29___redArg(lean_object* v_x_590_, lean_object* v_x_591_){
_start:
{
if (lean_obj_tag(v_x_591_) == 0)
{
return v_x_590_;
}
else
{
lean_object* v_key_592_; lean_object* v_value_593_; lean_object* v_tail_594_; lean_object* v___x_596_; uint8_t v_isShared_597_; uint8_t v_isSharedCheck_618_; 
v_key_592_ = lean_ctor_get(v_x_591_, 0);
v_value_593_ = lean_ctor_get(v_x_591_, 1);
v_tail_594_ = lean_ctor_get(v_x_591_, 2);
v_isSharedCheck_618_ = !lean_is_exclusive(v_x_591_);
if (v_isSharedCheck_618_ == 0)
{
v___x_596_ = v_x_591_;
v_isShared_597_ = v_isSharedCheck_618_;
goto v_resetjp_595_;
}
else
{
lean_inc(v_tail_594_);
lean_inc(v_value_593_);
lean_inc(v_key_592_);
lean_dec(v_x_591_);
v___x_596_ = lean_box(0);
v_isShared_597_ = v_isSharedCheck_618_;
goto v_resetjp_595_;
}
v_resetjp_595_:
{
lean_object* v___x_598_; uint32_t v___x_599_; uint64_t v___x_600_; uint64_t v___x_601_; uint64_t v___x_602_; uint64_t v_fold_603_; uint64_t v___x_604_; uint64_t v___x_605_; uint64_t v___x_606_; size_t v___x_607_; size_t v___x_608_; size_t v___x_609_; size_t v___x_610_; size_t v___x_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_598_ = lean_array_get_size(v_x_590_);
v___x_599_ = lean_unbox_uint32(v_key_592_);
v___x_600_ = lean_uint32_to_uint64(v___x_599_);
v___x_601_ = 32ULL;
v___x_602_ = lean_uint64_shift_right(v___x_600_, v___x_601_);
v_fold_603_ = lean_uint64_xor(v___x_600_, v___x_602_);
v___x_604_ = 16ULL;
v___x_605_ = lean_uint64_shift_right(v_fold_603_, v___x_604_);
v___x_606_ = lean_uint64_xor(v_fold_603_, v___x_605_);
v___x_607_ = lean_uint64_to_usize(v___x_606_);
v___x_608_ = lean_usize_of_nat(v___x_598_);
v___x_609_ = ((size_t)1ULL);
v___x_610_ = lean_usize_sub(v___x_608_, v___x_609_);
v___x_611_ = lean_usize_land(v___x_607_, v___x_610_);
v___x_612_ = lean_array_uget_borrowed(v_x_590_, v___x_611_);
lean_inc(v___x_612_);
if (v_isShared_597_ == 0)
{
lean_ctor_set(v___x_596_, 2, v___x_612_);
v___x_614_ = v___x_596_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_key_592_);
lean_ctor_set(v_reuseFailAlloc_617_, 1, v_value_593_);
lean_ctor_set(v_reuseFailAlloc_617_, 2, v___x_612_);
v___x_614_ = v_reuseFailAlloc_617_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
lean_object* v___x_615_; 
v___x_615_ = lean_array_uset(v_x_590_, v___x_611_, v___x_614_);
v_x_590_ = v___x_615_;
v_x_591_ = v_tail_594_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28___redArg(lean_object* v_i_619_, lean_object* v_source_620_, lean_object* v_target_621_){
_start:
{
lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_622_ = lean_array_get_size(v_source_620_);
v___x_623_ = lean_nat_dec_lt(v_i_619_, v___x_622_);
if (v___x_623_ == 0)
{
lean_dec_ref(v_source_620_);
lean_dec(v_i_619_);
return v_target_621_;
}
else
{
lean_object* v_es_624_; lean_object* v___x_625_; lean_object* v_source_626_; lean_object* v_target_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v_es_624_ = lean_array_fget(v_source_620_, v_i_619_);
v___x_625_ = lean_box(0);
v_source_626_ = lean_array_fset(v_source_620_, v_i_619_, v___x_625_);
v_target_627_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29___redArg(v_target_621_, v_es_624_);
v___x_628_ = lean_unsigned_to_nat(1u);
v___x_629_ = lean_nat_add(v_i_619_, v___x_628_);
lean_dec(v_i_619_);
v_i_619_ = v___x_629_;
v_source_620_ = v_source_626_;
v_target_621_ = v_target_627_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23___redArg(lean_object* v_data_631_){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v_nbuckets_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_632_ = lean_array_get_size(v_data_631_);
v___x_633_ = lean_unsigned_to_nat(2u);
v_nbuckets_634_ = lean_nat_mul(v___x_632_, v___x_633_);
v___x_635_ = lean_unsigned_to_nat(0u);
v___x_636_ = lean_box(0);
v___x_637_ = lean_mk_array(v_nbuckets_634_, v___x_636_);
v___x_638_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28___redArg(v___x_635_, v_data_631_, v___x_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(lean_object* v_m_639_, uint32_t v_a_640_, lean_object* v_b_641_){
_start:
{
lean_object* v_size_642_; lean_object* v_buckets_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_687_; 
v_size_642_ = lean_ctor_get(v_m_639_, 0);
v_buckets_643_ = lean_ctor_get(v_m_639_, 1);
v_isSharedCheck_687_ = !lean_is_exclusive(v_m_639_);
if (v_isSharedCheck_687_ == 0)
{
v___x_645_ = v_m_639_;
v_isShared_646_ = v_isSharedCheck_687_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_buckets_643_);
lean_inc(v_size_642_);
lean_dec(v_m_639_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_687_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_647_; uint64_t v___x_648_; uint64_t v___x_649_; uint64_t v___x_650_; uint64_t v_fold_651_; uint64_t v___x_652_; uint64_t v___x_653_; uint64_t v___x_654_; size_t v___x_655_; size_t v___x_656_; size_t v___x_657_; size_t v___x_658_; size_t v___x_659_; lean_object* v_bkt_660_; uint8_t v___x_661_; 
v___x_647_ = lean_array_get_size(v_buckets_643_);
v___x_648_ = lean_uint32_to_uint64(v_a_640_);
v___x_649_ = 32ULL;
v___x_650_ = lean_uint64_shift_right(v___x_648_, v___x_649_);
v_fold_651_ = lean_uint64_xor(v___x_648_, v___x_650_);
v___x_652_ = 16ULL;
v___x_653_ = lean_uint64_shift_right(v_fold_651_, v___x_652_);
v___x_654_ = lean_uint64_xor(v_fold_651_, v___x_653_);
v___x_655_ = lean_uint64_to_usize(v___x_654_);
v___x_656_ = lean_usize_of_nat(v___x_647_);
v___x_657_ = ((size_t)1ULL);
v___x_658_ = lean_usize_sub(v___x_656_, v___x_657_);
v___x_659_ = lean_usize_land(v___x_655_, v___x_658_);
v_bkt_660_ = lean_array_uget_borrowed(v_buckets_643_, v___x_659_);
v___x_661_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg(v_a_640_, v_bkt_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; lean_object* v_size_x27_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v_buckets_x27_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v___x_662_ = lean_unsigned_to_nat(1u);
v_size_x27_663_ = lean_nat_add(v_size_642_, v___x_662_);
lean_dec(v_size_642_);
v___x_664_ = lean_box_uint32(v_a_640_);
lean_inc(v_bkt_660_);
v___x_665_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v_b_641_);
lean_ctor_set(v___x_665_, 2, v_bkt_660_);
v_buckets_x27_666_ = lean_array_uset(v_buckets_643_, v___x_659_, v___x_665_);
v___x_667_ = lean_unsigned_to_nat(4u);
v___x_668_ = lean_nat_mul(v_size_x27_663_, v___x_667_);
v___x_669_ = lean_unsigned_to_nat(3u);
v___x_670_ = lean_nat_div(v___x_668_, v___x_669_);
lean_dec(v___x_668_);
v___x_671_ = lean_array_get_size(v_buckets_x27_666_);
v___x_672_ = lean_nat_dec_le(v___x_670_, v___x_671_);
lean_dec(v___x_670_);
if (v___x_672_ == 0)
{
lean_object* v_val_673_; lean_object* v___x_675_; 
v_val_673_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23___redArg(v_buckets_x27_666_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 1, v_val_673_);
lean_ctor_set(v___x_645_, 0, v_size_x27_663_);
v___x_675_ = v___x_645_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_size_x27_663_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_val_673_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
else
{
lean_object* v___x_678_; 
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 1, v_buckets_x27_666_);
lean_ctor_set(v___x_645_, 0, v_size_x27_663_);
v___x_678_ = v___x_645_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_size_x27_663_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v_buckets_x27_666_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
else
{
lean_object* v___x_680_; lean_object* v_buckets_x27_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_685_; 
lean_inc(v_bkt_660_);
v___x_680_ = lean_box(0);
v_buckets_x27_681_ = lean_array_uset(v_buckets_643_, v___x_659_, v___x_680_);
v___x_682_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(v_a_640_, v_b_641_, v_bkt_660_);
v___x_683_ = lean_array_uset(v_buckets_x27_681_, v___x_659_, v___x_682_);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 1, v___x_683_);
v___x_685_ = v___x_645_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_size_642_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v___x_683_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg___boxed(lean_object* v_m_688_, lean_object* v_a_689_, lean_object* v_b_690_){
_start:
{
uint32_t v_a_boxed_691_; lean_object* v_res_692_; 
v_a_boxed_691_ = lean_unbox_uint32(v_a_689_);
lean_dec(v_a_689_);
v_res_692_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_m_688_, v_a_boxed_691_, v_b_690_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(lean_object* v_histogram_693_, lean_object* v_index_694_, uint32_t v_val_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(v_histogram_693_, v_val_695_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_697_ = lean_unsigned_to_nat(0u);
v___x_698_ = lean_box(0);
v___x_699_ = lean_unsigned_to_nat(1u);
v___x_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_700_, 0, v_index_694_);
v___x_701_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_701_, 0, v___x_697_);
lean_ctor_set(v___x_701_, 1, v___x_698_);
lean_ctor_set(v___x_701_, 2, v___x_699_);
lean_ctor_set(v___x_701_, 3, v___x_700_);
v___x_702_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_histogram_693_, v_val_695_, v___x_701_);
return v___x_702_;
}
else
{
lean_object* v_val_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_724_; 
v_val_703_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_724_ == 0)
{
v___x_705_ = v___x_696_;
v_isShared_706_ = v_isSharedCheck_724_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_val_703_);
lean_dec(v___x_696_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_724_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v_leftCount_707_; lean_object* v_leftIndex_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_721_; 
v_leftCount_707_ = lean_ctor_get(v_val_703_, 0);
v_leftIndex_708_ = lean_ctor_get(v_val_703_, 1);
v_isSharedCheck_721_ = !lean_is_exclusive(v_val_703_);
if (v_isSharedCheck_721_ == 0)
{
lean_object* v_unused_722_; lean_object* v_unused_723_; 
v_unused_722_ = lean_ctor_get(v_val_703_, 3);
lean_dec(v_unused_722_);
v_unused_723_ = lean_ctor_get(v_val_703_, 2);
lean_dec(v_unused_723_);
v___x_710_ = v_val_703_;
v_isShared_711_ = v_isSharedCheck_721_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_leftIndex_708_);
lean_inc(v_leftCount_707_);
lean_dec(v_val_703_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_721_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_712_ = lean_unsigned_to_nat(1u);
v___x_713_ = lean_nat_add(v_leftCount_707_, v___x_712_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v_index_694_);
v___x_715_ = v___x_705_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_index_694_);
v___x_715_ = v_reuseFailAlloc_720_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_717_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 3, v___x_715_);
lean_ctor_set(v___x_710_, 2, v___x_713_);
v___x_717_ = v___x_710_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_leftCount_707_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v_leftIndex_708_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_719_, 3, v___x_715_);
v___x_717_ = v_reuseFailAlloc_719_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_718_; 
v___x_718_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_histogram_693_, v_val_695_, v___x_717_);
return v___x_718_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg___boxed(lean_object* v_histogram_725_, lean_object* v_index_726_, lean_object* v_val_727_){
_start:
{
uint32_t v_val_boxed_728_; lean_object* v_res_729_; 
v_val_boxed_728_ = lean_unbox_uint32(v_val_727_);
lean_dec(v_val_727_);
v_res_729_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(v_histogram_725_, v_index_726_, v_val_boxed_728_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(lean_object* v_upperBound_730_, lean_object* v___x_731_, lean_object* v_fst_732_, lean_object* v___x_733_, lean_object* v_a_734_, lean_object* v_b_735_){
_start:
{
uint8_t v___x_736_; 
v___x_736_ = lean_nat_dec_lt(v_a_734_, v_upperBound_730_);
if (v___x_736_ == 0)
{
lean_dec(v_a_734_);
return v_b_735_;
}
else
{
lean_object* v___x_737_; uint32_t v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_737_ = l_Subarray_get___redArg(v_fst_732_, v_a_734_);
v___x_738_ = lean_unbox_uint32(v___x_737_);
lean_dec(v___x_737_);
lean_inc(v_a_734_);
v___x_739_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(v_b_735_, v_a_734_, v___x_738_);
v___x_740_ = lean_unsigned_to_nat(1u);
v___x_741_ = lean_nat_add(v_a_734_, v___x_740_);
lean_dec(v_a_734_);
v_a_734_ = v___x_741_;
v_b_735_ = v___x_739_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg___boxed(lean_object* v_upperBound_743_, lean_object* v___x_744_, lean_object* v_fst_745_, lean_object* v___x_746_, lean_object* v_a_747_, lean_object* v_b_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(v_upperBound_743_, v___x_744_, v_fst_745_, v___x_746_, v_a_747_, v_b_748_);
lean_dec(v___x_746_);
lean_dec_ref(v_fst_745_);
lean_dec(v___x_744_);
lean_dec(v_upperBound_743_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg(lean_object* v_as_x27_750_, lean_object* v_b_751_){
_start:
{
if (lean_obj_tag(v_as_x27_750_) == 0)
{
return v_b_751_;
}
else
{
lean_object* v_head_752_; lean_object* v_snd_753_; lean_object* v_leftIndex_754_; 
v_head_752_ = lean_ctor_get(v_as_x27_750_, 0);
v_snd_753_ = lean_ctor_get(v_head_752_, 1);
v_leftIndex_754_ = lean_ctor_get(v_snd_753_, 1);
if (lean_obj_tag(v_leftIndex_754_) == 1)
{
lean_object* v_rightIndex_755_; 
v_rightIndex_755_ = lean_ctor_get(v_snd_753_, 3);
if (lean_obj_tag(v_rightIndex_755_) == 1)
{
if (lean_obj_tag(v_b_751_) == 0)
{
lean_object* v_tail_756_; lean_object* v_fst_757_; lean_object* v_leftCount_758_; lean_object* v_rightCount_759_; lean_object* v_val_760_; lean_object* v_val_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v_tail_756_ = lean_ctor_get(v_as_x27_750_, 1);
v_fst_757_ = lean_ctor_get(v_head_752_, 0);
v_leftCount_758_ = lean_ctor_get(v_snd_753_, 0);
v_rightCount_759_ = lean_ctor_get(v_snd_753_, 2);
v_val_760_ = lean_ctor_get(v_leftIndex_754_, 0);
v_val_761_ = lean_ctor_get(v_rightIndex_755_, 0);
v___x_762_ = lean_nat_add(v_leftCount_758_, v_rightCount_759_);
lean_inc(v_val_761_);
lean_inc(v_val_760_);
v___x_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_763_, 0, v_val_760_);
lean_ctor_set(v___x_763_, 1, v_val_761_);
lean_inc(v_fst_757_);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v_fst_757_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_765_, 0, v___x_762_);
lean_ctor_set(v___x_765_, 1, v___x_764_);
v___x_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
v_as_x27_750_ = v_tail_756_;
v_b_751_ = v___x_766_;
goto _start;
}
else
{
lean_object* v_val_768_; lean_object* v_tail_769_; lean_object* v_fst_770_; lean_object* v_leftCount_771_; lean_object* v_rightCount_772_; lean_object* v_val_773_; lean_object* v_val_774_; lean_object* v_fst_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_796_; 
v_val_768_ = lean_ctor_get(v_b_751_, 0);
lean_inc(v_val_768_);
v_tail_769_ = lean_ctor_get(v_as_x27_750_, 1);
v_fst_770_ = lean_ctor_get(v_head_752_, 0);
v_leftCount_771_ = lean_ctor_get(v_snd_753_, 0);
v_rightCount_772_ = lean_ctor_get(v_snd_753_, 2);
v_val_773_ = lean_ctor_get(v_leftIndex_754_, 0);
v_val_774_ = lean_ctor_get(v_rightIndex_755_, 0);
v_fst_775_ = lean_ctor_get(v_val_768_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v_val_768_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; 
v_unused_797_ = lean_ctor_get(v_val_768_, 1);
lean_dec(v_unused_797_);
v___x_777_ = v_val_768_;
v_isShared_778_ = v_isSharedCheck_796_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_fst_775_);
lean_dec(v_val_768_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_796_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_779_; uint8_t v___x_780_; 
v___x_779_ = lean_nat_add(v_leftCount_771_, v_rightCount_772_);
v___x_780_ = lean_nat_dec_lt(v___x_779_, v_fst_775_);
lean_dec(v_fst_775_);
if (v___x_780_ == 0)
{
lean_dec(v___x_779_);
lean_del_object(v___x_777_);
v_as_x27_750_ = v_tail_769_;
goto _start;
}
else
{
lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_794_; 
v_isSharedCheck_794_ = !lean_is_exclusive(v_b_751_);
if (v_isSharedCheck_794_ == 0)
{
lean_object* v_unused_795_; 
v_unused_795_ = lean_ctor_get(v_b_751_, 0);
lean_dec(v_unused_795_);
v___x_783_ = v_b_751_;
v_isShared_784_ = v_isSharedCheck_794_;
goto v_resetjp_782_;
}
else
{
lean_dec(v_b_751_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_794_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
lean_inc(v_val_774_);
lean_inc(v_val_773_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v_val_774_);
lean_ctor_set(v___x_777_, 0, v_val_773_);
v___x_786_ = v___x_777_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_val_773_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_val_774_);
v___x_786_ = v_reuseFailAlloc_793_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
lean_inc(v_fst_770_);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v_fst_770_);
lean_ctor_set(v___x_787_, 1, v___x_786_);
v___x_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_779_);
lean_ctor_set(v___x_788_, 1, v___x_787_);
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_788_);
v___x_790_ = v___x_783_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_788_);
v___x_790_ = v_reuseFailAlloc_792_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
v_as_x27_750_ = v_tail_769_;
v_b_751_ = v___x_790_;
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
lean_object* v_tail_798_; 
v_tail_798_ = lean_ctor_get(v_as_x27_750_, 1);
v_as_x27_750_ = v_tail_798_;
goto _start;
}
}
else
{
lean_object* v_tail_800_; 
v_tail_800_ = lean_ctor_get(v_as_x27_750_, 1);
v_as_x27_750_ = v_tail_800_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_as_x27_802_, lean_object* v_b_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg(v_as_x27_802_, v_b_803_);
lean_dec(v_as_x27_802_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3_spec__4(lean_object* v_left_805_, lean_object* v_right_806_, lean_object* v_pref_807_){
_start:
{
lean_object* v_start_808_; lean_object* v_stop_809_; lean_object* v_i_810_; lean_object* v___x_816_; uint8_t v___x_817_; 
v_start_808_ = lean_ctor_get(v_left_805_, 1);
v_stop_809_ = lean_ctor_get(v_left_805_, 2);
v_i_810_ = lean_array_get_size(v_pref_807_);
v___x_816_ = lean_nat_sub(v_stop_809_, v_start_808_);
v___x_817_ = lean_nat_dec_lt(v_i_810_, v___x_816_);
lean_dec(v___x_816_);
if (v___x_817_ == 0)
{
goto v___jp_811_;
}
else
{
lean_object* v_start_818_; lean_object* v_stop_819_; lean_object* v___x_820_; uint8_t v___x_821_; 
v_start_818_ = lean_ctor_get(v_right_806_, 1);
v_stop_819_ = lean_ctor_get(v_right_806_, 2);
v___x_820_ = lean_nat_sub(v_stop_819_, v_start_818_);
v___x_821_ = lean_nat_dec_lt(v_i_810_, v___x_820_);
lean_dec(v___x_820_);
if (v___x_821_ == 0)
{
goto v___jp_811_;
}
else
{
lean_object* v___x_822_; lean_object* v___x_823_; uint32_t v___x_824_; uint32_t v___x_825_; uint8_t v___x_826_; 
v___x_822_ = l_Subarray_get___redArg(v_left_805_, v_i_810_);
v___x_823_ = l_Subarray_get___redArg(v_right_806_, v_i_810_);
v___x_824_ = lean_unbox_uint32(v___x_822_);
v___x_825_ = lean_unbox_uint32(v___x_823_);
lean_dec(v___x_823_);
v___x_826_ = lean_uint32_dec_eq(v___x_824_, v___x_825_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
lean_dec(v___x_822_);
v___x_827_ = l_Subarray_drop___redArg(v_left_805_, v_i_810_);
v___x_828_ = l_Subarray_drop___redArg(v_right_806_, v_i_810_);
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v_pref_807_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
return v___x_830_;
}
else
{
lean_object* v___x_831_; 
v___x_831_ = lean_array_push(v_pref_807_, v___x_822_);
v_pref_807_ = v___x_831_;
goto _start;
}
}
}
v___jp_811_:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_812_ = l_Subarray_drop___redArg(v_left_805_, v_i_810_);
v___x_813_ = l_Subarray_drop___redArg(v_right_806_, v_i_810_);
v___x_814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_812_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v_pref_807_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
return v___x_815_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3(lean_object* v_left_833_, lean_object* v_right_834_){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_836_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3_spec__4(v_left_833_, v_right_834_, v___x_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(lean_object* v_a_837_, lean_object* v_b_838_){
_start:
{
lean_object* v_array_839_; lean_object* v_start_840_; lean_object* v_stop_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_854_; 
v_array_839_ = lean_ctor_get(v_a_837_, 0);
v_start_840_ = lean_ctor_get(v_a_837_, 1);
v_stop_841_ = lean_ctor_get(v_a_837_, 2);
v_isSharedCheck_854_ = !lean_is_exclusive(v_a_837_);
if (v_isSharedCheck_854_ == 0)
{
v___x_843_ = v_a_837_;
v_isShared_844_ = v_isSharedCheck_854_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_stop_841_);
lean_inc(v_start_840_);
lean_inc(v_array_839_);
lean_dec(v_a_837_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_854_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
uint8_t v___x_845_; 
v___x_845_ = lean_nat_dec_lt(v_start_840_, v_stop_841_);
if (v___x_845_ == 0)
{
lean_del_object(v___x_843_);
lean_dec(v_stop_841_);
lean_dec(v_start_840_);
lean_dec_ref(v_array_839_);
return v_b_838_;
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_846_ = lean_unsigned_to_nat(1u);
v___x_847_ = lean_nat_add(v_start_840_, v___x_846_);
lean_inc_ref(v_array_839_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 1, v___x_847_);
v___x_849_ = v___x_843_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_array_839_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_853_, 2, v_stop_841_);
v___x_849_ = v_reuseFailAlloc_853_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_array_fget(v_array_839_, v_start_840_);
lean_dec(v_start_840_);
lean_dec_ref(v_array_839_);
v___x_851_ = lean_array_push(v_b_838_, v___x_850_);
v_a_837_ = v___x_849_;
v_b_838_ = v___x_851_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6(lean_object* v_left_855_, lean_object* v_right_856_, lean_object* v_i_857_){
_start:
{
lean_object* v_start_858_; lean_object* v_stop_859_; lean_object* v___x_860_; uint8_t v___x_874_; 
v_start_858_ = lean_ctor_get(v_left_855_, 1);
v_stop_859_ = lean_ctor_get(v_left_855_, 2);
v___x_860_ = lean_nat_sub(v_stop_859_, v_start_858_);
v___x_874_ = lean_nat_dec_lt(v_i_857_, v___x_860_);
if (v___x_874_ == 0)
{
goto v___jp_861_;
}
else
{
lean_object* v_start_875_; lean_object* v_stop_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v_start_875_ = lean_ctor_get(v_right_856_, 1);
v_stop_876_ = lean_ctor_get(v_right_856_, 2);
v___x_877_ = lean_nat_sub(v_stop_876_, v_start_875_);
v___x_878_ = lean_nat_dec_lt(v_i_857_, v___x_877_);
if (v___x_878_ == 0)
{
lean_dec(v___x_877_);
goto v___jp_861_;
}
else
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; uint32_t v___x_886_; uint32_t v___x_887_; uint8_t v___x_888_; 
v___x_879_ = lean_nat_sub(v___x_860_, v_i_857_);
lean_dec(v___x_860_);
v___x_880_ = lean_unsigned_to_nat(1u);
v___x_881_ = lean_nat_sub(v___x_879_, v___x_880_);
v___x_882_ = l_Subarray_get___redArg(v_left_855_, v___x_881_);
lean_dec(v___x_881_);
v___x_883_ = lean_nat_sub(v___x_877_, v_i_857_);
lean_dec(v___x_877_);
v___x_884_ = lean_nat_sub(v___x_883_, v___x_880_);
v___x_885_ = l_Subarray_get___redArg(v_right_856_, v___x_884_);
lean_dec(v___x_884_);
v___x_886_ = lean_unbox_uint32(v___x_882_);
lean_dec(v___x_882_);
v___x_887_ = lean_unbox_uint32(v___x_885_);
lean_dec(v___x_885_);
v___x_888_ = lean_uint32_dec_eq(v___x_886_, v___x_887_);
if (v___x_888_ == 0)
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
lean_dec(v_i_857_);
lean_inc_ref(v_left_855_);
v___x_889_ = l_Subarray_take___redArg(v_left_855_, v___x_879_);
v___x_890_ = l_Subarray_take___redArg(v_right_856_, v___x_883_);
lean_dec(v___x_883_);
v___x_891_ = l_Subarray_drop___redArg(v_left_855_, v___x_879_);
lean_dec(v___x_879_);
v___x_892_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_893_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(v___x_891_, v___x_892_);
v___x_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_894_, 0, v___x_890_);
lean_ctor_set(v___x_894_, 1, v___x_893_);
v___x_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_895_, 0, v___x_889_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
return v___x_895_;
}
else
{
lean_object* v___x_896_; 
lean_dec(v___x_883_);
lean_dec(v___x_879_);
v___x_896_ = lean_nat_add(v_i_857_, v___x_880_);
lean_dec(v_i_857_);
v_i_857_ = v___x_896_;
goto _start;
}
}
}
v___jp_861_:
{
lean_object* v_start_862_; lean_object* v_stop_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v_start_862_ = lean_ctor_get(v_right_856_, 1);
v_stop_863_ = lean_ctor_get(v_right_856_, 2);
v___x_864_ = lean_nat_sub(v___x_860_, v_i_857_);
lean_dec(v___x_860_);
lean_inc_ref(v_left_855_);
v___x_865_ = l_Subarray_take___redArg(v_left_855_, v___x_864_);
v___x_866_ = lean_nat_sub(v_stop_863_, v_start_862_);
v___x_867_ = lean_nat_sub(v___x_866_, v_i_857_);
lean_dec(v_i_857_);
lean_dec(v___x_866_);
v___x_868_ = l_Subarray_take___redArg(v_right_856_, v___x_867_);
lean_dec(v___x_867_);
v___x_869_ = l_Subarray_drop___redArg(v_left_855_, v___x_864_);
lean_dec(v___x_864_);
v___x_870_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_871_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(v___x_869_, v___x_870_);
v___x_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_868_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_865_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
return v___x_873_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4(lean_object* v_left_898_, lean_object* v_right_899_){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_900_ = lean_unsigned_to_nat(0u);
v___x_901_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6(v_left_898_, v_right_899_, v___x_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(lean_object* v_x_902_, lean_object* v_x_903_){
_start:
{
if (lean_obj_tag(v_x_903_) == 0)
{
lean_inc(v_x_902_);
return v_x_902_;
}
else
{
lean_object* v_key_904_; lean_object* v_value_905_; lean_object* v_tail_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v_key_904_ = lean_ctor_get(v_x_903_, 0);
v_value_905_ = lean_ctor_get(v_x_903_, 1);
v_tail_906_ = lean_ctor_get(v_x_903_, 2);
v___x_907_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(v_x_902_, v_tail_906_);
lean_inc(v_value_905_);
lean_inc(v_key_904_);
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v_key_904_);
lean_ctor_set(v___x_908_, 1, v_value_905_);
v___x_909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
lean_ctor_set(v___x_909_, 1, v___x_907_);
return v___x_909_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6___boxed(lean_object* v_x_910_, lean_object* v_x_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(v_x_910_, v_x_911_);
lean_dec(v_x_911_);
lean_dec(v_x_910_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7(lean_object* v_as_913_, size_t v_i_914_, size_t v_stop_915_, lean_object* v_b_916_){
_start:
{
uint8_t v___x_917_; 
v___x_917_ = lean_usize_dec_eq(v_i_914_, v_stop_915_);
if (v___x_917_ == 0)
{
size_t v___x_918_; size_t v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_918_ = ((size_t)1ULL);
v___x_919_ = lean_usize_sub(v_i_914_, v___x_918_);
v___x_920_ = lean_array_uget_borrowed(v_as_913_, v___x_919_);
v___x_921_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(v_b_916_, v___x_920_);
lean_dec(v_b_916_);
v_i_914_ = v___x_919_;
v_b_916_ = v___x_921_;
goto _start;
}
else
{
return v_b_916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7___boxed(lean_object* v_as_923_, lean_object* v_i_924_, lean_object* v_stop_925_, lean_object* v_b_926_){
_start:
{
size_t v_i_boxed_927_; size_t v_stop_boxed_928_; lean_object* v_res_929_; 
v_i_boxed_927_ = lean_unbox_usize(v_i_924_);
lean_dec(v_i_924_);
v_stop_boxed_928_ = lean_unbox_usize(v_stop_925_);
lean_dec(v_stop_925_);
v_res_929_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7(v_as_923_, v_i_boxed_927_, v_stop_boxed_928_, v_b_926_);
lean_dec_ref(v_as_923_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(lean_object* v_histogram_930_, lean_object* v_index_931_, uint32_t v_val_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(v_histogram_930_, v_val_932_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_934_ = lean_unsigned_to_nat(1u);
v___x_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_935_, 0, v_index_931_);
v___x_936_ = lean_unsigned_to_nat(0u);
v___x_937_ = lean_box(0);
v___x_938_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_938_, 0, v___x_934_);
lean_ctor_set(v___x_938_, 1, v___x_935_);
lean_ctor_set(v___x_938_, 2, v___x_936_);
lean_ctor_set(v___x_938_, 3, v___x_937_);
v___x_939_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_histogram_930_, v_val_932_, v___x_938_);
return v___x_939_;
}
else
{
lean_object* v_val_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_961_; 
v_val_940_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_961_ == 0)
{
v___x_942_ = v___x_933_;
v_isShared_943_ = v_isSharedCheck_961_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_val_940_);
lean_dec(v___x_933_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_961_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v_leftCount_944_; lean_object* v_rightCount_945_; lean_object* v_rightIndex_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_959_; 
v_leftCount_944_ = lean_ctor_get(v_val_940_, 0);
v_rightCount_945_ = lean_ctor_get(v_val_940_, 2);
v_rightIndex_946_ = lean_ctor_get(v_val_940_, 3);
v_isSharedCheck_959_ = !lean_is_exclusive(v_val_940_);
if (v_isSharedCheck_959_ == 0)
{
lean_object* v_unused_960_; 
v_unused_960_ = lean_ctor_get(v_val_940_, 1);
lean_dec(v_unused_960_);
v___x_948_ = v_val_940_;
v_isShared_949_ = v_isSharedCheck_959_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_rightIndex_946_);
lean_inc(v_rightCount_945_);
lean_inc(v_leftCount_944_);
lean_dec(v_val_940_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_959_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_950_ = lean_unsigned_to_nat(1u);
v___x_951_ = lean_nat_add(v_leftCount_944_, v___x_950_);
lean_dec(v_leftCount_944_);
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 0, v_index_931_);
v___x_953_ = v___x_942_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_index_931_);
v___x_953_ = v_reuseFailAlloc_958_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
lean_object* v___x_955_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 1, v___x_953_);
lean_ctor_set(v___x_948_, 0, v___x_951_);
v___x_955_ = v___x_948_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_951_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v___x_953_);
lean_ctor_set(v_reuseFailAlloc_957_, 2, v_rightCount_945_);
lean_ctor_set(v_reuseFailAlloc_957_, 3, v_rightIndex_946_);
v___x_955_ = v_reuseFailAlloc_957_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_956_; 
v___x_956_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_histogram_930_, v_val_932_, v___x_955_);
return v___x_956_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg___boxed(lean_object* v_histogram_962_, lean_object* v_index_963_, lean_object* v_val_964_){
_start:
{
uint32_t v_val_boxed_965_; lean_object* v_res_966_; 
v_val_boxed_965_ = lean_unbox_uint32(v_val_964_);
lean_dec(v_val_964_);
v_res_966_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(v_histogram_962_, v_index_963_, v_val_boxed_965_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg(lean_object* v_upperBound_967_, lean_object* v_fst_968_, lean_object* v___x_969_, lean_object* v_fst_970_, lean_object* v_a_971_, lean_object* v_b_972_){
_start:
{
uint8_t v___x_973_; 
v___x_973_ = lean_nat_dec_lt(v_a_971_, v_upperBound_967_);
if (v___x_973_ == 0)
{
lean_dec(v_a_971_);
return v_b_972_;
}
else
{
lean_object* v___x_974_; uint32_t v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_974_ = l_Subarray_get___redArg(v_fst_970_, v_a_971_);
v___x_975_ = lean_unbox_uint32(v___x_974_);
lean_dec(v___x_974_);
lean_inc(v_a_971_);
v___x_976_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(v_b_972_, v_a_971_, v___x_975_);
v___x_977_ = lean_unsigned_to_nat(1u);
v___x_978_ = lean_nat_add(v_a_971_, v___x_977_);
lean_dec(v_a_971_);
v_a_971_ = v___x_978_;
v_b_972_ = v___x_976_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg___boxed(lean_object* v_upperBound_980_, lean_object* v_fst_981_, lean_object* v___x_982_, lean_object* v_fst_983_, lean_object* v_a_984_, lean_object* v_b_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg(v_upperBound_980_, v_fst_981_, v___x_982_, v_fst_983_, v_a_984_, v_b_985_);
lean_dec_ref(v_fst_983_);
lean_dec(v___x_982_);
lean_dec_ref(v_fst_981_);
lean_dec(v_upperBound_980_);
return v_res_986_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_987_ = lean_box(0);
v___x_988_ = lean_unsigned_to_nat(16u);
v___x_989_ = lean_mk_array(v___x_988_, v___x_987_);
return v___x_989_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v_hist_992_; 
v___x_990_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0);
v___x_991_ = lean_unsigned_to_nat(0u);
v_hist_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_992_, 0, v___x_991_);
lean_ctor_set(v_hist_992_, 1, v___x_990_);
return v_hist_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(lean_object* v_left_993_, lean_object* v_right_994_){
_start:
{
lean_object* v___x_995_; lean_object* v_snd_996_; lean_object* v_fst_997_; lean_object* v_fst_998_; lean_object* v_snd_999_; lean_object* v___x_1000_; lean_object* v_snd_1001_; lean_object* v_fst_1002_; lean_object* v_fst_1003_; lean_object* v_snd_1004_; lean_object* v_start_1005_; lean_object* v_stop_1006_; lean_object* v___x_1007_; lean_object* v_hist_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v_start_1011_; lean_object* v_stop_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v_buckets_1015_; lean_object* v___x_1016_; lean_object* v___y_1018_; lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v___x_995_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3(v_left_993_, v_right_994_);
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
v___x_1000_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4(v_fst_998_, v_snd_999_);
v_snd_1001_ = lean_ctor_get(v___x_1000_, 1);
lean_inc(v_snd_1001_);
v_fst_1002_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_fst_1002_);
lean_dec_ref(v___x_1000_);
v_fst_1003_ = lean_ctor_get(v_snd_1001_, 0);
lean_inc(v_fst_1003_);
v_snd_1004_ = lean_ctor_get(v_snd_1001_, 1);
lean_inc(v_snd_1004_);
lean_dec(v_snd_1001_);
v_start_1005_ = lean_ctor_get(v_fst_1002_, 1);
v_stop_1006_ = lean_ctor_get(v_fst_1002_, 2);
v___x_1007_ = lean_unsigned_to_nat(0u);
v_hist_1008_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1);
v___x_1009_ = lean_nat_sub(v_stop_1006_, v_start_1005_);
v___x_1010_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg(v___x_1009_, v_fst_1003_, v___x_1009_, v_fst_1002_, v___x_1007_, v_hist_1008_);
v_start_1011_ = lean_ctor_get(v_fst_1003_, 1);
v_stop_1012_ = lean_ctor_get(v_fst_1003_, 2);
v___x_1013_ = lean_nat_sub(v_stop_1012_, v_start_1011_);
v___x_1014_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(v___x_1013_, v___x_1013_, v_fst_1003_, v___x_1009_, v___x_1007_, v___x_1010_);
lean_dec(v___x_1009_);
lean_dec(v___x_1013_);
v_buckets_1015_ = lean_ctor_get(v___x_1014_, 1);
lean_inc_ref(v_buckets_1015_);
lean_dec_ref(v___x_1014_);
v___x_1016_ = lean_box(0);
v___x_1044_ = lean_box(0);
v___x_1045_ = lean_array_get_size(v_buckets_1015_);
v___x_1046_ = lean_nat_dec_lt(v___x_1007_, v___x_1045_);
if (v___x_1046_ == 0)
{
lean_dec_ref(v_buckets_1015_);
v___y_1018_ = v___x_1044_;
goto v___jp_1017_;
}
else
{
size_t v___x_1047_; size_t v___x_1048_; lean_object* v___x_1049_; 
v___x_1047_ = lean_usize_of_nat(v___x_1045_);
v___x_1048_ = ((size_t)0ULL);
v___x_1049_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7(v_buckets_1015_, v___x_1047_, v___x_1048_, v___x_1044_);
lean_dec_ref(v_buckets_1015_);
v___y_1018_ = v___x_1049_;
goto v___jp_1017_;
}
v___jp_1017_:
{
lean_object* v___x_1019_; 
v___x_1019_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg(v___y_1018_, v___x_1016_);
lean_dec(v___y_1018_);
if (lean_obj_tag(v___x_1019_) == 1)
{
lean_object* v_val_1020_; lean_object* v_snd_1021_; lean_object* v_snd_1022_; lean_object* v_fst_1023_; lean_object* v_fst_1024_; lean_object* v_snd_1025_; lean_object* v___x_1026_; lean_object* v_fst_1027_; lean_object* v_snd_1028_; lean_object* v___x_1029_; lean_object* v_fst_1030_; lean_object* v_snd_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v_val_1020_ = lean_ctor_get(v___x_1019_, 0);
lean_inc(v_val_1020_);
lean_dec_ref_known(v___x_1019_, 1);
v_snd_1021_ = lean_ctor_get(v_val_1020_, 1);
lean_inc(v_snd_1021_);
lean_dec(v_val_1020_);
v_snd_1022_ = lean_ctor_get(v_snd_1021_, 1);
lean_inc(v_snd_1022_);
v_fst_1023_ = lean_ctor_get(v_snd_1021_, 0);
lean_inc(v_fst_1023_);
lean_dec(v_snd_1021_);
v_fst_1024_ = lean_ctor_get(v_snd_1022_, 0);
lean_inc(v_fst_1024_);
v_snd_1025_ = lean_ctor_get(v_snd_1022_, 1);
lean_inc(v_snd_1025_);
lean_dec(v_snd_1022_);
v___x_1026_ = l_Subarray_split___redArg(v_fst_1002_, v_fst_1024_);
lean_dec(v_fst_1024_);
v_fst_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_fst_1027_);
v_snd_1028_ = lean_ctor_get(v___x_1026_, 1);
lean_inc(v_snd_1028_);
lean_dec_ref(v___x_1026_);
v___x_1029_ = l_Subarray_split___redArg(v_fst_1003_, v_snd_1025_);
lean_dec(v_snd_1025_);
v_fst_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc(v_fst_1030_);
v_snd_1031_ = lean_ctor_get(v___x_1029_, 1);
lean_inc(v_snd_1031_);
lean_dec_ref(v___x_1029_);
v___x_1032_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v_fst_1027_, v_fst_1030_);
v___x_1033_ = l_Array_append___redArg(v_fst_997_, v___x_1032_);
lean_dec_ref(v___x_1032_);
v___x_1034_ = lean_unsigned_to_nat(1u);
v___x_1035_ = lean_mk_empty_array_with_capacity(v___x_1034_);
v___x_1036_ = lean_array_push(v___x_1035_, v_fst_1023_);
v___x_1037_ = l_Array_append___redArg(v___x_1033_, v___x_1036_);
lean_dec_ref(v___x_1036_);
v___x_1038_ = l_Subarray_drop___redArg(v_snd_1028_, v___x_1034_);
v___x_1039_ = l_Subarray_drop___redArg(v_snd_1031_, v___x_1034_);
v___x_1040_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v___x_1038_, v___x_1039_);
v___x_1041_ = l_Array_append___redArg(v___x_1037_, v___x_1040_);
lean_dec_ref(v___x_1040_);
v___x_1042_ = l_Array_append___redArg(v___x_1041_, v_snd_1004_);
lean_dec(v_snd_1004_);
return v___x_1042_;
}
else
{
lean_object* v___x_1043_; 
lean_dec(v___x_1019_);
lean_dec(v_fst_1003_);
lean_dec(v_fst_1002_);
v___x_1043_ = l_Array_append___redArg(v_fst_997_, v_snd_1004_);
lean_dec(v_snd_1004_);
return v___x_1043_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(lean_object* v___x_1050_, lean_object* v_edited_1051_, lean_object* v_a_1052_){
_start:
{
lean_object* v_fst_1053_; lean_object* v_snd_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1073_; 
v_fst_1053_ = lean_ctor_get(v_a_1052_, 0);
v_snd_1054_ = lean_ctor_get(v_a_1052_, 1);
v_isSharedCheck_1073_ = !lean_is_exclusive(v_a_1052_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1056_ = v_a_1052_;
v_isShared_1057_ = v_isSharedCheck_1073_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_snd_1054_);
lean_inc(v_fst_1053_);
lean_dec(v_a_1052_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1073_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
uint8_t v___x_1058_; 
v___x_1058_ = lean_nat_dec_lt(v_snd_1054_, v___x_1050_);
if (v___x_1058_ == 0)
{
lean_object* v___x_1060_; 
if (v_isShared_1057_ == 0)
{
v___x_1060_ = v___x_1056_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_fst_1053_);
lean_ctor_set(v_reuseFailAlloc_1061_, 1, v_snd_1054_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
else
{
uint8_t v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1066_; 
v___x_1062_ = 0;
v___x_1063_ = lean_array_fget_borrowed(v_edited_1051_, v_snd_1054_);
v___x_1064_ = lean_box(v___x_1062_);
lean_inc(v___x_1063_);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 1, v___x_1063_);
lean_ctor_set(v___x_1056_, 0, v___x_1064_);
v___x_1066_ = v___x_1056_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v___x_1064_);
lean_ctor_set(v_reuseFailAlloc_1072_, 1, v___x_1063_);
v___x_1066_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1067_ = lean_array_push(v_fst_1053_, v___x_1066_);
v___x_1068_ = lean_unsigned_to_nat(1u);
v___x_1069_ = lean_nat_add(v_snd_1054_, v___x_1068_);
lean_dec(v_snd_1054_);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1067_);
lean_ctor_set(v___x_1070_, 1, v___x_1069_);
v_a_1052_ = v___x_1070_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg___boxed(lean_object* v___x_1074_, lean_object* v_edited_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1074_, v_edited_1075_, v_a_1076_);
lean_dec_ref(v_edited_1075_);
lean_dec(v___x_1074_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(size_t v_sz_1078_, size_t v_i_1079_, lean_object* v_bs_1080_){
_start:
{
uint8_t v___x_1081_; 
v___x_1081_ = lean_usize_dec_lt(v_i_1079_, v_sz_1078_);
if (v___x_1081_ == 0)
{
return v_bs_1080_;
}
else
{
lean_object* v_v_1082_; lean_object* v___x_1083_; lean_object* v_bs_x27_1084_; uint8_t v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; size_t v___x_1088_; size_t v___x_1089_; lean_object* v___x_1090_; 
v_v_1082_ = lean_array_uget(v_bs_1080_, v_i_1079_);
v___x_1083_ = lean_unsigned_to_nat(0u);
v_bs_x27_1084_ = lean_array_uset(v_bs_1080_, v_i_1079_, v___x_1083_);
v___x_1085_ = 1;
v___x_1086_ = lean_box(v___x_1085_);
v___x_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
lean_ctor_set(v___x_1087_, 1, v_v_1082_);
v___x_1088_ = ((size_t)1ULL);
v___x_1089_ = lean_usize_add(v_i_1079_, v___x_1088_);
v___x_1090_ = lean_array_uset(v_bs_x27_1084_, v_i_1079_, v___x_1087_);
v_i_1079_ = v___x_1089_;
v_bs_1080_ = v___x_1090_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8___boxed(lean_object* v_sz_1092_, lean_object* v_i_1093_, lean_object* v_bs_1094_){
_start:
{
size_t v_sz_boxed_1095_; size_t v_i_boxed_1096_; lean_object* v_res_1097_; 
v_sz_boxed_1095_ = lean_unbox_usize(v_sz_1092_);
lean_dec(v_sz_1092_);
v_i_boxed_1096_ = lean_unbox_usize(v_i_1093_);
lean_dec(v_i_1093_);
v_res_1097_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(v_sz_boxed_1095_, v_i_boxed_1096_, v_bs_1094_);
return v_res_1097_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = 65;
v___x_1099_ = lean_box_uint32(v___x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg(lean_object* v_edited_1100_, lean_object* v___x_1101_, uint32_t v_a_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v_fst_1104_; lean_object* v_snd_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1132_; 
v_fst_1104_ = lean_ctor_get(v_a_1103_, 0);
v_snd_1105_ = lean_ctor_get(v_a_1103_, 1);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_a_1103_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1107_ = v_a_1103_;
v_isShared_1108_ = v_isSharedCheck_1132_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_snd_1105_);
lean_inc(v_fst_1104_);
lean_dec(v_a_1103_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1132_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
uint8_t v___y_1110_; uint8_t v___x_1126_; 
v___x_1126_ = lean_nat_dec_lt(v_snd_1105_, v___x_1101_);
if (v___x_1126_ == 0)
{
v___y_1110_ = v___x_1126_;
goto v___jp_1109_;
}
else
{
lean_object* v___x_1127_; lean_object* v___x_1128_; uint32_t v___x_1129_; uint8_t v___x_1130_; 
v___x_1127_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1;
v___x_1128_ = lean_array_get_borrowed(v___x_1127_, v_edited_1100_, v_snd_1105_);
v___x_1129_ = lean_unbox_uint32(v___x_1128_);
v___x_1130_ = lean_uint32_dec_eq(v___x_1129_, v_a_1102_);
if (v___x_1130_ == 0)
{
v___y_1110_ = v___x_1126_;
goto v___jp_1109_;
}
else
{
lean_object* v___x_1131_; 
lean_del_object(v___x_1107_);
v___x_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1131_, 0, v_fst_1104_);
lean_ctor_set(v___x_1131_, 1, v_snd_1105_);
return v___x_1131_;
}
}
v___jp_1109_:
{
if (v___y_1110_ == 0)
{
lean_object* v___x_1112_; 
if (v_isShared_1108_ == 0)
{
v___x_1112_ = v___x_1107_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_fst_1104_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_snd_1105_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
else
{
uint8_t v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1119_; 
v___x_1114_ = 0;
v___x_1115_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1;
v___x_1116_ = lean_array_get_borrowed(v___x_1115_, v_edited_1100_, v_snd_1105_);
v___x_1117_ = lean_box(v___x_1114_);
lean_inc(v___x_1116_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 1, v___x_1116_);
lean_ctor_set(v___x_1107_, 0, v___x_1117_);
v___x_1119_ = v___x_1107_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v___x_1116_);
v___x_1119_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1120_ = lean_array_push(v_fst_1104_, v___x_1119_);
v___x_1121_ = lean_unsigned_to_nat(1u);
v___x_1122_ = lean_nat_add(v_snd_1105_, v___x_1121_);
lean_dec(v_snd_1105_);
v___x_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1120_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
v_a_1103_ = v___x_1123_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed(lean_object* v_edited_1133_, lean_object* v___x_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
uint32_t v_a_boxed_1137_; lean_object* v_res_1138_; 
v_a_boxed_1137_ = lean_unbox_uint32(v_a_1135_);
lean_dec(v_a_1135_);
v_res_1138_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg(v_edited_1133_, v___x_1134_, v_a_boxed_1137_, v_a_1136_);
lean_dec(v___x_1134_);
lean_dec_ref(v_edited_1133_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(lean_object* v_original_1139_, lean_object* v___x_1140_, uint32_t v_a_1141_, lean_object* v_a_1142_){
_start:
{
lean_object* v_fst_1143_; lean_object* v_snd_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1171_; 
v_fst_1143_ = lean_ctor_get(v_a_1142_, 0);
v_snd_1144_ = lean_ctor_get(v_a_1142_, 1);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_a_1142_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1146_ = v_a_1142_;
v_isShared_1147_ = v_isSharedCheck_1171_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_snd_1144_);
lean_inc(v_fst_1143_);
lean_dec(v_a_1142_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1171_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
uint8_t v___y_1149_; uint8_t v___x_1165_; 
v___x_1165_ = lean_nat_dec_lt(v_snd_1144_, v___x_1140_);
if (v___x_1165_ == 0)
{
v___y_1149_ = v___x_1165_;
goto v___jp_1148_;
}
else
{
lean_object* v___x_1166_; lean_object* v___x_1167_; uint32_t v___x_1168_; uint8_t v___x_1169_; 
v___x_1166_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1;
v___x_1167_ = lean_array_get_borrowed(v___x_1166_, v_original_1139_, v_snd_1144_);
v___x_1168_ = lean_unbox_uint32(v___x_1167_);
v___x_1169_ = lean_uint32_dec_eq(v___x_1168_, v_a_1141_);
if (v___x_1169_ == 0)
{
v___y_1149_ = v___x_1165_;
goto v___jp_1148_;
}
else
{
lean_object* v___x_1170_; 
lean_del_object(v___x_1146_);
v___x_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1170_, 0, v_fst_1143_);
lean_ctor_set(v___x_1170_, 1, v_snd_1144_);
return v___x_1170_;
}
}
v___jp_1148_:
{
if (v___y_1149_ == 0)
{
lean_object* v___x_1151_; 
if (v_isShared_1147_ == 0)
{
v___x_1151_ = v___x_1146_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v_fst_1143_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_snd_1144_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
else
{
uint8_t v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1158_; 
v___x_1153_ = 1;
v___x_1154_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1;
v___x_1155_ = lean_array_get_borrowed(v___x_1154_, v_original_1139_, v_snd_1144_);
v___x_1156_ = lean_box(v___x_1153_);
lean_inc(v___x_1155_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 1, v___x_1155_);
lean_ctor_set(v___x_1146_, 0, v___x_1156_);
v___x_1158_ = v___x_1146_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v___x_1155_);
v___x_1158_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1159_ = lean_array_push(v_fst_1143_, v___x_1158_);
v___x_1160_ = lean_unsigned_to_nat(1u);
v___x_1161_ = lean_nat_add(v_snd_1144_, v___x_1160_);
lean_dec(v_snd_1144_);
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1159_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
v_a_1142_ = v___x_1162_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg___boxed(lean_object* v_original_1172_, lean_object* v___x_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
uint32_t v_a_boxed_1176_; lean_object* v_res_1177_; 
v_a_boxed_1176_ = lean_unbox_uint32(v_a_1174_);
lean_dec(v_a_1174_);
v_res_1177_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v_original_1172_, v___x_1173_, v_a_boxed_1176_, v_a_1175_);
lean_dec(v___x_1173_);
lean_dec_ref(v_original_1172_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(lean_object* v_original_1178_, lean_object* v___x_1179_, lean_object* v_edited_1180_, lean_object* v___x_1181_, lean_object* v_as_1182_, size_t v_sz_1183_, size_t v_i_1184_, lean_object* v_b_1185_){
_start:
{
uint8_t v___x_1186_; 
v___x_1186_ = lean_usize_dec_lt(v_i_1184_, v_sz_1183_);
if (v___x_1186_ == 0)
{
return v_b_1185_;
}
else
{
lean_object* v_snd_1187_; lean_object* v_fst_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1237_; 
v_snd_1187_ = lean_ctor_get(v_b_1185_, 1);
v_fst_1188_ = lean_ctor_get(v_b_1185_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_b_1185_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1190_ = v_b_1185_;
v_isShared_1191_ = v_isSharedCheck_1237_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_snd_1187_);
lean_inc(v_fst_1188_);
lean_dec(v_b_1185_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1237_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v_fst_1192_; lean_object* v_snd_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1236_; 
v_fst_1192_ = lean_ctor_get(v_snd_1187_, 0);
v_snd_1193_ = lean_ctor_get(v_snd_1187_, 1);
v_isSharedCheck_1236_ = !lean_is_exclusive(v_snd_1187_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1195_ = v_snd_1187_;
v_isShared_1196_ = v_isSharedCheck_1236_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_snd_1193_);
lean_inc(v_fst_1192_);
lean_dec(v_snd_1187_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1236_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v_a_1197_; lean_object* v___x_1199_; 
v_a_1197_ = lean_array_uget_borrowed(v_as_1182_, v_i_1184_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 1, v_fst_1192_);
lean_ctor_set(v___x_1195_, 0, v_fst_1188_);
v___x_1199_ = v___x_1195_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_fst_1188_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_fst_1192_);
v___x_1199_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
uint32_t v___x_1200_; lean_object* v___x_1201_; lean_object* v_fst_1202_; lean_object* v_snd_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1234_; 
v___x_1200_ = lean_unbox_uint32(v_a_1197_);
v___x_1201_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v_original_1178_, v___x_1179_, v___x_1200_, v___x_1199_);
v_fst_1202_ = lean_ctor_get(v___x_1201_, 0);
v_snd_1203_ = lean_ctor_get(v___x_1201_, 1);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1205_ = v___x_1201_;
v_isShared_1206_ = v_isSharedCheck_1234_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_snd_1203_);
lean_inc(v_fst_1202_);
lean_dec(v___x_1201_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1234_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 1, v_snd_1193_);
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_fst_1202_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_snd_1193_);
v___x_1208_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
uint32_t v___x_1209_; lean_object* v___x_1210_; lean_object* v_fst_1211_; lean_object* v_snd_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1232_; 
v___x_1209_ = lean_unbox_uint32(v_a_1197_);
v___x_1210_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg(v_edited_1180_, v___x_1181_, v___x_1209_, v___x_1208_);
v_fst_1211_ = lean_ctor_get(v___x_1210_, 0);
v_snd_1212_ = lean_ctor_get(v___x_1210_, 1);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1214_ = v___x_1210_;
v_isShared_1215_ = v_isSharedCheck_1232_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_snd_1212_);
lean_inc(v_fst_1211_);
lean_dec(v___x_1210_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1232_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
uint8_t v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1216_ = 2;
v___x_1217_ = lean_box(v___x_1216_);
lean_inc(v_a_1197_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 1, v_a_1197_);
lean_ctor_set(v___x_1214_, 0, v___x_1217_);
v___x_1219_ = v___x_1214_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v_a_1197_);
v___x_1219_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1225_; 
v___x_1220_ = lean_array_push(v_fst_1211_, v___x_1219_);
v___x_1221_ = lean_unsigned_to_nat(1u);
v___x_1222_ = lean_nat_add(v_snd_1203_, v___x_1221_);
lean_dec(v_snd_1203_);
v___x_1223_ = lean_nat_add(v_snd_1212_, v___x_1221_);
lean_dec(v_snd_1212_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 1, v___x_1223_);
lean_ctor_set(v___x_1190_, 0, v___x_1222_);
v___x_1225_ = v___x_1190_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1222_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v___x_1223_);
v___x_1225_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1226_; size_t v___x_1227_; size_t v___x_1228_; 
v___x_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1220_);
lean_ctor_set(v___x_1226_, 1, v___x_1225_);
v___x_1227_ = ((size_t)1ULL);
v___x_1228_ = lean_usize_add(v_i_1184_, v___x_1227_);
v_i_1184_ = v___x_1228_;
v_b_1185_ = v___x_1226_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15___boxed(lean_object* v_original_1238_, lean_object* v___x_1239_, lean_object* v_edited_1240_, lean_object* v___x_1241_, lean_object* v_as_1242_, lean_object* v_sz_1243_, lean_object* v_i_1244_, lean_object* v_b_1245_){
_start:
{
size_t v_sz_boxed_1246_; size_t v_i_boxed_1247_; lean_object* v_res_1248_; 
v_sz_boxed_1246_ = lean_unbox_usize(v_sz_1243_);
lean_dec(v_sz_1243_);
v_i_boxed_1247_ = lean_unbox_usize(v_i_1244_);
lean_dec(v_i_1244_);
v_res_1248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(v_original_1238_, v___x_1239_, v_edited_1240_, v___x_1241_, v_as_1242_, v_sz_boxed_1246_, v_i_boxed_1247_, v_b_1245_);
lean_dec_ref(v_as_1242_);
lean_dec(v___x_1241_);
lean_dec_ref(v_edited_1240_);
lean_dec(v___x_1239_);
lean_dec_ref(v_original_1238_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(lean_object* v_edited_1249_, lean_object* v___x_1250_, lean_object* v_original_1251_, lean_object* v___x_1252_, lean_object* v_as_1253_, size_t v_sz_1254_, size_t v_i_1255_, lean_object* v_b_1256_){
_start:
{
uint8_t v___x_1257_; 
v___x_1257_ = lean_usize_dec_lt(v_i_1255_, v_sz_1254_);
if (v___x_1257_ == 0)
{
return v_b_1256_;
}
else
{
lean_object* v_snd_1258_; lean_object* v_fst_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1308_; 
v_snd_1258_ = lean_ctor_get(v_b_1256_, 1);
v_fst_1259_ = lean_ctor_get(v_b_1256_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v_b_1256_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1261_ = v_b_1256_;
v_isShared_1262_ = v_isSharedCheck_1308_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_snd_1258_);
lean_inc(v_fst_1259_);
lean_dec(v_b_1256_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1308_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v_fst_1263_; lean_object* v_snd_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1307_; 
v_fst_1263_ = lean_ctor_get(v_snd_1258_, 0);
v_snd_1264_ = lean_ctor_get(v_snd_1258_, 1);
v_isSharedCheck_1307_ = !lean_is_exclusive(v_snd_1258_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1266_ = v_snd_1258_;
v_isShared_1267_ = v_isSharedCheck_1307_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_snd_1264_);
lean_inc(v_fst_1263_);
lean_dec(v_snd_1258_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1307_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v_a_1268_; lean_object* v___x_1270_; 
v_a_1268_ = lean_array_uget_borrowed(v_as_1253_, v_i_1255_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v_fst_1263_);
lean_ctor_set(v___x_1266_, 0, v_fst_1259_);
v___x_1270_ = v___x_1266_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_fst_1259_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_fst_1263_);
v___x_1270_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
uint32_t v___x_1271_; lean_object* v___x_1272_; lean_object* v_fst_1273_; lean_object* v_snd_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1305_; 
v___x_1271_ = lean_unbox_uint32(v_a_1268_);
v___x_1272_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v_original_1251_, v___x_1252_, v___x_1271_, v___x_1270_);
v_fst_1273_ = lean_ctor_get(v___x_1272_, 0);
v_snd_1274_ = lean_ctor_get(v___x_1272_, 1);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1276_ = v___x_1272_;
v_isShared_1277_ = v_isSharedCheck_1305_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_snd_1274_);
lean_inc(v_fst_1273_);
lean_dec(v___x_1272_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1305_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1279_; 
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 1, v_snd_1264_);
v___x_1279_ = v___x_1276_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_fst_1273_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v_snd_1264_);
v___x_1279_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
uint32_t v___x_1280_; lean_object* v___x_1281_; lean_object* v_fst_1282_; lean_object* v_snd_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1303_; 
v___x_1280_ = lean_unbox_uint32(v_a_1268_);
v___x_1281_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg(v_edited_1249_, v___x_1250_, v___x_1280_, v___x_1279_);
v_fst_1282_ = lean_ctor_get(v___x_1281_, 0);
v_snd_1283_ = lean_ctor_get(v___x_1281_, 1);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1281_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1285_ = v___x_1281_;
v_isShared_1286_ = v_isSharedCheck_1303_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_snd_1283_);
lean_inc(v_fst_1282_);
lean_dec(v___x_1281_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1303_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
uint8_t v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1290_; 
v___x_1287_ = 2;
v___x_1288_ = lean_box(v___x_1287_);
lean_inc(v_a_1268_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v_a_1268_);
lean_ctor_set(v___x_1285_, 0, v___x_1288_);
v___x_1290_ = v___x_1285_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1288_);
lean_ctor_set(v_reuseFailAlloc_1302_, 1, v_a_1268_);
v___x_1290_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1296_; 
v___x_1291_ = lean_array_push(v_fst_1282_, v___x_1290_);
v___x_1292_ = lean_unsigned_to_nat(1u);
v___x_1293_ = lean_nat_add(v_snd_1274_, v___x_1292_);
lean_dec(v_snd_1274_);
v___x_1294_ = lean_nat_add(v_snd_1283_, v___x_1292_);
lean_dec(v_snd_1283_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v___x_1294_);
lean_ctor_set(v___x_1261_, 0, v___x_1293_);
v___x_1296_ = v___x_1261_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v___x_1294_);
v___x_1296_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
lean_object* v___x_1297_; size_t v___x_1298_; size_t v___x_1299_; lean_object* v___x_1300_; 
v___x_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1291_);
lean_ctor_set(v___x_1297_, 1, v___x_1296_);
v___x_1298_ = ((size_t)1ULL);
v___x_1299_ = lean_usize_add(v_i_1255_, v___x_1298_);
v___x_1300_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(v_original_1251_, v___x_1252_, v_edited_1249_, v___x_1250_, v_as_1253_, v_sz_1254_, v___x_1299_, v___x_1297_);
return v___x_1300_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5___boxed(lean_object* v_edited_1309_, lean_object* v___x_1310_, lean_object* v_original_1311_, lean_object* v___x_1312_, lean_object* v_as_1313_, lean_object* v_sz_1314_, lean_object* v_i_1315_, lean_object* v_b_1316_){
_start:
{
size_t v_sz_boxed_1317_; size_t v_i_boxed_1318_; lean_object* v_res_1319_; 
v_sz_boxed_1317_ = lean_unbox_usize(v_sz_1314_);
lean_dec(v_sz_1314_);
v_i_boxed_1318_ = lean_unbox_usize(v_i_1315_);
lean_dec(v_i_1315_);
v_res_1319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v_edited_1309_, v___x_1310_, v_original_1311_, v___x_1312_, v_as_1313_, v_sz_boxed_1317_, v_i_boxed_1318_, v_b_1316_);
lean_dec_ref(v_as_1313_);
lean_dec(v___x_1312_);
lean_dec_ref(v_original_1311_);
lean_dec(v___x_1310_);
lean_dec_ref(v_edited_1309_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(lean_object* v_original_1327_, lean_object* v_edited_1328_){
_start:
{
lean_object* v_i_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v_i_1329_ = lean_unsigned_to_nat(0u);
v___x_1330_ = lean_array_get_size(v_original_1327_);
v___x_1331_ = lean_nat_dec_lt(v_i_1329_, v___x_1330_);
if (v___x_1331_ == 0)
{
size_t v_sz_1332_; size_t v___x_1333_; lean_object* v___x_1334_; 
lean_dec_ref(v_original_1327_);
v_sz_1332_ = lean_array_size(v_edited_1328_);
v___x_1333_ = ((size_t)0ULL);
v___x_1334_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(v_sz_1332_, v___x_1333_, v_edited_1328_);
return v___x_1334_;
}
else
{
lean_object* v___x_1335_; uint8_t v___x_1336_; 
v___x_1335_ = lean_array_get_size(v_edited_1328_);
v___x_1336_ = lean_nat_dec_lt(v_i_1329_, v___x_1335_);
if (v___x_1336_ == 0)
{
size_t v_sz_1337_; size_t v___x_1338_; lean_object* v___x_1339_; 
lean_dec_ref(v_edited_1328_);
v_sz_1337_ = lean_array_size(v_original_1327_);
v___x_1338_ = ((size_t)0ULL);
v___x_1339_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(v_sz_1337_, v___x_1338_, v_original_1327_);
return v___x_1339_;
}
else
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v_ds_1342_; lean_object* v___x_1343_; size_t v_sz_1344_; size_t v___x_1345_; lean_object* v___x_1346_; lean_object* v_snd_1347_; lean_object* v_fst_1348_; lean_object* v_fst_1349_; lean_object* v_snd_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1369_; 
lean_inc_ref(v_original_1327_);
v___x_1340_ = l_Array_toSubarray___redArg(v_original_1327_, v_i_1329_, v___x_1330_);
lean_inc_ref(v_edited_1328_);
v___x_1341_ = l_Array_toSubarray___redArg(v_edited_1328_, v_i_1329_, v___x_1335_);
v_ds_1342_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v___x_1340_, v___x_1341_);
v___x_1343_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__2));
v_sz_1344_ = lean_array_size(v_ds_1342_);
v___x_1345_ = ((size_t)0ULL);
v___x_1346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v_edited_1328_, v___x_1335_, v_original_1327_, v___x_1330_, v_ds_1342_, v_sz_1344_, v___x_1345_, v___x_1343_);
lean_dec_ref(v_ds_1342_);
v_snd_1347_ = lean_ctor_get(v___x_1346_, 1);
lean_inc(v_snd_1347_);
v_fst_1348_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_fst_1348_);
lean_dec_ref(v___x_1346_);
v_fst_1349_ = lean_ctor_get(v_snd_1347_, 0);
v_snd_1350_ = lean_ctor_get(v_snd_1347_, 1);
v_isSharedCheck_1369_ = !lean_is_exclusive(v_snd_1347_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1352_ = v_snd_1347_;
v_isShared_1353_ = v_isSharedCheck_1369_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_snd_1350_);
lean_inc(v_fst_1349_);
lean_dec(v_snd_1347_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1369_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 1, v_fst_1349_);
lean_ctor_set(v___x_1352_, 0, v_fst_1348_);
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_fst_1348_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v_fst_1349_);
v___x_1355_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1356_; lean_object* v_fst_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1366_; 
v___x_1356_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_1330_, v_original_1327_, v___x_1355_);
lean_dec_ref(v_original_1327_);
v_fst_1357_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; 
v_unused_1367_ = lean_ctor_get(v___x_1356_, 1);
lean_dec(v_unused_1367_);
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1366_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_fst_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1366_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 1, v_snd_1350_);
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_fst_1357_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_snd_1350_);
v___x_1362_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1363_; lean_object* v_fst_1364_; 
v___x_1363_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1335_, v_edited_1328_, v___x_1362_);
lean_dec_ref(v_edited_1328_);
v_fst_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_fst_1364_);
lean_dec_ref(v___x_1363_);
return v_fst_1364_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(lean_object* v_s_1370_, lean_object* v_a_1371_, uint8_t v_b_1372_){
_start:
{
lean_object* v_str_1373_; lean_object* v_startInclusive_1374_; lean_object* v_endExclusive_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
v_str_1373_ = lean_ctor_get(v_s_1370_, 0);
v_startInclusive_1374_ = lean_ctor_get(v_s_1370_, 1);
v_endExclusive_1375_ = lean_ctor_get(v_s_1370_, 2);
v___x_1376_ = lean_nat_sub(v_endExclusive_1375_, v_startInclusive_1374_);
v___x_1377_ = lean_nat_dec_eq(v_a_1371_, v___x_1376_);
lean_dec(v___x_1376_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; uint32_t v___x_1379_; uint32_t v___x_1380_; uint8_t v___x_1381_; 
v___x_1378_ = lean_nat_add(v_startInclusive_1374_, v_a_1371_);
lean_dec(v_a_1371_);
v___x_1379_ = lean_string_utf8_get_fast(v_str_1373_, v___x_1378_);
v___x_1380_ = 10;
v___x_1381_ = lean_uint32_dec_eq(v___x_1379_, v___x_1380_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = lean_string_utf8_next_fast(v_str_1373_, v___x_1378_);
lean_dec(v___x_1378_);
v___x_1383_ = lean_nat_sub(v___x_1382_, v_startInclusive_1374_);
v_a_1371_ = v___x_1383_;
v_b_1372_ = v___x_1381_;
goto _start;
}
else
{
lean_dec(v___x_1378_);
return v___x_1381_;
}
}
else
{
lean_dec(v_a_1371_);
return v_b_1372_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg___boxed(lean_object* v_s_1385_, lean_object* v_a_1386_, lean_object* v_b_1387_){
_start:
{
uint8_t v_b_boxed_1388_; uint8_t v_res_1389_; lean_object* v_r_1390_; 
v_b_boxed_1388_ = lean_unbox(v_b_1387_);
v_res_1389_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1385_, v_a_1386_, v_b_boxed_1388_);
lean_dec_ref(v_s_1385_);
v_r_1390_ = lean_box(v_res_1389_);
return v_r_1390_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(lean_object* v_s_1391_){
_start:
{
lean_object* v_searcher_1392_; uint8_t v___x_1393_; uint8_t v___x_1394_; 
v_searcher_1392_ = lean_unsigned_to_nat(0u);
v___x_1393_ = 0;
v___x_1394_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1391_, v_searcher_1392_, v___x_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0___boxed(lean_object* v_s_1395_){
_start:
{
uint8_t v_res_1396_; lean_object* v_r_1397_; 
v_res_1396_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v_s_1395_);
lean_dec_ref(v_s_1395_);
v_r_1397_ = lean_box(v_res_1396_);
return v_r_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(lean_object* v_oldWs_1398_, lean_object* v_newWs_1399_){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v___x_1400_ = lean_unsigned_to_nat(0u);
v___x_1401_ = lean_string_utf8_byte_size(v_oldWs_1398_);
lean_inc_ref(v_oldWs_1398_);
v___x_1402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1402_, 0, v_oldWs_1398_);
lean_ctor_set(v___x_1402_, 1, v___x_1400_);
lean_ctor_set(v___x_1402_, 2, v___x_1401_);
v___x_1403_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_1402_);
lean_dec_ref_known(v___x_1402_, 3);
if (v___x_1403_ == 0)
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1404_ = lean_string_data(v_oldWs_1398_);
v___x_1405_ = lean_array_mk(v___x_1404_);
v___x_1406_ = lean_string_data(v_newWs_1399_);
v___x_1407_ = lean_array_mk(v___x_1406_);
v___x_1408_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_1405_, v___x_1407_);
v___x_1409_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_1408_);
lean_dec_ref(v___x_1408_);
return v___x_1409_;
}
else
{
uint8_t v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
lean_dec_ref(v_oldWs_1398_);
v___x_1410_ = 2;
v___x_1411_ = lean_box(v___x_1410_);
v___x_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
lean_ctor_set(v___x_1412_, 1, v_newWs_1399_);
v___x_1413_ = lean_unsigned_to_nat(1u);
v___x_1414_ = lean_mk_empty_array_with_capacity(v___x_1413_);
v___x_1415_ = lean_array_push(v___x_1414_, v___x_1412_);
return v___x_1415_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(lean_object* v_s_1416_, lean_object* v_inst_1417_, lean_object* v_R_1418_, lean_object* v_a_1419_, uint8_t v_b_1420_, lean_object* v_c_1421_){
_start:
{
uint8_t v___x_1422_; 
v___x_1422_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1416_, v_a_1419_, v_b_1420_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___boxed(lean_object* v_s_1423_, lean_object* v_inst_1424_, lean_object* v_R_1425_, lean_object* v_a_1426_, lean_object* v_b_1427_, lean_object* v_c_1428_){
_start:
{
uint8_t v_b_boxed_1429_; uint8_t v_res_1430_; lean_object* v_r_1431_; 
v_b_boxed_1429_ = lean_unbox(v_b_1427_);
v_res_1430_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(v_s_1423_, v_inst_1424_, v_R_1425_, v_a_1426_, v_b_boxed_1429_, v_c_1428_);
lean_dec_ref(v_s_1423_);
v_r_1431_ = lean_box(v_res_1430_);
return v_r_1431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(lean_object* v_original_1432_, lean_object* v___x_1433_, uint32_t v_a_1434_, lean_object* v_inst_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v_original_1432_, v___x_1433_, v_a_1434_, v_a_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___boxed(lean_object* v_original_1438_, lean_object* v___x_1439_, lean_object* v_a_1440_, lean_object* v_inst_1441_, lean_object* v_a_1442_){
_start:
{
uint32_t v_a_boxed_1443_; lean_object* v_res_1444_; 
v_a_boxed_1443_ = lean_unbox_uint32(v_a_1440_);
lean_dec(v_a_1440_);
v_res_1444_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(v_original_1438_, v___x_1439_, v_a_boxed_1443_, v_inst_1441_, v_a_1442_);
lean_dec(v___x_1439_);
lean_dec_ref(v_original_1438_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(lean_object* v_edited_1445_, lean_object* v___x_1446_, uint32_t v_a_1447_, lean_object* v_inst_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg(v_edited_1445_, v___x_1446_, v_a_1447_, v_a_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed(lean_object* v_edited_1451_, lean_object* v___x_1452_, lean_object* v_a_1453_, lean_object* v_inst_1454_, lean_object* v_a_1455_){
_start:
{
uint32_t v_a_boxed_1456_; lean_object* v_res_1457_; 
v_a_boxed_1456_ = lean_unbox_uint32(v_a_1453_);
lean_dec(v_a_1453_);
v_res_1457_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v_edited_1451_, v___x_1452_, v_a_boxed_1456_, v_inst_1454_, v_a_1455_);
lean_dec(v___x_1452_);
lean_dec_ref(v_edited_1451_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(lean_object* v___x_1458_, lean_object* v_original_1459_, lean_object* v_inst_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_1458_, v_original_1459_, v_a_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___boxed(lean_object* v___x_1463_, lean_object* v_original_1464_, lean_object* v_inst_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(v___x_1463_, v_original_1464_, v_inst_1465_, v_a_1466_);
lean_dec_ref(v_original_1464_);
lean_dec(v___x_1463_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(lean_object* v___x_1468_, lean_object* v_edited_1469_, lean_object* v_inst_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1468_, v_edited_1469_, v_a_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___boxed(lean_object* v___x_1473_, lean_object* v_edited_1474_, lean_object* v_inst_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(v___x_1473_, v_edited_1474_, v_inst_1475_, v_a_1476_);
lean_dec_ref(v_edited_1474_);
lean_dec(v___x_1473_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5(lean_object* v_as_1478_, lean_object* v_as_x27_1479_, lean_object* v_b_1480_, lean_object* v_a_1481_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg(v_as_x27_1479_, v_b_1480_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___boxed(lean_object* v_as_1483_, lean_object* v_as_x27_1484_, lean_object* v_b_1485_, lean_object* v_a_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5(v_as_1483_, v_as_x27_1484_, v_b_1485_, v_a_1486_);
lean_dec(v_as_x27_1484_);
lean_dec(v_as_1483_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8(lean_object* v_lsize_1488_, lean_object* v_rsize_1489_, lean_object* v_histogram_1490_, lean_object* v_index_1491_, uint32_t v_val_1492_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(v_histogram_1490_, v_index_1491_, v_val_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___boxed(lean_object* v_lsize_1494_, lean_object* v_rsize_1495_, lean_object* v_histogram_1496_, lean_object* v_index_1497_, lean_object* v_val_1498_){
_start:
{
uint32_t v_val_boxed_1499_; lean_object* v_res_1500_; 
v_val_boxed_1499_ = lean_unbox_uint32(v_val_1498_);
lean_dec(v_val_1498_);
v_res_1500_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8(v_lsize_1494_, v_rsize_1495_, v_histogram_1496_, v_index_1497_, v_val_boxed_1499_);
lean_dec(v_rsize_1495_);
lean_dec(v_lsize_1494_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9(lean_object* v_upperBound_1501_, lean_object* v___x_1502_, lean_object* v_fst_1503_, lean_object* v___x_1504_, lean_object* v_inst_1505_, lean_object* v_R_1506_, lean_object* v_a_1507_, lean_object* v_b_1508_, lean_object* v_c_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(v_upperBound_1501_, v___x_1502_, v_fst_1503_, v___x_1504_, v_a_1507_, v_b_1508_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___boxed(lean_object* v_upperBound_1511_, lean_object* v___x_1512_, lean_object* v_fst_1513_, lean_object* v___x_1514_, lean_object* v_inst_1515_, lean_object* v_R_1516_, lean_object* v_a_1517_, lean_object* v_b_1518_, lean_object* v_c_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9(v_upperBound_1511_, v___x_1512_, v_fst_1513_, v___x_1514_, v_inst_1515_, v_R_1516_, v_a_1517_, v_b_1518_, v_c_1519_);
lean_dec(v___x_1514_);
lean_dec_ref(v_fst_1513_);
lean_dec(v___x_1512_);
lean_dec(v_upperBound_1511_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10(lean_object* v_lsize_1521_, lean_object* v_rsize_1522_, lean_object* v_histogram_1523_, lean_object* v_index_1524_, uint32_t v_val_1525_){
_start:
{
lean_object* v___x_1526_; 
v___x_1526_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(v_histogram_1523_, v_index_1524_, v_val_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___boxed(lean_object* v_lsize_1527_, lean_object* v_rsize_1528_, lean_object* v_histogram_1529_, lean_object* v_index_1530_, lean_object* v_val_1531_){
_start:
{
uint32_t v_val_boxed_1532_; lean_object* v_res_1533_; 
v_val_boxed_1532_ = lean_unbox_uint32(v_val_1531_);
lean_dec(v_val_1531_);
v_res_1533_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10(v_lsize_1527_, v_rsize_1528_, v_histogram_1529_, v_index_1530_, v_val_boxed_1532_);
lean_dec(v_rsize_1528_);
lean_dec(v_lsize_1527_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11(lean_object* v_upperBound_1534_, lean_object* v_fst_1535_, lean_object* v___x_1536_, lean_object* v_fst_1537_, lean_object* v_inst_1538_, lean_object* v_R_1539_, lean_object* v_a_1540_, lean_object* v_b_1541_, lean_object* v_c_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg(v_upperBound_1534_, v_fst_1535_, v___x_1536_, v_fst_1537_, v_a_1540_, v_b_1541_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___boxed(lean_object* v_upperBound_1544_, lean_object* v_fst_1545_, lean_object* v___x_1546_, lean_object* v_fst_1547_, lean_object* v_inst_1548_, lean_object* v_R_1549_, lean_object* v_a_1550_, lean_object* v_b_1551_, lean_object* v_c_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11(v_upperBound_1544_, v_fst_1545_, v___x_1546_, v_fst_1547_, v_inst_1548_, v_R_1549_, v_a_1550_, v_b_1551_, v_c_1552_);
lean_dec_ref(v_fst_1547_);
lean_dec(v___x_1546_);
lean_dec_ref(v_fst_1545_);
lean_dec(v_upperBound_1544_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11(lean_object* v_00_u03b2_1554_, lean_object* v_m_1555_, uint32_t v_a_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(v_m_1555_, v_a_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___boxed(lean_object* v_00_u03b2_1558_, lean_object* v_m_1559_, lean_object* v_a_1560_){
_start:
{
uint32_t v_a_boxed_1561_; lean_object* v_res_1562_; 
v_a_boxed_1561_ = lean_unbox_uint32(v_a_1560_);
lean_dec(v_a_1560_);
v_res_1562_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11(v_00_u03b2_1558_, v_m_1559_, v_a_boxed_1561_);
lean_dec_ref(v_m_1559_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12(lean_object* v_00_u03b2_1563_, lean_object* v_m_1564_, uint32_t v_a_1565_, lean_object* v_b_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_m_1564_, v_a_1565_, v_b_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___boxed(lean_object* v_00_u03b2_1568_, lean_object* v_m_1569_, lean_object* v_a_1570_, lean_object* v_b_1571_){
_start:
{
uint32_t v_a_boxed_1572_; lean_object* v_res_1573_; 
v_a_boxed_1572_ = lean_unbox_uint32(v_a_1570_);
lean_dec(v_a_1570_);
v_res_1573_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12(v_00_u03b2_1568_, v_m_1569_, v_a_boxed_1572_, v_b_1571_);
return v_res_1573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14(lean_object* v_inst_1574_, lean_object* v_R_1575_, lean_object* v_a_1576_, lean_object* v_b_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(v_a_1576_, v_b_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20(lean_object* v_00_u03b2_1579_, uint32_t v_a_1580_, lean_object* v_x_1581_){
_start:
{
lean_object* v___x_1582_; 
v___x_1582_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg(v_a_1580_, v_x_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___boxed(lean_object* v_00_u03b2_1583_, lean_object* v_a_1584_, lean_object* v_x_1585_){
_start:
{
uint32_t v_a_boxed_1586_; lean_object* v_res_1587_; 
v_a_boxed_1586_ = lean_unbox_uint32(v_a_1584_);
lean_dec(v_a_1584_);
v_res_1587_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20(v_00_u03b2_1583_, v_a_boxed_1586_, v_x_1585_);
lean_dec(v_x_1585_);
return v_res_1587_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22(lean_object* v_00_u03b2_1588_, uint32_t v_a_1589_, lean_object* v_x_1590_){
_start:
{
uint8_t v___x_1591_; 
v___x_1591_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg(v_a_1589_, v_x_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___boxed(lean_object* v_00_u03b2_1592_, lean_object* v_a_1593_, lean_object* v_x_1594_){
_start:
{
uint32_t v_a_boxed_1595_; uint8_t v_res_1596_; lean_object* v_r_1597_; 
v_a_boxed_1595_ = lean_unbox_uint32(v_a_1593_);
lean_dec(v_a_1593_);
v_res_1596_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22(v_00_u03b2_1592_, v_a_boxed_1595_, v_x_1594_);
lean_dec(v_x_1594_);
v_r_1597_ = lean_box(v_res_1596_);
return v_r_1597_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23(lean_object* v_00_u03b2_1598_, lean_object* v_data_1599_){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23___redArg(v_data_1599_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24(lean_object* v_00_u03b2_1601_, uint32_t v_a_1602_, lean_object* v_b_1603_, lean_object* v_x_1604_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(v_a_1602_, v_b_1603_, v_x_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___boxed(lean_object* v_00_u03b2_1606_, lean_object* v_a_1607_, lean_object* v_b_1608_, lean_object* v_x_1609_){
_start:
{
uint32_t v_a_boxed_1610_; lean_object* v_res_1611_; 
v_a_boxed_1610_ = lean_unbox_uint32(v_a_1607_);
lean_dec(v_a_1607_);
v_res_1611_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24(v_00_u03b2_1606_, v_a_boxed_1610_, v_b_1608_, v_x_1609_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28(lean_object* v_00_u03b2_1612_, lean_object* v_i_1613_, lean_object* v_source_1614_, lean_object* v_target_1615_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28___redArg(v_i_1613_, v_source_1614_, v_target_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_1617_, lean_object* v_x_1618_, lean_object* v_x_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29___redArg(v_x_1618_, v_x_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(lean_object* v_s_1621_, lean_object* v_stopPos_1622_, lean_object* v_i_1623_){
_start:
{
uint8_t v___y_1628_; uint8_t v___x_1629_; 
v___x_1629_ = lean_nat_dec_lt(v_i_1623_, v_stopPos_1622_);
if (v___x_1629_ == 0)
{
return v_i_1623_;
}
else
{
uint32_t v___x_1630_; uint8_t v___y_1632_; uint32_t v___x_1637_; uint8_t v___x_1638_; 
v___x_1630_ = lean_string_utf8_get(v_s_1621_, v_i_1623_);
v___x_1637_ = 32;
v___x_1638_ = lean_uint32_dec_eq(v___x_1630_, v___x_1637_);
if (v___x_1638_ == 0)
{
uint32_t v___x_1639_; uint8_t v___x_1640_; 
v___x_1639_ = 9;
v___x_1640_ = lean_uint32_dec_eq(v___x_1630_, v___x_1639_);
v___y_1632_ = v___x_1640_;
goto v___jp_1631_;
}
else
{
v___y_1632_ = v___x_1638_;
goto v___jp_1631_;
}
v___jp_1631_:
{
if (v___y_1632_ == 0)
{
uint32_t v___x_1633_; uint8_t v___x_1634_; 
v___x_1633_ = 13;
v___x_1634_ = lean_uint32_dec_eq(v___x_1630_, v___x_1633_);
if (v___x_1634_ == 0)
{
uint32_t v___x_1635_; uint8_t v___x_1636_; 
v___x_1635_ = 10;
v___x_1636_ = lean_uint32_dec_eq(v___x_1630_, v___x_1635_);
v___y_1628_ = v___x_1636_;
goto v___jp_1627_;
}
else
{
v___y_1628_ = v___x_1634_;
goto v___jp_1627_;
}
}
else
{
goto v___jp_1624_;
}
}
}
v___jp_1624_:
{
lean_object* v___x_1625_; 
v___x_1625_ = lean_string_utf8_next(v_s_1621_, v_i_1623_);
lean_dec(v_i_1623_);
v_i_1623_ = v___x_1625_;
goto _start;
}
v___jp_1627_:
{
if (v___y_1628_ == 0)
{
return v_i_1623_;
}
else
{
goto v___jp_1624_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0___boxed(lean_object* v_s_1641_, lean_object* v_stopPos_1642_, lean_object* v_i_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1641_, v_stopPos_1642_, v_i_1643_);
lean_dec(v_stopPos_1642_);
lean_dec_ref(v_s_1641_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(lean_object* v_s_1645_, lean_object* v_b_1646_, lean_object* v_i_1647_, lean_object* v_r_1648_, lean_object* v_ws_1649_){
_start:
{
uint8_t v___y_1659_; uint8_t v___x_1662_; 
v___x_1662_ = lean_string_utf8_at_end(v_s_1645_, v_i_1647_);
if (v___x_1662_ == 0)
{
uint32_t v___x_1663_; uint8_t v___y_1665_; uint32_t v___x_1670_; uint8_t v___x_1671_; 
v___x_1663_ = lean_string_utf8_get(v_s_1645_, v_i_1647_);
v___x_1670_ = 32;
v___x_1671_ = lean_uint32_dec_eq(v___x_1663_, v___x_1670_);
if (v___x_1671_ == 0)
{
uint32_t v___x_1672_; uint8_t v___x_1673_; 
v___x_1672_ = 9;
v___x_1673_ = lean_uint32_dec_eq(v___x_1663_, v___x_1672_);
v___y_1665_ = v___x_1673_;
goto v___jp_1664_;
}
else
{
v___y_1665_ = v___x_1671_;
goto v___jp_1664_;
}
v___jp_1664_:
{
if (v___y_1665_ == 0)
{
uint32_t v___x_1666_; uint8_t v___x_1667_; 
v___x_1666_ = 13;
v___x_1667_ = lean_uint32_dec_eq(v___x_1663_, v___x_1666_);
if (v___x_1667_ == 0)
{
uint32_t v___x_1668_; uint8_t v___x_1669_; 
v___x_1668_ = 10;
v___x_1669_ = lean_uint32_dec_eq(v___x_1663_, v___x_1668_);
v___y_1659_ = v___x_1669_;
goto v___jp_1658_;
}
else
{
v___y_1659_ = v___x_1667_;
goto v___jp_1658_;
}
}
else
{
goto v___jp_1650_;
}
}
}
else
{
lean_object* v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; 
v___x_1674_ = lean_string_utf8_extract(v_s_1645_, v_b_1646_, v_i_1647_);
lean_dec(v_i_1647_);
lean_dec(v_b_1646_);
v___x_1675_ = lean_array_push(v_r_1648_, v___x_1674_);
v___x_1676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1676_, 0, v___x_1675_);
lean_ctor_set(v___x_1676_, 1, v_ws_1649_);
return v___x_1676_;
}
v___jp_1650_:
{
lean_object* v___x_1651_; lean_object* v_e_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1651_ = lean_string_utf8_byte_size(v_s_1645_);
lean_inc(v_i_1647_);
v_e_1652_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1645_, v___x_1651_, v_i_1647_);
v___x_1653_ = lean_string_utf8_extract(v_s_1645_, v_b_1646_, v_i_1647_);
lean_dec(v_b_1646_);
v___x_1654_ = lean_array_push(v_r_1648_, v___x_1653_);
v___x_1655_ = lean_string_utf8_extract(v_s_1645_, v_i_1647_, v_e_1652_);
lean_dec(v_i_1647_);
v___x_1656_ = lean_array_push(v_ws_1649_, v___x_1655_);
lean_inc(v_e_1652_);
v_b_1646_ = v_e_1652_;
v_i_1647_ = v_e_1652_;
v_r_1648_ = v___x_1654_;
v_ws_1649_ = v___x_1656_;
goto _start;
}
v___jp_1658_:
{
if (v___y_1659_ == 0)
{
lean_object* v___x_1660_; 
v___x_1660_ = lean_string_utf8_next(v_s_1645_, v_i_1647_);
lean_dec(v_i_1647_);
v_i_1647_ = v___x_1660_;
goto _start;
}
else
{
goto v___jp_1650_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux___boxed(lean_object* v_s_1677_, lean_object* v_b_1678_, lean_object* v_i_1679_, lean_object* v_r_1680_, lean_object* v_ws_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1677_, v_b_1678_, v_i_1679_, v_r_1680_, v_ws_1681_);
lean_dec_ref(v_s_1677_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(lean_object* v_s_1685_){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v___x_1686_ = lean_unsigned_to_nat(0u);
v___x_1687_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_1688_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1685_, v___x_1686_, v___x_1686_, v___x_1687_, v___x_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___boxed(lean_object* v_s_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_1689_);
lean_dec_ref(v_s_1689_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(size_t v_sz_1691_, size_t v_i_1692_, lean_object* v_bs_1693_){
_start:
{
uint8_t v___x_1694_; 
v___x_1694_ = lean_usize_dec_lt(v_i_1692_, v_sz_1691_);
if (v___x_1694_ == 0)
{
return v_bs_1693_;
}
else
{
lean_object* v_v_1695_; lean_object* v_fst_1696_; lean_object* v_snd_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1731_; 
v_v_1695_ = lean_array_uget(v_bs_1693_, v_i_1692_);
v_fst_1696_ = lean_ctor_get(v_v_1695_, 0);
v_snd_1697_ = lean_ctor_get(v_v_1695_, 1);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_v_1695_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1699_ = v_v_1695_;
v_isShared_1700_ = v_isSharedCheck_1731_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_snd_1697_);
lean_inc(v_fst_1696_);
lean_dec(v_v_1695_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1731_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1701_; lean_object* v_bs_x27_1702_; lean_object* v___y_1704_; lean_object* v___x_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; 
v___x_1701_ = lean_unsigned_to_nat(0u);
v_bs_x27_1702_ = lean_array_uset(v_bs_1693_, v_i_1692_, v___x_1701_);
v___x_1709_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_1710_ = lean_array_get_size(v_snd_1697_);
v___x_1711_ = lean_nat_dec_lt(v___x_1701_, v___x_1710_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1713_; 
lean_dec(v_snd_1697_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 1, v___x_1709_);
v___x_1713_ = v___x_1699_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_fst_1696_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v___x_1709_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
v___y_1704_ = v___x_1713_;
goto v___jp_1703_;
}
}
else
{
uint8_t v___x_1715_; 
v___x_1715_ = lean_nat_dec_le(v___x_1710_, v___x_1710_);
if (v___x_1715_ == 0)
{
if (v___x_1711_ == 0)
{
lean_object* v___x_1717_; 
lean_dec(v_snd_1697_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 1, v___x_1709_);
v___x_1717_ = v___x_1699_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_fst_1696_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v___x_1709_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
v___y_1704_ = v___x_1717_;
goto v___jp_1703_;
}
}
else
{
size_t v___x_1719_; size_t v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1723_; 
v___x_1719_ = ((size_t)0ULL);
v___x_1720_ = lean_usize_of_nat(v___x_1710_);
v___x_1721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_1697_, v___x_1719_, v___x_1720_, v___x_1709_);
lean_dec(v_snd_1697_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 1, v___x_1721_);
v___x_1723_ = v___x_1699_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_fst_1696_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v___x_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
v___y_1704_ = v___x_1723_;
goto v___jp_1703_;
}
}
}
else
{
size_t v___x_1725_; size_t v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1725_ = ((size_t)0ULL);
v___x_1726_ = lean_usize_of_nat(v___x_1710_);
v___x_1727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_1697_, v___x_1725_, v___x_1726_, v___x_1709_);
lean_dec(v_snd_1697_);
if (v_isShared_1700_ == 0)
{
lean_ctor_set(v___x_1699_, 1, v___x_1727_);
v___x_1729_ = v___x_1699_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v_fst_1696_);
lean_ctor_set(v_reuseFailAlloc_1730_, 1, v___x_1727_);
v___x_1729_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
v___y_1704_ = v___x_1729_;
goto v___jp_1703_;
}
}
}
v___jp_1703_:
{
size_t v___x_1705_; size_t v___x_1706_; lean_object* v___x_1707_; 
v___x_1705_ = ((size_t)1ULL);
v___x_1706_ = lean_usize_add(v_i_1692_, v___x_1705_);
v___x_1707_ = lean_array_uset(v_bs_x27_1702_, v_i_1692_, v___y_1704_);
v_i_1692_ = v___x_1706_;
v_bs_1693_ = v___x_1707_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0___boxed(lean_object* v_sz_1732_, lean_object* v_i_1733_, lean_object* v_bs_1734_){
_start:
{
size_t v_sz_boxed_1735_; size_t v_i_boxed_1736_; lean_object* v_res_1737_; 
v_sz_boxed_1735_ = lean_unbox_usize(v_sz_1732_);
lean_dec(v_sz_1732_);
v_i_boxed_1736_ = lean_unbox_usize(v_i_1733_);
lean_dec(v_i_1733_);
v_res_1737_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_boxed_1735_, v_i_boxed_1736_, v_bs_1734_);
return v_res_1737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(size_t v_sz_1738_, size_t v_i_1739_, lean_object* v_bs_1740_){
_start:
{
uint8_t v___x_1741_; 
v___x_1741_ = lean_usize_dec_lt(v_i_1739_, v_sz_1738_);
if (v___x_1741_ == 0)
{
return v_bs_1740_;
}
else
{
lean_object* v_v_1742_; lean_object* v___x_1743_; lean_object* v_bs_x27_1744_; uint8_t v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; size_t v___x_1748_; size_t v___x_1749_; lean_object* v___x_1750_; 
v_v_1742_ = lean_array_uget(v_bs_1740_, v_i_1739_);
v___x_1743_ = lean_unsigned_to_nat(0u);
v_bs_x27_1744_ = lean_array_uset(v_bs_1740_, v_i_1739_, v___x_1743_);
v___x_1745_ = 0;
v___x_1746_ = lean_box(v___x_1745_);
v___x_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
lean_ctor_set(v___x_1747_, 1, v_v_1742_);
v___x_1748_ = ((size_t)1ULL);
v___x_1749_ = lean_usize_add(v_i_1739_, v___x_1748_);
v___x_1750_ = lean_array_uset(v_bs_x27_1744_, v_i_1739_, v___x_1747_);
v_i_1739_ = v___x_1749_;
v_bs_1740_ = v___x_1750_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8___boxed(lean_object* v_sz_1752_, lean_object* v_i_1753_, lean_object* v_bs_1754_){
_start:
{
size_t v_sz_boxed_1755_; size_t v_i_boxed_1756_; lean_object* v_res_1757_; 
v_sz_boxed_1755_ = lean_unbox_usize(v_sz_1752_);
lean_dec(v_sz_1752_);
v_i_boxed_1756_ = lean_unbox_usize(v_i_1753_);
lean_dec(v_i_1753_);
v_res_1757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_boxed_1755_, v_i_boxed_1756_, v_bs_1754_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(lean_object* v___x_1758_, lean_object* v_original_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v_fst_1761_; lean_object* v_snd_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1781_; 
v_fst_1761_ = lean_ctor_get(v_a_1760_, 0);
v_snd_1762_ = lean_ctor_get(v_a_1760_, 1);
v_isSharedCheck_1781_ = !lean_is_exclusive(v_a_1760_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1764_ = v_a_1760_;
v_isShared_1765_ = v_isSharedCheck_1781_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_snd_1762_);
lean_inc(v_fst_1761_);
lean_dec(v_a_1760_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1781_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
uint8_t v___x_1766_; 
v___x_1766_ = lean_nat_dec_lt(v_snd_1762_, v___x_1758_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1768_; 
if (v_isShared_1765_ == 0)
{
v___x_1768_ = v___x_1764_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_fst_1761_);
lean_ctor_set(v_reuseFailAlloc_1769_, 1, v_snd_1762_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
else
{
uint8_t v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1774_; 
v___x_1770_ = 1;
v___x_1771_ = lean_array_fget_borrowed(v_original_1759_, v_snd_1762_);
v___x_1772_ = lean_box(v___x_1770_);
lean_inc(v___x_1771_);
if (v_isShared_1765_ == 0)
{
lean_ctor_set(v___x_1764_, 1, v___x_1771_);
lean_ctor_set(v___x_1764_, 0, v___x_1772_);
v___x_1774_ = v___x_1764_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1772_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v___x_1771_);
v___x_1774_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1775_ = lean_array_push(v_fst_1761_, v___x_1774_);
v___x_1776_ = lean_unsigned_to_nat(1u);
v___x_1777_ = lean_nat_add(v_snd_1762_, v___x_1776_);
lean_dec(v_snd_1762_);
v___x_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1778_, 0, v___x_1775_);
lean_ctor_set(v___x_1778_, 1, v___x_1777_);
v_a_1760_ = v___x_1778_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg___boxed(lean_object* v___x_1782_, lean_object* v_original_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v_res_1785_; 
v_res_1785_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_1782_, v_original_1783_, v_a_1784_);
lean_dec_ref(v_original_1783_);
lean_dec(v___x_1782_);
return v_res_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(lean_object* v___x_1786_, lean_object* v_edited_1787_, lean_object* v_a_1788_){
_start:
{
lean_object* v_fst_1789_; lean_object* v_snd_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1809_; 
v_fst_1789_ = lean_ctor_get(v_a_1788_, 0);
v_snd_1790_ = lean_ctor_get(v_a_1788_, 1);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_a_1788_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1792_ = v_a_1788_;
v_isShared_1793_ = v_isSharedCheck_1809_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_snd_1790_);
lean_inc(v_fst_1789_);
lean_dec(v_a_1788_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1809_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
uint8_t v___x_1794_; 
v___x_1794_ = lean_nat_dec_lt(v_snd_1790_, v___x_1786_);
if (v___x_1794_ == 0)
{
lean_object* v___x_1796_; 
if (v_isShared_1793_ == 0)
{
v___x_1796_ = v___x_1792_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_fst_1789_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_snd_1790_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
else
{
uint8_t v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1802_; 
v___x_1798_ = 0;
v___x_1799_ = lean_array_fget_borrowed(v_edited_1787_, v_snd_1790_);
v___x_1800_ = lean_box(v___x_1798_);
lean_inc(v___x_1799_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 1, v___x_1799_);
lean_ctor_set(v___x_1792_, 0, v___x_1800_);
v___x_1802_ = v___x_1792_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1800_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v___x_1799_);
v___x_1802_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1803_ = lean_array_push(v_fst_1789_, v___x_1802_);
v___x_1804_ = lean_unsigned_to_nat(1u);
v___x_1805_ = lean_nat_add(v_snd_1790_, v___x_1804_);
lean_dec(v_snd_1790_);
v___x_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1803_);
lean_ctor_set(v___x_1806_, 1, v___x_1805_);
v_a_1788_ = v___x_1806_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg___boxed(lean_object* v___x_1810_, lean_object* v_edited_1811_, lean_object* v_a_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_1810_, v_edited_1811_, v_a_1812_);
lean_dec_ref(v_edited_1811_);
lean_dec(v___x_1810_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(lean_object* v_original_1814_, lean_object* v___x_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v_fst_1818_; lean_object* v_snd_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1844_; 
v_fst_1818_ = lean_ctor_get(v_a_1817_, 0);
v_snd_1819_ = lean_ctor_get(v_a_1817_, 1);
v_isSharedCheck_1844_ = !lean_is_exclusive(v_a_1817_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1821_ = v_a_1817_;
v_isShared_1822_ = v_isSharedCheck_1844_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_snd_1819_);
lean_inc(v_fst_1818_);
lean_dec(v_a_1817_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1844_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; uint8_t v___y_1825_; uint8_t v___x_1840_; 
v___x_1823_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_1840_ = lean_nat_dec_lt(v_snd_1819_, v___x_1815_);
if (v___x_1840_ == 0)
{
v___y_1825_ = v___x_1840_;
goto v___jp_1824_;
}
else
{
lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1841_ = lean_array_get_borrowed(v___x_1823_, v_original_1814_, v_snd_1819_);
v___x_1842_ = lean_string_dec_eq(v___x_1841_, v_a_1816_);
if (v___x_1842_ == 0)
{
v___y_1825_ = v___x_1840_;
goto v___jp_1824_;
}
else
{
lean_object* v___x_1843_; 
lean_del_object(v___x_1821_);
v___x_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1843_, 0, v_fst_1818_);
lean_ctor_set(v___x_1843_, 1, v_snd_1819_);
return v___x_1843_;
}
}
v___jp_1824_:
{
if (v___y_1825_ == 0)
{
lean_object* v___x_1827_; 
if (v_isShared_1822_ == 0)
{
v___x_1827_ = v___x_1821_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_fst_1818_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_snd_1819_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
else
{
uint8_t v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1829_ = 1;
v___x_1830_ = lean_array_get_borrowed(v___x_1823_, v_original_1814_, v_snd_1819_);
v___x_1831_ = lean_box(v___x_1829_);
lean_inc(v___x_1830_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 1, v___x_1830_);
lean_ctor_set(v___x_1821_, 0, v___x_1831_);
v___x_1833_ = v___x_1821_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v___x_1831_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v___x_1830_);
v___x_1833_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1834_ = lean_array_push(v_fst_1818_, v___x_1833_);
v___x_1835_ = lean_unsigned_to_nat(1u);
v___x_1836_ = lean_nat_add(v_snd_1819_, v___x_1835_);
lean_dec(v_snd_1819_);
v___x_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1834_);
lean_ctor_set(v___x_1837_, 1, v___x_1836_);
v_a_1817_ = v___x_1837_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg___boxed(lean_object* v_original_1845_, lean_object* v___x_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v_original_1845_, v___x_1846_, v_a_1847_, v_a_1848_);
lean_dec_ref(v_a_1847_);
lean_dec(v___x_1846_);
lean_dec_ref(v_original_1845_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(lean_object* v_edited_1850_, lean_object* v___x_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_){
_start:
{
lean_object* v_fst_1854_; lean_object* v_snd_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1880_; 
v_fst_1854_ = lean_ctor_get(v_a_1853_, 0);
v_snd_1855_ = lean_ctor_get(v_a_1853_, 1);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_a_1853_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1857_ = v_a_1853_;
v_isShared_1858_ = v_isSharedCheck_1880_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_snd_1855_);
lean_inc(v_fst_1854_);
lean_dec(v_a_1853_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1880_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; uint8_t v___y_1861_; uint8_t v___x_1876_; 
v___x_1859_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_1876_ = lean_nat_dec_lt(v_snd_1855_, v___x_1851_);
if (v___x_1876_ == 0)
{
v___y_1861_ = v___x_1876_;
goto v___jp_1860_;
}
else
{
lean_object* v___x_1877_; uint8_t v___x_1878_; 
v___x_1877_ = lean_array_get_borrowed(v___x_1859_, v_edited_1850_, v_snd_1855_);
v___x_1878_ = lean_string_dec_eq(v___x_1877_, v_a_1852_);
if (v___x_1878_ == 0)
{
v___y_1861_ = v___x_1876_;
goto v___jp_1860_;
}
else
{
lean_object* v___x_1879_; 
lean_del_object(v___x_1857_);
v___x_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1879_, 0, v_fst_1854_);
lean_ctor_set(v___x_1879_, 1, v_snd_1855_);
return v___x_1879_;
}
}
v___jp_1860_:
{
if (v___y_1861_ == 0)
{
lean_object* v___x_1863_; 
if (v_isShared_1858_ == 0)
{
v___x_1863_ = v___x_1857_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_fst_1854_);
lean_ctor_set(v_reuseFailAlloc_1864_, 1, v_snd_1855_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
else
{
uint8_t v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1865_ = 0;
v___x_1866_ = lean_array_get_borrowed(v___x_1859_, v_edited_1850_, v_snd_1855_);
v___x_1867_ = lean_box(v___x_1865_);
lean_inc(v___x_1866_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 1, v___x_1866_);
lean_ctor_set(v___x_1857_, 0, v___x_1867_);
v___x_1869_ = v___x_1857_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1875_, 1, v___x_1866_);
v___x_1869_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1870_ = lean_array_push(v_fst_1854_, v___x_1869_);
v___x_1871_ = lean_unsigned_to_nat(1u);
v___x_1872_ = lean_nat_add(v_snd_1855_, v___x_1871_);
lean_dec(v_snd_1855_);
v___x_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1870_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v_a_1853_ = v___x_1873_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg___boxed(lean_object* v_edited_1881_, lean_object* v___x_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(v_edited_1881_, v___x_1882_, v_a_1883_, v_a_1884_);
lean_dec_ref(v_a_1883_);
lean_dec(v___x_1882_);
lean_dec_ref(v_edited_1881_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(lean_object* v_original_1886_, lean_object* v___x_1887_, lean_object* v_edited_1888_, lean_object* v___x_1889_, lean_object* v_as_1890_, size_t v_sz_1891_, size_t v_i_1892_, lean_object* v_b_1893_){
_start:
{
uint8_t v___x_1894_; 
v___x_1894_ = lean_usize_dec_lt(v_i_1892_, v_sz_1891_);
if (v___x_1894_ == 0)
{
return v_b_1893_;
}
else
{
lean_object* v_snd_1895_; lean_object* v_fst_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1943_; 
v_snd_1895_ = lean_ctor_get(v_b_1893_, 1);
v_fst_1896_ = lean_ctor_get(v_b_1893_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_b_1893_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1898_ = v_b_1893_;
v_isShared_1899_ = v_isSharedCheck_1943_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_snd_1895_);
lean_inc(v_fst_1896_);
lean_dec(v_b_1893_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1943_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v_fst_1900_; lean_object* v_snd_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1942_; 
v_fst_1900_ = lean_ctor_get(v_snd_1895_, 0);
v_snd_1901_ = lean_ctor_get(v_snd_1895_, 1);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_snd_1895_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1903_ = v_snd_1895_;
v_isShared_1904_ = v_isSharedCheck_1942_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_snd_1901_);
lean_inc(v_fst_1900_);
lean_dec(v_snd_1895_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1942_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v_a_1905_; lean_object* v___x_1907_; 
v_a_1905_ = lean_array_uget_borrowed(v_as_1890_, v_i_1892_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 1, v_fst_1900_);
lean_ctor_set(v___x_1903_, 0, v_fst_1896_);
v___x_1907_ = v___x_1903_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_fst_1896_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_fst_1900_);
v___x_1907_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1908_; lean_object* v_fst_1909_; lean_object* v_snd_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1940_; 
v___x_1908_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v_original_1886_, v___x_1887_, v_a_1905_, v___x_1907_);
v_fst_1909_ = lean_ctor_get(v___x_1908_, 0);
v_snd_1910_ = lean_ctor_get(v___x_1908_, 1);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1912_ = v___x_1908_;
v_isShared_1913_ = v_isSharedCheck_1940_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_snd_1910_);
lean_inc(v_fst_1909_);
lean_dec(v___x_1908_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1940_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 1, v_snd_1901_);
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_fst_1909_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_snd_1901_);
v___x_1915_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1916_; lean_object* v_fst_1917_; lean_object* v_snd_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1938_; 
v___x_1916_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(v_edited_1888_, v___x_1889_, v_a_1905_, v___x_1915_);
v_fst_1917_ = lean_ctor_get(v___x_1916_, 0);
v_snd_1918_ = lean_ctor_get(v___x_1916_, 1);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1916_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1920_ = v___x_1916_;
v_isShared_1921_ = v_isSharedCheck_1938_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_snd_1918_);
lean_inc(v_fst_1917_);
lean_dec(v___x_1916_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1938_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
uint8_t v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1922_ = 2;
v___x_1923_ = lean_box(v___x_1922_);
lean_inc(v_a_1905_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 1, v_a_1905_);
lean_ctor_set(v___x_1920_, 0, v___x_1923_);
v___x_1925_ = v___x_1920_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1923_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_a_1905_);
v___x_1925_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1926_ = lean_array_push(v_fst_1917_, v___x_1925_);
v___x_1927_ = lean_unsigned_to_nat(1u);
v___x_1928_ = lean_nat_add(v_snd_1910_, v___x_1927_);
lean_dec(v_snd_1910_);
v___x_1929_ = lean_nat_add(v_snd_1918_, v___x_1927_);
lean_dec(v_snd_1918_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 1, v___x_1929_);
lean_ctor_set(v___x_1898_, 0, v___x_1928_);
v___x_1931_ = v___x_1898_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1928_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v___x_1929_);
v___x_1931_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
lean_object* v___x_1932_; size_t v___x_1933_; size_t v___x_1934_; 
v___x_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1926_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
v___x_1933_ = ((size_t)1ULL);
v___x_1934_ = lean_usize_add(v_i_1892_, v___x_1933_);
v_i_1892_ = v___x_1934_;
v_b_1893_ = v___x_1932_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14___boxed(lean_object* v_original_1944_, lean_object* v___x_1945_, lean_object* v_edited_1946_, lean_object* v___x_1947_, lean_object* v_as_1948_, lean_object* v_sz_1949_, lean_object* v_i_1950_, lean_object* v_b_1951_){
_start:
{
size_t v_sz_boxed_1952_; size_t v_i_boxed_1953_; lean_object* v_res_1954_; 
v_sz_boxed_1952_ = lean_unbox_usize(v_sz_1949_);
lean_dec(v_sz_1949_);
v_i_boxed_1953_ = lean_unbox_usize(v_i_1950_);
lean_dec(v_i_1950_);
v_res_1954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v_original_1944_, v___x_1945_, v_edited_1946_, v___x_1947_, v_as_1948_, v_sz_boxed_1952_, v_i_boxed_1953_, v_b_1951_);
lean_dec_ref(v_as_1948_);
lean_dec(v___x_1947_);
lean_dec_ref(v_edited_1946_);
lean_dec(v___x_1945_);
lean_dec_ref(v_original_1944_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(lean_object* v_edited_1955_, lean_object* v___x_1956_, lean_object* v_original_1957_, lean_object* v___x_1958_, lean_object* v_as_1959_, size_t v_sz_1960_, size_t v_i_1961_, lean_object* v_b_1962_){
_start:
{
uint8_t v___x_1963_; 
v___x_1963_ = lean_usize_dec_lt(v_i_1961_, v_sz_1960_);
if (v___x_1963_ == 0)
{
return v_b_1962_;
}
else
{
lean_object* v_snd_1964_; lean_object* v_fst_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_2012_; 
v_snd_1964_ = lean_ctor_get(v_b_1962_, 1);
v_fst_1965_ = lean_ctor_get(v_b_1962_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v_b_1962_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_1967_ = v_b_1962_;
v_isShared_1968_ = v_isSharedCheck_2012_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_snd_1964_);
lean_inc(v_fst_1965_);
lean_dec(v_b_1962_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_2012_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v_fst_1969_; lean_object* v_snd_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2011_; 
v_fst_1969_ = lean_ctor_get(v_snd_1964_, 0);
v_snd_1970_ = lean_ctor_get(v_snd_1964_, 1);
v_isSharedCheck_2011_ = !lean_is_exclusive(v_snd_1964_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_1972_ = v_snd_1964_;
v_isShared_1973_ = v_isSharedCheck_2011_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_snd_1970_);
lean_inc(v_fst_1969_);
lean_dec(v_snd_1964_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2011_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_a_1974_; lean_object* v___x_1976_; 
v_a_1974_ = lean_array_uget_borrowed(v_as_1959_, v_i_1961_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 1, v_fst_1969_);
lean_ctor_set(v___x_1972_, 0, v_fst_1965_);
v___x_1976_ = v___x_1972_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_fst_1965_);
lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_fst_1969_);
v___x_1976_ = v_reuseFailAlloc_2010_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1977_; lean_object* v_fst_1978_; lean_object* v_snd_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_2009_; 
v___x_1977_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v_original_1957_, v___x_1958_, v_a_1974_, v___x_1976_);
v_fst_1978_ = lean_ctor_get(v___x_1977_, 0);
v_snd_1979_ = lean_ctor_get(v___x_1977_, 1);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___x_1977_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_1981_ = v___x_1977_;
v_isShared_1982_ = v_isSharedCheck_2009_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_snd_1979_);
lean_inc(v_fst_1978_);
lean_dec(v___x_1977_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_2009_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v___x_1984_; 
if (v_isShared_1982_ == 0)
{
lean_ctor_set(v___x_1981_, 1, v_snd_1970_);
v___x_1984_ = v___x_1981_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_fst_1978_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_snd_1970_);
v___x_1984_ = v_reuseFailAlloc_2008_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1985_; lean_object* v_fst_1986_; lean_object* v_snd_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2007_; 
v___x_1985_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(v_edited_1955_, v___x_1956_, v_a_1974_, v___x_1984_);
v_fst_1986_ = lean_ctor_get(v___x_1985_, 0);
v_snd_1987_ = lean_ctor_get(v___x_1985_, 1);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_1989_ = v___x_1985_;
v_isShared_1990_ = v_isSharedCheck_2007_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_snd_1987_);
lean_inc(v_fst_1986_);
lean_dec(v___x_1985_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2007_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
uint8_t v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1994_; 
v___x_1991_ = 2;
v___x_1992_ = lean_box(v___x_1991_);
lean_inc(v_a_1974_);
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 1, v_a_1974_);
lean_ctor_set(v___x_1989_, 0, v___x_1992_);
v___x_1994_ = v___x_1989_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_a_1974_);
v___x_1994_ = v_reuseFailAlloc_2006_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_2000_; 
v___x_1995_ = lean_array_push(v_fst_1986_, v___x_1994_);
v___x_1996_ = lean_unsigned_to_nat(1u);
v___x_1997_ = lean_nat_add(v_snd_1979_, v___x_1996_);
lean_dec(v_snd_1979_);
v___x_1998_ = lean_nat_add(v_snd_1987_, v___x_1996_);
lean_dec(v_snd_1987_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 1, v___x_1998_);
lean_ctor_set(v___x_1967_, 0, v___x_1997_);
v___x_2000_ = v___x_1967_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v___x_1997_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2005_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_object* v___x_2001_; size_t v___x_2002_; size_t v___x_2003_; lean_object* v___x_2004_; 
v___x_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1995_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
v___x_2002_ = ((size_t)1ULL);
v___x_2003_ = lean_usize_add(v_i_1961_, v___x_2002_);
v___x_2004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v_original_1957_, v___x_1958_, v_edited_1955_, v___x_1956_, v_as_1959_, v_sz_1960_, v___x_2003_, v___x_2001_);
return v___x_2004_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4___boxed(lean_object* v_edited_2013_, lean_object* v___x_2014_, lean_object* v_original_2015_, lean_object* v___x_2016_, lean_object* v_as_2017_, lean_object* v_sz_2018_, lean_object* v_i_2019_, lean_object* v_b_2020_){
_start:
{
size_t v_sz_boxed_2021_; size_t v_i_boxed_2022_; lean_object* v_res_2023_; 
v_sz_boxed_2021_ = lean_unbox_usize(v_sz_2018_);
lean_dec(v_sz_2018_);
v_i_boxed_2022_ = lean_unbox_usize(v_i_2019_);
lean_dec(v_i_2019_);
v_res_2023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v_edited_2013_, v___x_2014_, v_original_2015_, v___x_2016_, v_as_2017_, v_sz_boxed_2021_, v_i_boxed_2022_, v_b_2020_);
lean_dec_ref(v_as_2017_);
lean_dec(v___x_2016_);
lean_dec_ref(v_original_2015_);
lean_dec(v___x_2014_);
lean_dec_ref(v_edited_2013_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(lean_object* v_a_2024_, lean_object* v_b_2025_){
_start:
{
lean_object* v_array_2026_; lean_object* v_start_2027_; lean_object* v_stop_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2041_; 
v_array_2026_ = lean_ctor_get(v_a_2024_, 0);
v_start_2027_ = lean_ctor_get(v_a_2024_, 1);
v_stop_2028_ = lean_ctor_get(v_a_2024_, 2);
v_isSharedCheck_2041_ = !lean_is_exclusive(v_a_2024_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2030_ = v_a_2024_;
v_isShared_2031_ = v_isSharedCheck_2041_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_stop_2028_);
lean_inc(v_start_2027_);
lean_inc(v_array_2026_);
lean_dec(v_a_2024_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2041_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
uint8_t v___x_2032_; 
v___x_2032_ = lean_nat_dec_lt(v_start_2027_, v_stop_2028_);
if (v___x_2032_ == 0)
{
lean_del_object(v___x_2030_);
lean_dec(v_stop_2028_);
lean_dec(v_start_2027_);
lean_dec_ref(v_array_2026_);
return v_b_2025_;
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2036_; 
v___x_2033_ = lean_unsigned_to_nat(1u);
v___x_2034_ = lean_nat_add(v_start_2027_, v___x_2033_);
lean_inc_ref(v_array_2026_);
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 1, v___x_2034_);
v___x_2036_ = v___x_2030_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_array_2026_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2034_);
lean_ctor_set(v_reuseFailAlloc_2040_, 2, v_stop_2028_);
v___x_2036_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = lean_array_fget(v_array_2026_, v_start_2027_);
lean_dec(v_start_2027_);
lean_dec_ref(v_array_2026_);
v___x_2038_ = lean_array_push(v_b_2025_, v___x_2037_);
v_a_2024_ = v___x_2036_;
v_b_2025_ = v___x_2038_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6(lean_object* v_left_2042_, lean_object* v_right_2043_, lean_object* v_i_2044_){
_start:
{
lean_object* v_start_2045_; lean_object* v_stop_2046_; lean_object* v___x_2047_; uint8_t v___x_2061_; 
v_start_2045_ = lean_ctor_get(v_left_2042_, 1);
v_stop_2046_ = lean_ctor_get(v_left_2042_, 2);
v___x_2047_ = lean_nat_sub(v_stop_2046_, v_start_2045_);
v___x_2061_ = lean_nat_dec_lt(v_i_2044_, v___x_2047_);
if (v___x_2061_ == 0)
{
goto v___jp_2048_;
}
else
{
lean_object* v_start_2062_; lean_object* v_stop_2063_; lean_object* v___x_2064_; uint8_t v___x_2065_; 
v_start_2062_ = lean_ctor_get(v_right_2043_, 1);
v_stop_2063_ = lean_ctor_get(v_right_2043_, 2);
v___x_2064_ = lean_nat_sub(v_stop_2063_, v_start_2062_);
v___x_2065_ = lean_nat_dec_lt(v_i_2044_, v___x_2064_);
if (v___x_2065_ == 0)
{
lean_dec(v___x_2064_);
goto v___jp_2048_;
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
v___x_2066_ = lean_nat_sub(v___x_2047_, v_i_2044_);
lean_dec(v___x_2047_);
v___x_2067_ = lean_unsigned_to_nat(1u);
v___x_2068_ = lean_nat_sub(v___x_2066_, v___x_2067_);
v___x_2069_ = l_Subarray_get___redArg(v_left_2042_, v___x_2068_);
lean_dec(v___x_2068_);
v___x_2070_ = lean_nat_sub(v___x_2064_, v_i_2044_);
lean_dec(v___x_2064_);
v___x_2071_ = lean_nat_sub(v___x_2070_, v___x_2067_);
v___x_2072_ = l_Subarray_get___redArg(v_right_2043_, v___x_2071_);
lean_dec(v___x_2071_);
v___x_2073_ = lean_string_dec_eq(v___x_2069_, v___x_2072_);
lean_dec(v___x_2072_);
lean_dec(v___x_2069_);
if (v___x_2073_ == 0)
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
lean_dec(v_i_2044_);
lean_inc_ref(v_left_2042_);
v___x_2074_ = l_Subarray_take___redArg(v_left_2042_, v___x_2066_);
v___x_2075_ = l_Subarray_take___redArg(v_right_2043_, v___x_2070_);
lean_dec(v___x_2070_);
v___x_2076_ = l_Subarray_drop___redArg(v_left_2042_, v___x_2066_);
lean_dec(v___x_2066_);
v___x_2077_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2078_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v___x_2076_, v___x_2077_);
v___x_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2075_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2074_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
return v___x_2080_;
}
else
{
lean_object* v___x_2081_; 
lean_dec(v___x_2070_);
lean_dec(v___x_2066_);
v___x_2081_ = lean_nat_add(v_i_2044_, v___x_2067_);
lean_dec(v_i_2044_);
v_i_2044_ = v___x_2081_;
goto _start;
}
}
}
v___jp_2048_:
{
lean_object* v_start_2049_; lean_object* v_stop_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v_start_2049_ = lean_ctor_get(v_right_2043_, 1);
v_stop_2050_ = lean_ctor_get(v_right_2043_, 2);
v___x_2051_ = lean_nat_sub(v___x_2047_, v_i_2044_);
lean_dec(v___x_2047_);
lean_inc_ref(v_left_2042_);
v___x_2052_ = l_Subarray_take___redArg(v_left_2042_, v___x_2051_);
v___x_2053_ = lean_nat_sub(v_stop_2050_, v_start_2049_);
v___x_2054_ = lean_nat_sub(v___x_2053_, v_i_2044_);
lean_dec(v_i_2044_);
lean_dec(v___x_2053_);
v___x_2055_ = l_Subarray_take___redArg(v_right_2043_, v___x_2054_);
lean_dec(v___x_2054_);
v___x_2056_ = l_Subarray_drop___redArg(v_left_2042_, v___x_2051_);
lean_dec(v___x_2051_);
v___x_2057_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2058_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v___x_2056_, v___x_2057_);
v___x_2059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2055_);
lean_ctor_set(v___x_2059_, 1, v___x_2058_);
v___x_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2052_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
return v___x_2060_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3(lean_object* v_left_2083_, lean_object* v_right_2084_){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
v___x_2085_ = lean_unsigned_to_nat(0u);
v___x_2086_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6(v_left_2083_, v_right_2084_, v___x_2085_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2_spec__4(lean_object* v_left_2087_, lean_object* v_right_2088_, lean_object* v_pref_2089_){
_start:
{
lean_object* v_start_2090_; lean_object* v_stop_2091_; lean_object* v_i_2092_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v_start_2090_ = lean_ctor_get(v_left_2087_, 1);
v_stop_2091_ = lean_ctor_get(v_left_2087_, 2);
v_i_2092_ = lean_array_get_size(v_pref_2089_);
v___x_2098_ = lean_nat_sub(v_stop_2091_, v_start_2090_);
v___x_2099_ = lean_nat_dec_lt(v_i_2092_, v___x_2098_);
lean_dec(v___x_2098_);
if (v___x_2099_ == 0)
{
goto v___jp_2093_;
}
else
{
lean_object* v_start_2100_; lean_object* v_stop_2101_; lean_object* v___x_2102_; uint8_t v___x_2103_; 
v_start_2100_ = lean_ctor_get(v_right_2088_, 1);
v_stop_2101_ = lean_ctor_get(v_right_2088_, 2);
v___x_2102_ = lean_nat_sub(v_stop_2101_, v_start_2100_);
v___x_2103_ = lean_nat_dec_lt(v_i_2092_, v___x_2102_);
lean_dec(v___x_2102_);
if (v___x_2103_ == 0)
{
goto v___jp_2093_;
}
else
{
lean_object* v___x_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v___x_2104_ = l_Subarray_get___redArg(v_left_2087_, v_i_2092_);
v___x_2105_ = l_Subarray_get___redArg(v_right_2088_, v_i_2092_);
v___x_2106_ = lean_string_dec_eq(v___x_2104_, v___x_2105_);
lean_dec(v___x_2105_);
if (v___x_2106_ == 0)
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
lean_dec(v___x_2104_);
v___x_2107_ = l_Subarray_drop___redArg(v_left_2087_, v_i_2092_);
v___x_2108_ = l_Subarray_drop___redArg(v_right_2088_, v_i_2092_);
v___x_2109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2107_);
lean_ctor_set(v___x_2109_, 1, v___x_2108_);
v___x_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2110_, 0, v_pref_2089_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
return v___x_2110_;
}
else
{
lean_object* v___x_2111_; 
v___x_2111_ = lean_array_push(v_pref_2089_, v___x_2104_);
v_pref_2089_ = v___x_2111_;
goto _start;
}
}
}
v___jp_2093_:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2094_ = l_Subarray_drop___redArg(v_left_2087_, v_i_2092_);
v___x_2095_ = l_Subarray_drop___redArg(v_right_2088_, v_i_2092_);
v___x_2096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2094_);
lean_ctor_set(v___x_2096_, 1, v___x_2095_);
v___x_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2097_, 0, v_pref_2089_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
return v___x_2097_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2(lean_object* v_left_2113_, lean_object* v_right_2114_){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2116_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2_spec__4(v_left_2113_, v_right_2114_, v___x_2115_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(lean_object* v_as_x27_2117_, lean_object* v_b_2118_){
_start:
{
if (lean_obj_tag(v_as_x27_2117_) == 0)
{
return v_b_2118_;
}
else
{
lean_object* v_head_2119_; lean_object* v_snd_2120_; lean_object* v_leftIndex_2121_; 
v_head_2119_ = lean_ctor_get(v_as_x27_2117_, 0);
v_snd_2120_ = lean_ctor_get(v_head_2119_, 1);
v_leftIndex_2121_ = lean_ctor_get(v_snd_2120_, 1);
if (lean_obj_tag(v_leftIndex_2121_) == 1)
{
lean_object* v_rightIndex_2122_; 
v_rightIndex_2122_ = lean_ctor_get(v_snd_2120_, 3);
if (lean_obj_tag(v_rightIndex_2122_) == 1)
{
if (lean_obj_tag(v_b_2118_) == 0)
{
lean_object* v_tail_2123_; lean_object* v_fst_2124_; lean_object* v_leftCount_2125_; lean_object* v_rightCount_2126_; lean_object* v_val_2127_; lean_object* v_val_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; 
v_tail_2123_ = lean_ctor_get(v_as_x27_2117_, 1);
v_fst_2124_ = lean_ctor_get(v_head_2119_, 0);
v_leftCount_2125_ = lean_ctor_get(v_snd_2120_, 0);
v_rightCount_2126_ = lean_ctor_get(v_snd_2120_, 2);
v_val_2127_ = lean_ctor_get(v_leftIndex_2121_, 0);
v_val_2128_ = lean_ctor_get(v_rightIndex_2122_, 0);
v___x_2129_ = lean_nat_add(v_leftCount_2125_, v_rightCount_2126_);
lean_inc(v_val_2128_);
lean_inc(v_val_2127_);
v___x_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2130_, 0, v_val_2127_);
lean_ctor_set(v___x_2130_, 1, v_val_2128_);
lean_inc(v_fst_2124_);
v___x_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2131_, 0, v_fst_2124_);
lean_ctor_set(v___x_2131_, 1, v___x_2130_);
v___x_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2129_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2132_);
v_as_x27_2117_ = v_tail_2123_;
v_b_2118_ = v___x_2133_;
goto _start;
}
else
{
lean_object* v_val_2135_; lean_object* v_tail_2136_; lean_object* v_fst_2137_; lean_object* v_leftCount_2138_; lean_object* v_rightCount_2139_; lean_object* v_val_2140_; lean_object* v_val_2141_; lean_object* v_fst_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2163_; 
v_val_2135_ = lean_ctor_get(v_b_2118_, 0);
lean_inc(v_val_2135_);
v_tail_2136_ = lean_ctor_get(v_as_x27_2117_, 1);
v_fst_2137_ = lean_ctor_get(v_head_2119_, 0);
v_leftCount_2138_ = lean_ctor_get(v_snd_2120_, 0);
v_rightCount_2139_ = lean_ctor_get(v_snd_2120_, 2);
v_val_2140_ = lean_ctor_get(v_leftIndex_2121_, 0);
v_val_2141_ = lean_ctor_get(v_rightIndex_2122_, 0);
v_fst_2142_ = lean_ctor_get(v_val_2135_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_val_2135_);
if (v_isSharedCheck_2163_ == 0)
{
lean_object* v_unused_2164_; 
v_unused_2164_ = lean_ctor_get(v_val_2135_, 1);
lean_dec(v_unused_2164_);
v___x_2144_ = v_val_2135_;
v_isShared_2145_ = v_isSharedCheck_2163_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_fst_2142_);
lean_dec(v_val_2135_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2163_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2146_; uint8_t v___x_2147_; 
v___x_2146_ = lean_nat_add(v_leftCount_2138_, v_rightCount_2139_);
v___x_2147_ = lean_nat_dec_lt(v___x_2146_, v_fst_2142_);
lean_dec(v_fst_2142_);
if (v___x_2147_ == 0)
{
lean_dec(v___x_2146_);
lean_del_object(v___x_2144_);
v_as_x27_2117_ = v_tail_2136_;
goto _start;
}
else
{
lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2161_; 
v_isSharedCheck_2161_ = !lean_is_exclusive(v_b_2118_);
if (v_isSharedCheck_2161_ == 0)
{
lean_object* v_unused_2162_; 
v_unused_2162_ = lean_ctor_get(v_b_2118_, 0);
lean_dec(v_unused_2162_);
v___x_2150_ = v_b_2118_;
v_isShared_2151_ = v_isSharedCheck_2161_;
goto v_resetjp_2149_;
}
else
{
lean_dec(v_b_2118_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2161_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
lean_inc(v_val_2141_);
lean_inc(v_val_2140_);
if (v_isShared_2145_ == 0)
{
lean_ctor_set(v___x_2144_, 1, v_val_2141_);
lean_ctor_set(v___x_2144_, 0, v_val_2140_);
v___x_2153_ = v___x_2144_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_val_2140_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_val_2141_);
v___x_2153_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2157_; 
lean_inc(v_fst_2137_);
v___x_2154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2154_, 0, v_fst_2137_);
lean_ctor_set(v___x_2154_, 1, v___x_2153_);
v___x_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2146_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 0, v___x_2155_);
v___x_2157_ = v___x_2150_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2155_);
v___x_2157_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
v_as_x27_2117_ = v_tail_2136_;
v_b_2118_ = v___x_2157_;
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
lean_object* v_tail_2165_; 
v_tail_2165_ = lean_ctor_get(v_as_x27_2117_, 1);
v_as_x27_2117_ = v_tail_2165_;
goto _start;
}
}
else
{
lean_object* v_tail_2167_; 
v_tail_2167_ = lean_ctor_get(v_as_x27_2117_, 1);
v_as_x27_2117_ = v_tail_2167_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2169_, lean_object* v_b_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(v_as_x27_2169_, v_b_2170_);
lean_dec(v_as_x27_2169_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(lean_object* v_a_2172_, lean_object* v_b_2173_, lean_object* v_x_2174_){
_start:
{
if (lean_obj_tag(v_x_2174_) == 0)
{
lean_dec(v_b_2173_);
lean_dec_ref(v_a_2172_);
return v_x_2174_;
}
else
{
lean_object* v_key_2175_; lean_object* v_value_2176_; lean_object* v_tail_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2189_; 
v_key_2175_ = lean_ctor_get(v_x_2174_, 0);
v_value_2176_ = lean_ctor_get(v_x_2174_, 1);
v_tail_2177_ = lean_ctor_get(v_x_2174_, 2);
v_isSharedCheck_2189_ = !lean_is_exclusive(v_x_2174_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2179_ = v_x_2174_;
v_isShared_2180_ = v_isSharedCheck_2189_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_tail_2177_);
lean_inc(v_value_2176_);
lean_inc(v_key_2175_);
lean_dec(v_x_2174_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2189_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
uint8_t v___x_2181_; 
v___x_2181_ = lean_string_dec_eq(v_key_2175_, v_a_2172_);
if (v___x_2181_ == 0)
{
lean_object* v___x_2182_; lean_object* v___x_2184_; 
v___x_2182_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(v_a_2172_, v_b_2173_, v_tail_2177_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 2, v___x_2182_);
v___x_2184_ = v___x_2179_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_key_2175_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v_value_2176_);
lean_ctor_set(v_reuseFailAlloc_2185_, 2, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
else
{
lean_object* v___x_2187_; 
lean_dec(v_value_2176_);
lean_dec(v_key_2175_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 1, v_b_2173_);
lean_ctor_set(v___x_2179_, 0, v_a_2172_);
v___x_2187_ = v___x_2179_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2172_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_b_2173_);
lean_ctor_set(v_reuseFailAlloc_2188_, 2, v_tail_2177_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(lean_object* v_a_2190_, lean_object* v_x_2191_){
_start:
{
if (lean_obj_tag(v_x_2191_) == 0)
{
uint8_t v___x_2192_; 
v___x_2192_ = 0;
return v___x_2192_;
}
else
{
lean_object* v_key_2193_; lean_object* v_tail_2194_; uint8_t v___x_2195_; 
v_key_2193_ = lean_ctor_get(v_x_2191_, 0);
v_tail_2194_ = lean_ctor_get(v_x_2191_, 2);
v___x_2195_ = lean_string_dec_eq(v_key_2193_, v_a_2190_);
if (v___x_2195_ == 0)
{
v_x_2191_ = v_tail_2194_;
goto _start;
}
else
{
return v___x_2195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg___boxed(lean_object* v_a_2197_, lean_object* v_x_2198_){
_start:
{
uint8_t v_res_2199_; lean_object* v_r_2200_; 
v_res_2199_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(v_a_2197_, v_x_2198_);
lean_dec(v_x_2198_);
lean_dec_ref(v_a_2197_);
v_r_2200_ = lean_box(v_res_2199_);
return v_r_2200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29___redArg(lean_object* v_x_2201_, lean_object* v_x_2202_){
_start:
{
if (lean_obj_tag(v_x_2202_) == 0)
{
return v_x_2201_;
}
else
{
lean_object* v_key_2203_; lean_object* v_value_2204_; lean_object* v_tail_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2228_; 
v_key_2203_ = lean_ctor_get(v_x_2202_, 0);
v_value_2204_ = lean_ctor_get(v_x_2202_, 1);
v_tail_2205_ = lean_ctor_get(v_x_2202_, 2);
v_isSharedCheck_2228_ = !lean_is_exclusive(v_x_2202_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2207_ = v_x_2202_;
v_isShared_2208_ = v_isSharedCheck_2228_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_tail_2205_);
lean_inc(v_value_2204_);
lean_inc(v_key_2203_);
lean_dec(v_x_2202_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2228_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2209_; uint64_t v___x_2210_; uint64_t v___x_2211_; uint64_t v___x_2212_; uint64_t v_fold_2213_; uint64_t v___x_2214_; uint64_t v___x_2215_; uint64_t v___x_2216_; size_t v___x_2217_; size_t v___x_2218_; size_t v___x_2219_; size_t v___x_2220_; size_t v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2224_; 
v___x_2209_ = lean_array_get_size(v_x_2201_);
v___x_2210_ = lean_string_hash(v_key_2203_);
v___x_2211_ = 32ULL;
v___x_2212_ = lean_uint64_shift_right(v___x_2210_, v___x_2211_);
v_fold_2213_ = lean_uint64_xor(v___x_2210_, v___x_2212_);
v___x_2214_ = 16ULL;
v___x_2215_ = lean_uint64_shift_right(v_fold_2213_, v___x_2214_);
v___x_2216_ = lean_uint64_xor(v_fold_2213_, v___x_2215_);
v___x_2217_ = lean_uint64_to_usize(v___x_2216_);
v___x_2218_ = lean_usize_of_nat(v___x_2209_);
v___x_2219_ = ((size_t)1ULL);
v___x_2220_ = lean_usize_sub(v___x_2218_, v___x_2219_);
v___x_2221_ = lean_usize_land(v___x_2217_, v___x_2220_);
v___x_2222_ = lean_array_uget_borrowed(v_x_2201_, v___x_2221_);
lean_inc(v___x_2222_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 2, v___x_2222_);
v___x_2224_ = v___x_2207_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_key_2203_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_value_2204_);
lean_ctor_set(v_reuseFailAlloc_2227_, 2, v___x_2222_);
v___x_2224_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2225_; 
v___x_2225_ = lean_array_uset(v_x_2201_, v___x_2221_, v___x_2224_);
v_x_2201_ = v___x_2225_;
v_x_2202_ = v_tail_2205_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28___redArg(lean_object* v_i_2229_, lean_object* v_source_2230_, lean_object* v_target_2231_){
_start:
{
lean_object* v___x_2232_; uint8_t v___x_2233_; 
v___x_2232_ = lean_array_get_size(v_source_2230_);
v___x_2233_ = lean_nat_dec_lt(v_i_2229_, v___x_2232_);
if (v___x_2233_ == 0)
{
lean_dec_ref(v_source_2230_);
lean_dec(v_i_2229_);
return v_target_2231_;
}
else
{
lean_object* v_es_2234_; lean_object* v___x_2235_; lean_object* v_source_2236_; lean_object* v_target_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v_es_2234_ = lean_array_fget(v_source_2230_, v_i_2229_);
v___x_2235_ = lean_box(0);
v_source_2236_ = lean_array_fset(v_source_2230_, v_i_2229_, v___x_2235_);
v_target_2237_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29___redArg(v_target_2231_, v_es_2234_);
v___x_2238_ = lean_unsigned_to_nat(1u);
v___x_2239_ = lean_nat_add(v_i_2229_, v___x_2238_);
lean_dec(v_i_2229_);
v_i_2229_ = v___x_2239_;
v_source_2230_ = v_source_2236_;
v_target_2231_ = v_target_2237_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23___redArg(lean_object* v_data_2241_){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v_nbuckets_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2242_ = lean_array_get_size(v_data_2241_);
v___x_2243_ = lean_unsigned_to_nat(2u);
v_nbuckets_2244_ = lean_nat_mul(v___x_2242_, v___x_2243_);
v___x_2245_ = lean_unsigned_to_nat(0u);
v___x_2246_ = lean_box(0);
v___x_2247_ = lean_mk_array(v_nbuckets_2244_, v___x_2246_);
v___x_2248_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28___redArg(v___x_2245_, v_data_2241_, v___x_2247_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(lean_object* v_m_2249_, lean_object* v_a_2250_, lean_object* v_b_2251_){
_start:
{
lean_object* v_size_2252_; lean_object* v_buckets_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2296_; 
v_size_2252_ = lean_ctor_get(v_m_2249_, 0);
v_buckets_2253_ = lean_ctor_get(v_m_2249_, 1);
v_isSharedCheck_2296_ = !lean_is_exclusive(v_m_2249_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2255_ = v_m_2249_;
v_isShared_2256_ = v_isSharedCheck_2296_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_buckets_2253_);
lean_inc(v_size_2252_);
lean_dec(v_m_2249_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2296_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2257_; uint64_t v___x_2258_; uint64_t v___x_2259_; uint64_t v___x_2260_; uint64_t v_fold_2261_; uint64_t v___x_2262_; uint64_t v___x_2263_; uint64_t v___x_2264_; size_t v___x_2265_; size_t v___x_2266_; size_t v___x_2267_; size_t v___x_2268_; size_t v___x_2269_; lean_object* v_bkt_2270_; uint8_t v___x_2271_; 
v___x_2257_ = lean_array_get_size(v_buckets_2253_);
v___x_2258_ = lean_string_hash(v_a_2250_);
v___x_2259_ = 32ULL;
v___x_2260_ = lean_uint64_shift_right(v___x_2258_, v___x_2259_);
v_fold_2261_ = lean_uint64_xor(v___x_2258_, v___x_2260_);
v___x_2262_ = 16ULL;
v___x_2263_ = lean_uint64_shift_right(v_fold_2261_, v___x_2262_);
v___x_2264_ = lean_uint64_xor(v_fold_2261_, v___x_2263_);
v___x_2265_ = lean_uint64_to_usize(v___x_2264_);
v___x_2266_ = lean_usize_of_nat(v___x_2257_);
v___x_2267_ = ((size_t)1ULL);
v___x_2268_ = lean_usize_sub(v___x_2266_, v___x_2267_);
v___x_2269_ = lean_usize_land(v___x_2265_, v___x_2268_);
v_bkt_2270_ = lean_array_uget_borrowed(v_buckets_2253_, v___x_2269_);
v___x_2271_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(v_a_2250_, v_bkt_2270_);
if (v___x_2271_ == 0)
{
lean_object* v___x_2272_; lean_object* v_size_x27_2273_; lean_object* v___x_2274_; lean_object* v_buckets_x27_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; uint8_t v___x_2281_; 
v___x_2272_ = lean_unsigned_to_nat(1u);
v_size_x27_2273_ = lean_nat_add(v_size_2252_, v___x_2272_);
lean_dec(v_size_2252_);
lean_inc(v_bkt_2270_);
v___x_2274_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2274_, 0, v_a_2250_);
lean_ctor_set(v___x_2274_, 1, v_b_2251_);
lean_ctor_set(v___x_2274_, 2, v_bkt_2270_);
v_buckets_x27_2275_ = lean_array_uset(v_buckets_2253_, v___x_2269_, v___x_2274_);
v___x_2276_ = lean_unsigned_to_nat(4u);
v___x_2277_ = lean_nat_mul(v_size_x27_2273_, v___x_2276_);
v___x_2278_ = lean_unsigned_to_nat(3u);
v___x_2279_ = lean_nat_div(v___x_2277_, v___x_2278_);
lean_dec(v___x_2277_);
v___x_2280_ = lean_array_get_size(v_buckets_x27_2275_);
v___x_2281_ = lean_nat_dec_le(v___x_2279_, v___x_2280_);
lean_dec(v___x_2279_);
if (v___x_2281_ == 0)
{
lean_object* v_val_2282_; lean_object* v___x_2284_; 
v_val_2282_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23___redArg(v_buckets_x27_2275_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 1, v_val_2282_);
lean_ctor_set(v___x_2255_, 0, v_size_x27_2273_);
v___x_2284_ = v___x_2255_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_size_x27_2273_);
lean_ctor_set(v_reuseFailAlloc_2285_, 1, v_val_2282_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
else
{
lean_object* v___x_2287_; 
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 1, v_buckets_x27_2275_);
lean_ctor_set(v___x_2255_, 0, v_size_x27_2273_);
v___x_2287_ = v___x_2255_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_size_x27_2273_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v_buckets_x27_2275_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
else
{
lean_object* v___x_2289_; lean_object* v_buckets_x27_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2294_; 
lean_inc(v_bkt_2270_);
v___x_2289_ = lean_box(0);
v_buckets_x27_2290_ = lean_array_uset(v_buckets_2253_, v___x_2269_, v___x_2289_);
v___x_2291_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(v_a_2250_, v_b_2251_, v_bkt_2270_);
v___x_2292_ = lean_array_uset(v_buckets_x27_2290_, v___x_2269_, v___x_2291_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 1, v___x_2292_);
v___x_2294_ = v___x_2255_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_size_2252_);
lean_ctor_set(v_reuseFailAlloc_2295_, 1, v___x_2292_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(lean_object* v_a_2297_, lean_object* v_x_2298_){
_start:
{
if (lean_obj_tag(v_x_2298_) == 0)
{
lean_object* v___x_2299_; 
v___x_2299_ = lean_box(0);
return v___x_2299_;
}
else
{
lean_object* v_key_2300_; lean_object* v_value_2301_; lean_object* v_tail_2302_; uint8_t v___x_2303_; 
v_key_2300_ = lean_ctor_get(v_x_2298_, 0);
v_value_2301_ = lean_ctor_get(v_x_2298_, 1);
v_tail_2302_ = lean_ctor_get(v_x_2298_, 2);
v___x_2303_ = lean_string_dec_eq(v_key_2300_, v_a_2297_);
if (v___x_2303_ == 0)
{
v_x_2298_ = v_tail_2302_;
goto _start;
}
else
{
lean_object* v___x_2305_; 
lean_inc(v_value_2301_);
v___x_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2305_, 0, v_value_2301_);
return v___x_2305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg___boxed(lean_object* v_a_2306_, lean_object* v_x_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(v_a_2306_, v_x_2307_);
lean_dec(v_x_2307_);
lean_dec_ref(v_a_2306_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(lean_object* v_m_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v_buckets_2311_; lean_object* v___x_2312_; uint64_t v___x_2313_; uint64_t v___x_2314_; uint64_t v___x_2315_; uint64_t v_fold_2316_; uint64_t v___x_2317_; uint64_t v___x_2318_; uint64_t v___x_2319_; size_t v___x_2320_; size_t v___x_2321_; size_t v___x_2322_; size_t v___x_2323_; size_t v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v_buckets_2311_ = lean_ctor_get(v_m_2309_, 1);
v___x_2312_ = lean_array_get_size(v_buckets_2311_);
v___x_2313_ = lean_string_hash(v_a_2310_);
v___x_2314_ = 32ULL;
v___x_2315_ = lean_uint64_shift_right(v___x_2313_, v___x_2314_);
v_fold_2316_ = lean_uint64_xor(v___x_2313_, v___x_2315_);
v___x_2317_ = 16ULL;
v___x_2318_ = lean_uint64_shift_right(v_fold_2316_, v___x_2317_);
v___x_2319_ = lean_uint64_xor(v_fold_2316_, v___x_2318_);
v___x_2320_ = lean_uint64_to_usize(v___x_2319_);
v___x_2321_ = lean_usize_of_nat(v___x_2312_);
v___x_2322_ = ((size_t)1ULL);
v___x_2323_ = lean_usize_sub(v___x_2321_, v___x_2322_);
v___x_2324_ = lean_usize_land(v___x_2320_, v___x_2323_);
v___x_2325_ = lean_array_uget_borrowed(v_buckets_2311_, v___x_2324_);
v___x_2326_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(v_a_2310_, v___x_2325_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg___boxed(lean_object* v_m_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_m_2327_, v_a_2328_);
lean_dec_ref(v_a_2328_);
lean_dec_ref(v_m_2327_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(lean_object* v_histogram_2330_, lean_object* v_index_2331_, lean_object* v_val_2332_){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_histogram_2330_, v_val_2332_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2334_ = lean_unsigned_to_nat(1u);
v___x_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2335_, 0, v_index_2331_);
v___x_2336_ = lean_unsigned_to_nat(0u);
v___x_2337_ = lean_box(0);
v___x_2338_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2334_);
lean_ctor_set(v___x_2338_, 1, v___x_2335_);
lean_ctor_set(v___x_2338_, 2, v___x_2336_);
lean_ctor_set(v___x_2338_, 3, v___x_2337_);
v___x_2339_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2330_, v_val_2332_, v___x_2338_);
return v___x_2339_;
}
else
{
lean_object* v_val_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2361_; 
v_val_2340_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2342_ = v___x_2333_;
v_isShared_2343_ = v_isSharedCheck_2361_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_val_2340_);
lean_dec(v___x_2333_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2361_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v_leftCount_2344_; lean_object* v_rightCount_2345_; lean_object* v_rightIndex_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2359_; 
v_leftCount_2344_ = lean_ctor_get(v_val_2340_, 0);
v_rightCount_2345_ = lean_ctor_get(v_val_2340_, 2);
v_rightIndex_2346_ = lean_ctor_get(v_val_2340_, 3);
v_isSharedCheck_2359_ = !lean_is_exclusive(v_val_2340_);
if (v_isSharedCheck_2359_ == 0)
{
lean_object* v_unused_2360_; 
v_unused_2360_ = lean_ctor_get(v_val_2340_, 1);
lean_dec(v_unused_2360_);
v___x_2348_ = v_val_2340_;
v_isShared_2349_ = v_isSharedCheck_2359_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_rightIndex_2346_);
lean_inc(v_rightCount_2345_);
lean_inc(v_leftCount_2344_);
lean_dec(v_val_2340_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2359_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2353_; 
v___x_2350_ = lean_unsigned_to_nat(1u);
v___x_2351_ = lean_nat_add(v_leftCount_2344_, v___x_2350_);
lean_dec(v_leftCount_2344_);
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v_index_2331_);
v___x_2353_ = v___x_2342_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_index_2331_);
v___x_2353_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
lean_object* v___x_2355_; 
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 1, v___x_2353_);
lean_ctor_set(v___x_2348_, 0, v___x_2351_);
v___x_2355_ = v___x_2348_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2351_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v___x_2353_);
lean_ctor_set(v_reuseFailAlloc_2357_, 2, v_rightCount_2345_);
lean_ctor_set(v_reuseFailAlloc_2357_, 3, v_rightIndex_2346_);
v___x_2355_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
lean_object* v___x_2356_; 
v___x_2356_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2330_, v_val_2332_, v___x_2355_);
return v___x_2356_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(lean_object* v_upperBound_2362_, lean_object* v_fst_2363_, lean_object* v___x_2364_, lean_object* v_fst_2365_, lean_object* v_a_2366_, lean_object* v_b_2367_){
_start:
{
uint8_t v___x_2368_; 
v___x_2368_ = lean_nat_dec_lt(v_a_2366_, v_upperBound_2362_);
if (v___x_2368_ == 0)
{
lean_dec(v_a_2366_);
return v_b_2367_;
}
else
{
lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2369_ = l_Subarray_get___redArg(v_fst_2365_, v_a_2366_);
lean_inc(v_a_2366_);
v___x_2370_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(v_b_2367_, v_a_2366_, v___x_2369_);
v___x_2371_ = lean_unsigned_to_nat(1u);
v___x_2372_ = lean_nat_add(v_a_2366_, v___x_2371_);
lean_dec(v_a_2366_);
v_a_2366_ = v___x_2372_;
v_b_2367_ = v___x_2370_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_upperBound_2374_, lean_object* v_fst_2375_, lean_object* v___x_2376_, lean_object* v_fst_2377_, lean_object* v_a_2378_, lean_object* v_b_2379_){
_start:
{
lean_object* v_res_2380_; 
v_res_2380_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(v_upperBound_2374_, v_fst_2375_, v___x_2376_, v_fst_2377_, v_a_2378_, v_b_2379_);
lean_dec_ref(v_fst_2377_);
lean_dec(v___x_2376_);
lean_dec_ref(v_fst_2375_);
lean_dec(v_upperBound_2374_);
return v_res_2380_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(lean_object* v_x_2381_, lean_object* v_x_2382_){
_start:
{
if (lean_obj_tag(v_x_2382_) == 0)
{
lean_inc(v_x_2381_);
return v_x_2381_;
}
else
{
lean_object* v_key_2383_; lean_object* v_value_2384_; lean_object* v_tail_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v_key_2383_ = lean_ctor_get(v_x_2382_, 0);
v_value_2384_ = lean_ctor_get(v_x_2382_, 1);
v_tail_2385_ = lean_ctor_get(v_x_2382_, 2);
v___x_2386_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(v_x_2381_, v_tail_2385_);
lean_inc(v_value_2384_);
lean_inc(v_key_2383_);
v___x_2387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2387_, 0, v_key_2383_);
lean_ctor_set(v___x_2387_, 1, v_value_2384_);
v___x_2388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
lean_ctor_set(v___x_2388_, 1, v___x_2386_);
return v___x_2388_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5___boxed(lean_object* v_x_2389_, lean_object* v_x_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(v_x_2389_, v_x_2390_);
lean_dec(v_x_2390_);
lean_dec(v_x_2389_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(lean_object* v_as_2392_, size_t v_i_2393_, size_t v_stop_2394_, lean_object* v_b_2395_){
_start:
{
uint8_t v___x_2396_; 
v___x_2396_ = lean_usize_dec_eq(v_i_2393_, v_stop_2394_);
if (v___x_2396_ == 0)
{
size_t v___x_2397_; size_t v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; 
v___x_2397_ = ((size_t)1ULL);
v___x_2398_ = lean_usize_sub(v_i_2393_, v___x_2397_);
v___x_2399_ = lean_array_uget_borrowed(v_as_2392_, v___x_2398_);
v___x_2400_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(v_b_2395_, v___x_2399_);
lean_dec(v_b_2395_);
v_i_2393_ = v___x_2398_;
v_b_2395_ = v___x_2400_;
goto _start;
}
else
{
return v_b_2395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6___boxed(lean_object* v_as_2402_, lean_object* v_i_2403_, lean_object* v_stop_2404_, lean_object* v_b_2405_){
_start:
{
size_t v_i_boxed_2406_; size_t v_stop_boxed_2407_; lean_object* v_res_2408_; 
v_i_boxed_2406_ = lean_unbox_usize(v_i_2403_);
lean_dec(v_i_2403_);
v_stop_boxed_2407_ = lean_unbox_usize(v_stop_2404_);
lean_dec(v_stop_2404_);
v_res_2408_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(v_as_2402_, v_i_boxed_2406_, v_stop_boxed_2407_, v_b_2405_);
lean_dec_ref(v_as_2402_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(lean_object* v_histogram_2409_, lean_object* v_index_2410_, lean_object* v_val_2411_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_histogram_2409_, v_val_2411_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2413_ = lean_unsigned_to_nat(0u);
v___x_2414_ = lean_box(0);
v___x_2415_ = lean_unsigned_to_nat(1u);
v___x_2416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2416_, 0, v_index_2410_);
v___x_2417_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2417_, 0, v___x_2413_);
lean_ctor_set(v___x_2417_, 1, v___x_2414_);
lean_ctor_set(v___x_2417_, 2, v___x_2415_);
lean_ctor_set(v___x_2417_, 3, v___x_2416_);
v___x_2418_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2409_, v_val_2411_, v___x_2417_);
return v___x_2418_;
}
else
{
lean_object* v_val_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2440_; 
v_val_2419_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2421_ = v___x_2412_;
v_isShared_2422_ = v_isSharedCheck_2440_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_val_2419_);
lean_dec(v___x_2412_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2440_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v_leftCount_2423_; lean_object* v_leftIndex_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2437_; 
v_leftCount_2423_ = lean_ctor_get(v_val_2419_, 0);
v_leftIndex_2424_ = lean_ctor_get(v_val_2419_, 1);
v_isSharedCheck_2437_ = !lean_is_exclusive(v_val_2419_);
if (v_isSharedCheck_2437_ == 0)
{
lean_object* v_unused_2438_; lean_object* v_unused_2439_; 
v_unused_2438_ = lean_ctor_get(v_val_2419_, 3);
lean_dec(v_unused_2438_);
v_unused_2439_ = lean_ctor_get(v_val_2419_, 2);
lean_dec(v_unused_2439_);
v___x_2426_ = v_val_2419_;
v_isShared_2427_ = v_isSharedCheck_2437_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_leftIndex_2424_);
lean_inc(v_leftCount_2423_);
lean_dec(v_val_2419_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2437_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2431_; 
v___x_2428_ = lean_unsigned_to_nat(1u);
v___x_2429_ = lean_nat_add(v_leftCount_2423_, v___x_2428_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v_index_2410_);
v___x_2431_ = v___x_2421_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_index_2410_);
v___x_2431_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
lean_object* v___x_2433_; 
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 3, v___x_2431_);
lean_ctor_set(v___x_2426_, 2, v___x_2429_);
v___x_2433_ = v___x_2426_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_leftCount_2423_);
lean_ctor_set(v_reuseFailAlloc_2435_, 1, v_leftIndex_2424_);
lean_ctor_set(v_reuseFailAlloc_2435_, 2, v___x_2429_);
lean_ctor_set(v_reuseFailAlloc_2435_, 3, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2409_, v_val_2411_, v___x_2433_);
return v___x_2434_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(lean_object* v_upperBound_2441_, lean_object* v___x_2442_, lean_object* v_fst_2443_, lean_object* v___x_2444_, lean_object* v_a_2445_, lean_object* v_b_2446_){
_start:
{
uint8_t v___x_2447_; 
v___x_2447_ = lean_nat_dec_lt(v_a_2445_, v_upperBound_2441_);
if (v___x_2447_ == 0)
{
lean_dec(v_a_2445_);
return v_b_2446_;
}
else
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2448_ = l_Subarray_get___redArg(v_fst_2443_, v_a_2445_);
lean_inc(v_a_2445_);
v___x_2449_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(v_b_2446_, v_a_2445_, v___x_2448_);
v___x_2450_ = lean_unsigned_to_nat(1u);
v___x_2451_ = lean_nat_add(v_a_2445_, v___x_2450_);
lean_dec(v_a_2445_);
v_a_2445_ = v___x_2451_;
v_b_2446_ = v___x_2449_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg___boxed(lean_object* v_upperBound_2453_, lean_object* v___x_2454_, lean_object* v_fst_2455_, lean_object* v___x_2456_, lean_object* v_a_2457_, lean_object* v_b_2458_){
_start:
{
lean_object* v_res_2459_; 
v_res_2459_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(v_upperBound_2453_, v___x_2454_, v_fst_2455_, v___x_2456_, v_a_2457_, v_b_2458_);
lean_dec(v___x_2456_);
lean_dec_ref(v_fst_2455_);
lean_dec(v___x_2454_);
lean_dec(v_upperBound_2453_);
return v_res_2459_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2460_ = lean_box(0);
v___x_2461_ = lean_unsigned_to_nat(16u);
v___x_2462_ = lean_mk_array(v___x_2461_, v___x_2460_);
return v___x_2462_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v_hist_2465_; 
v___x_2463_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0);
v___x_2464_ = lean_unsigned_to_nat(0u);
v_hist_2465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_2465_, 0, v___x_2464_);
lean_ctor_set(v_hist_2465_, 1, v___x_2463_);
return v_hist_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(lean_object* v_left_2466_, lean_object* v_right_2467_){
_start:
{
lean_object* v___x_2468_; lean_object* v_snd_2469_; lean_object* v_fst_2470_; lean_object* v_fst_2471_; lean_object* v_snd_2472_; lean_object* v___x_2473_; lean_object* v_snd_2474_; lean_object* v_fst_2475_; lean_object* v_fst_2476_; lean_object* v_snd_2477_; lean_object* v_start_2478_; lean_object* v_stop_2479_; lean_object* v___x_2480_; lean_object* v_hist_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v_start_2484_; lean_object* v_stop_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v_buckets_2488_; lean_object* v___x_2489_; lean_object* v___y_2491_; lean_object* v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
v___x_2468_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2(v_left_2466_, v_right_2467_);
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
v___x_2473_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3(v_fst_2471_, v_snd_2472_);
v_snd_2474_ = lean_ctor_get(v___x_2473_, 1);
lean_inc(v_snd_2474_);
v_fst_2475_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_fst_2475_);
lean_dec_ref(v___x_2473_);
v_fst_2476_ = lean_ctor_get(v_snd_2474_, 0);
lean_inc(v_fst_2476_);
v_snd_2477_ = lean_ctor_get(v_snd_2474_, 1);
lean_inc(v_snd_2477_);
lean_dec(v_snd_2474_);
v_start_2478_ = lean_ctor_get(v_fst_2475_, 1);
v_stop_2479_ = lean_ctor_get(v_fst_2475_, 2);
v___x_2480_ = lean_unsigned_to_nat(0u);
v_hist_2481_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1);
v___x_2482_ = lean_nat_sub(v_stop_2479_, v_start_2478_);
v___x_2483_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(v___x_2482_, v_fst_2476_, v___x_2482_, v_fst_2475_, v___x_2480_, v_hist_2481_);
v_start_2484_ = lean_ctor_get(v_fst_2476_, 1);
v_stop_2485_ = lean_ctor_get(v_fst_2476_, 2);
v___x_2486_ = lean_nat_sub(v_stop_2485_, v_start_2484_);
v___x_2487_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(v___x_2486_, v___x_2486_, v_fst_2476_, v___x_2482_, v___x_2480_, v___x_2483_);
lean_dec(v___x_2482_);
lean_dec(v___x_2486_);
v_buckets_2488_ = lean_ctor_get(v___x_2487_, 1);
lean_inc_ref(v_buckets_2488_);
lean_dec_ref(v___x_2487_);
v___x_2489_ = lean_box(0);
v___x_2517_ = lean_box(0);
v___x_2518_ = lean_array_get_size(v_buckets_2488_);
v___x_2519_ = lean_nat_dec_lt(v___x_2480_, v___x_2518_);
if (v___x_2519_ == 0)
{
lean_dec_ref(v_buckets_2488_);
v___y_2491_ = v___x_2517_;
goto v___jp_2490_;
}
else
{
size_t v___x_2520_; size_t v___x_2521_; lean_object* v___x_2522_; 
v___x_2520_ = lean_usize_of_nat(v___x_2518_);
v___x_2521_ = ((size_t)0ULL);
v___x_2522_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(v_buckets_2488_, v___x_2520_, v___x_2521_, v___x_2517_);
lean_dec_ref(v_buckets_2488_);
v___y_2491_ = v___x_2522_;
goto v___jp_2490_;
}
v___jp_2490_:
{
lean_object* v___x_2492_; 
v___x_2492_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(v___y_2491_, v___x_2489_);
lean_dec(v___y_2491_);
if (lean_obj_tag(v___x_2492_) == 1)
{
lean_object* v_val_2493_; lean_object* v_snd_2494_; lean_object* v_snd_2495_; lean_object* v_fst_2496_; lean_object* v_fst_2497_; lean_object* v_snd_2498_; lean_object* v___x_2499_; lean_object* v_fst_2500_; lean_object* v_snd_2501_; lean_object* v___x_2502_; lean_object* v_fst_2503_; lean_object* v_snd_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v_val_2493_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_val_2493_);
lean_dec_ref_known(v___x_2492_, 1);
v_snd_2494_ = lean_ctor_get(v_val_2493_, 1);
lean_inc(v_snd_2494_);
lean_dec(v_val_2493_);
v_snd_2495_ = lean_ctor_get(v_snd_2494_, 1);
lean_inc(v_snd_2495_);
v_fst_2496_ = lean_ctor_get(v_snd_2494_, 0);
lean_inc(v_fst_2496_);
lean_dec(v_snd_2494_);
v_fst_2497_ = lean_ctor_get(v_snd_2495_, 0);
lean_inc(v_fst_2497_);
v_snd_2498_ = lean_ctor_get(v_snd_2495_, 1);
lean_inc(v_snd_2498_);
lean_dec(v_snd_2495_);
v___x_2499_ = l_Subarray_split___redArg(v_fst_2475_, v_fst_2497_);
lean_dec(v_fst_2497_);
v_fst_2500_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_fst_2500_);
v_snd_2501_ = lean_ctor_get(v___x_2499_, 1);
lean_inc(v_snd_2501_);
lean_dec_ref(v___x_2499_);
v___x_2502_ = l_Subarray_split___redArg(v_fst_2476_, v_snd_2498_);
lean_dec(v_snd_2498_);
v_fst_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_fst_2503_);
v_snd_2504_ = lean_ctor_get(v___x_2502_, 1);
lean_inc(v_snd_2504_);
lean_dec_ref(v___x_2502_);
v___x_2505_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v_fst_2500_, v_fst_2503_);
v___x_2506_ = l_Array_append___redArg(v_fst_2470_, v___x_2505_);
lean_dec_ref(v___x_2505_);
v___x_2507_ = lean_unsigned_to_nat(1u);
v___x_2508_ = lean_mk_empty_array_with_capacity(v___x_2507_);
v___x_2509_ = lean_array_push(v___x_2508_, v_fst_2496_);
v___x_2510_ = l_Array_append___redArg(v___x_2506_, v___x_2509_);
lean_dec_ref(v___x_2509_);
v___x_2511_ = l_Subarray_drop___redArg(v_snd_2501_, v___x_2507_);
v___x_2512_ = l_Subarray_drop___redArg(v_snd_2504_, v___x_2507_);
v___x_2513_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v___x_2511_, v___x_2512_);
v___x_2514_ = l_Array_append___redArg(v___x_2510_, v___x_2513_);
lean_dec_ref(v___x_2513_);
v___x_2515_ = l_Array_append___redArg(v___x_2514_, v_snd_2477_);
lean_dec(v_snd_2477_);
return v___x_2515_;
}
else
{
lean_object* v___x_2516_; 
lean_dec(v___x_2492_);
lean_dec(v_fst_2476_);
lean_dec(v_fst_2475_);
v___x_2516_ = l_Array_append___redArg(v_fst_2470_, v_snd_2477_);
lean_dec(v_snd_2477_);
return v___x_2516_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(size_t v_sz_2523_, size_t v_i_2524_, lean_object* v_bs_2525_){
_start:
{
uint8_t v___x_2526_; 
v___x_2526_ = lean_usize_dec_lt(v_i_2524_, v_sz_2523_);
if (v___x_2526_ == 0)
{
return v_bs_2525_;
}
else
{
lean_object* v_v_2527_; lean_object* v___x_2528_; lean_object* v_bs_x27_2529_; uint8_t v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; size_t v___x_2533_; size_t v___x_2534_; lean_object* v___x_2535_; 
v_v_2527_ = lean_array_uget(v_bs_2525_, v_i_2524_);
v___x_2528_ = lean_unsigned_to_nat(0u);
v_bs_x27_2529_ = lean_array_uset(v_bs_2525_, v_i_2524_, v___x_2528_);
v___x_2530_ = 1;
v___x_2531_ = lean_box(v___x_2530_);
v___x_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
lean_ctor_set(v___x_2532_, 1, v_v_2527_);
v___x_2533_ = ((size_t)1ULL);
v___x_2534_ = lean_usize_add(v_i_2524_, v___x_2533_);
v___x_2535_ = lean_array_uset(v_bs_x27_2529_, v_i_2524_, v___x_2532_);
v_i_2524_ = v___x_2534_;
v_bs_2525_ = v___x_2535_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7___boxed(lean_object* v_sz_2537_, lean_object* v_i_2538_, lean_object* v_bs_2539_){
_start:
{
size_t v_sz_boxed_2540_; size_t v_i_boxed_2541_; lean_object* v_res_2542_; 
v_sz_boxed_2540_ = lean_unbox_usize(v_sz_2537_);
lean_dec(v_sz_2537_);
v_i_boxed_2541_ = lean_unbox_usize(v_i_2538_);
lean_dec(v_i_2538_);
v_res_2542_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_boxed_2540_, v_i_boxed_2541_, v_bs_2539_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(lean_object* v_original_2548_, lean_object* v_edited_2549_){
_start:
{
lean_object* v_i_2550_; lean_object* v___x_2551_; uint8_t v___x_2552_; 
v_i_2550_ = lean_unsigned_to_nat(0u);
v___x_2551_ = lean_array_get_size(v_original_2548_);
v___x_2552_ = lean_nat_dec_lt(v_i_2550_, v___x_2551_);
if (v___x_2552_ == 0)
{
size_t v_sz_2553_; size_t v___x_2554_; lean_object* v___x_2555_; 
lean_dec_ref(v_original_2548_);
v_sz_2553_ = lean_array_size(v_edited_2549_);
v___x_2554_ = ((size_t)0ULL);
v___x_2555_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_2553_, v___x_2554_, v_edited_2549_);
return v___x_2555_;
}
else
{
lean_object* v___x_2556_; uint8_t v___x_2557_; 
v___x_2556_ = lean_array_get_size(v_edited_2549_);
v___x_2557_ = lean_nat_dec_lt(v_i_2550_, v___x_2556_);
if (v___x_2557_ == 0)
{
size_t v_sz_2558_; size_t v___x_2559_; lean_object* v___x_2560_; 
lean_dec_ref(v_edited_2549_);
v_sz_2558_ = lean_array_size(v_original_2548_);
v___x_2559_ = ((size_t)0ULL);
v___x_2560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_2558_, v___x_2559_, v_original_2548_);
return v___x_2560_;
}
else
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v_ds_2563_; lean_object* v___x_2564_; size_t v_sz_2565_; size_t v___x_2566_; lean_object* v___x_2567_; lean_object* v_snd_2568_; lean_object* v_fst_2569_; lean_object* v_fst_2570_; lean_object* v_snd_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2590_; 
lean_inc_ref(v_original_2548_);
v___x_2561_ = l_Array_toSubarray___redArg(v_original_2548_, v_i_2550_, v___x_2551_);
lean_inc_ref(v_edited_2549_);
v___x_2562_ = l_Array_toSubarray___redArg(v_edited_2549_, v_i_2550_, v___x_2556_);
v_ds_2563_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v___x_2561_, v___x_2562_);
v___x_2564_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__1));
v_sz_2565_ = lean_array_size(v_ds_2563_);
v___x_2566_ = ((size_t)0ULL);
v___x_2567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v_edited_2549_, v___x_2556_, v_original_2548_, v___x_2551_, v_ds_2563_, v_sz_2565_, v___x_2566_, v___x_2564_);
lean_dec_ref(v_ds_2563_);
v_snd_2568_ = lean_ctor_get(v___x_2567_, 1);
lean_inc(v_snd_2568_);
v_fst_2569_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_fst_2569_);
lean_dec_ref(v___x_2567_);
v_fst_2570_ = lean_ctor_get(v_snd_2568_, 0);
v_snd_2571_ = lean_ctor_get(v_snd_2568_, 1);
v_isSharedCheck_2590_ = !lean_is_exclusive(v_snd_2568_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2573_ = v_snd_2568_;
v_isShared_2574_ = v_isSharedCheck_2590_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_snd_2571_);
lean_inc(v_fst_2570_);
lean_dec(v_snd_2568_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2590_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2576_; 
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 1, v_fst_2570_);
lean_ctor_set(v___x_2573_, 0, v_fst_2569_);
v___x_2576_ = v___x_2573_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_fst_2569_);
lean_ctor_set(v_reuseFailAlloc_2589_, 1, v_fst_2570_);
v___x_2576_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
lean_object* v___x_2577_; lean_object* v_fst_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2587_; 
v___x_2577_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2551_, v_original_2548_, v___x_2576_);
lean_dec_ref(v_original_2548_);
v_fst_2578_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2587_ == 0)
{
lean_object* v_unused_2588_; 
v_unused_2588_ = lean_ctor_get(v___x_2577_, 1);
lean_dec(v_unused_2588_);
v___x_2580_ = v___x_2577_;
v_isShared_2581_ = v_isSharedCheck_2587_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_fst_2578_);
lean_dec(v___x_2577_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2587_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 1, v_snd_2571_);
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v_fst_2578_);
lean_ctor_set(v_reuseFailAlloc_2586_, 1, v_snd_2571_);
v___x_2583_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
lean_object* v___x_2584_; lean_object* v_fst_2585_; 
v___x_2584_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2556_, v_edited_2549_, v___x_2583_);
lean_dec_ref(v_edited_2549_);
v_fst_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_fst_2585_);
lean_dec_ref(v___x_2584_);
return v_fst_2585_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(lean_object* v___x_2591_, uint8_t v_inSubst_2592_, lean_object* v___x_2593_, lean_object* v_____r_2594_, lean_object* v_wssIdx_2595_){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; 
v___x_2596_ = lean_box(v_inSubst_2592_);
v___x_2597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2591_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
v___x_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2598_, 0, v_wssIdx_2595_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
v___x_2599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2593_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
v___x_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
return v___x_2600_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1___boxed(lean_object* v___x_2601_, lean_object* v_inSubst_2602_, lean_object* v___x_2603_, lean_object* v_____r_2604_, lean_object* v_wssIdx_2605_){
_start:
{
uint8_t v_inSubst_boxed_2606_; lean_object* v_res_2607_; 
v_inSubst_boxed_2606_ = lean_unbox(v_inSubst_2602_);
v_res_2607_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2601_, v_inSubst_boxed_2606_, v___x_2603_, v_____r_2604_, v_wssIdx_2605_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(lean_object* v_fst_2608_, uint8_t v___x_2609_, lean_object* v_fst_2610_, lean_object* v___x_2611_, lean_object* v_00___2612_){
_start:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2613_ = lean_box(v___x_2609_);
v___x_2614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2614_, 0, v_fst_2608_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
v___x_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2615_, 0, v_fst_2610_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v___x_2616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2611_);
lean_ctor_set(v___x_2616_, 1, v___x_2615_);
v___x_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
return v___x_2617_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0___boxed(lean_object* v_fst_2618_, lean_object* v___x_2619_, lean_object* v_fst_2620_, lean_object* v___x_2621_, lean_object* v_00___2622_){
_start:
{
uint8_t v___x_9180__boxed_2623_; lean_object* v_res_2624_; 
v___x_9180__boxed_2623_ = lean_unbox(v___x_2619_);
v_res_2624_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2618_, v___x_9180__boxed_2623_, v_fst_2620_, v___x_2621_, v_00___2622_);
return v_res_2624_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(uint8_t v_inSubst_2625_, lean_object* v_snd_2626_, lean_object* v_fst_2627_, lean_object* v_____r_2628_, lean_object* v_withWs_2629_, lean_object* v_wssIdx_2630_){
_start:
{
lean_object* v_wss_x27Idx_2632_; uint8_t v___x_2638_; 
v___x_2638_ = lean_unbox(v_snd_2626_);
if (v___x_2638_ == 0)
{
v_wss_x27Idx_2632_ = v_fst_2627_;
goto v___jp_2631_;
}
else
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2639_ = lean_unsigned_to_nat(1u);
v___x_2640_ = lean_nat_add(v_fst_2627_, v___x_2639_);
lean_dec(v_fst_2627_);
v_wss_x27Idx_2632_ = v___x_2640_;
goto v___jp_2631_;
}
v___jp_2631_:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2633_ = lean_box(v_inSubst_2625_);
v___x_2634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2634_, 0, v_wss_x27Idx_2632_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
v___x_2635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2635_, 0, v_wssIdx_2630_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2636_, 0, v_withWs_2629_);
lean_ctor_set(v___x_2636_, 1, v___x_2635_);
v___x_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2636_);
return v___x_2637_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2___boxed(lean_object* v_inSubst_2641_, lean_object* v_snd_2642_, lean_object* v_fst_2643_, lean_object* v_____r_2644_, lean_object* v_withWs_2645_, lean_object* v_wssIdx_2646_){
_start:
{
uint8_t v_inSubst_boxed_2647_; lean_object* v_res_2648_; 
v_inSubst_boxed_2647_ = lean_unbox(v_inSubst_2641_);
v_res_2648_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_boxed_2647_, v_snd_2642_, v_fst_2643_, v_____r_2644_, v_withWs_2645_, v_wssIdx_2646_);
lean_dec(v_snd_2642_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(lean_object* v_upperBound_2649_, lean_object* v_diff_2650_, lean_object* v_snd_2651_, lean_object* v_snd_2652_, lean_object* v_a_2653_, lean_object* v_b_2654_){
_start:
{
lean_object* v_a_2656_; lean_object* v___y_2661_; uint8_t v___x_2664_; 
v___x_2664_ = lean_nat_dec_lt(v_a_2653_, v_upperBound_2649_);
if (v___x_2664_ == 0)
{
lean_dec(v_a_2653_);
return v_b_2654_;
}
else
{
lean_object* v___x_2665_; lean_object* v_snd_2666_; lean_object* v_snd_2667_; lean_object* v_fst_2668_; lean_object* v_fst_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2809_; 
v___x_2665_ = lean_array_fget_borrowed(v_diff_2650_, v_a_2653_);
v_snd_2666_ = lean_ctor_get(v_b_2654_, 1);
lean_inc(v_snd_2666_);
v_snd_2667_ = lean_ctor_get(v_snd_2666_, 1);
lean_inc(v_snd_2667_);
v_fst_2668_ = lean_ctor_get(v___x_2665_, 0);
v_fst_2669_ = lean_ctor_get(v_b_2654_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v_b_2654_);
if (v_isSharedCheck_2809_ == 0)
{
lean_object* v_unused_2810_; 
v_unused_2810_ = lean_ctor_get(v_b_2654_, 1);
lean_dec(v_unused_2810_);
v___x_2671_ = v_b_2654_;
v_isShared_2672_ = v_isSharedCheck_2809_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_fst_2669_);
lean_dec(v_b_2654_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2809_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v_fst_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2807_; 
v_fst_2673_ = lean_ctor_get(v_snd_2666_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v_snd_2666_);
if (v_isSharedCheck_2807_ == 0)
{
lean_object* v_unused_2808_; 
v_unused_2808_ = lean_ctor_get(v_snd_2666_, 1);
lean_dec(v_unused_2808_);
v___x_2675_ = v_snd_2666_;
v_isShared_2676_ = v_isSharedCheck_2807_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_fst_2673_);
lean_dec(v_snd_2666_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2807_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v_fst_2677_; lean_object* v_snd_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2806_; 
v_fst_2677_ = lean_ctor_get(v_snd_2667_, 0);
v_snd_2678_ = lean_ctor_get(v_snd_2667_, 1);
v_isSharedCheck_2806_ = !lean_is_exclusive(v_snd_2667_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2680_ = v_snd_2667_;
v_isShared_2681_ = v_isSharedCheck_2806_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_snd_2678_);
lean_inc(v_fst_2677_);
lean_dec(v_snd_2667_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2806_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2682_; lean_object* v___y_2684_; lean_object* v___y_2699_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; uint8_t v___x_2710_; 
lean_inc(v___x_2665_);
v___x_2682_ = lean_array_push(v_fst_2669_, v___x_2665_);
v___x_2707_ = lean_unsigned_to_nat(1u);
v___x_2708_ = lean_nat_add(v_a_2653_, v___x_2707_);
v___x_2709_ = lean_array_get_size(v_diff_2650_);
v___x_2710_ = lean_nat_dec_lt(v___x_2708_, v___x_2709_);
if (v___x_2710_ == 0)
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
lean_dec(v___x_2708_);
lean_del_object(v___x_2680_);
lean_del_object(v___x_2675_);
lean_del_object(v___x_2671_);
v___x_2711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2711_, 0, v_fst_2677_);
lean_ctor_set(v___x_2711_, 1, v_snd_2678_);
v___x_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2712_, 0, v_fst_2673_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
v___x_2713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2682_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v_a_2656_ = v___x_2713_;
goto v___jp_2655_;
}
else
{
lean_object* v___x_2714_; lean_object* v_fst_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2804_; 
v___x_2714_ = lean_array_fget(v_diff_2650_, v___x_2708_);
lean_dec(v___x_2708_);
v_fst_2715_ = lean_ctor_get(v___x_2714_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2714_);
if (v_isSharedCheck_2804_ == 0)
{
lean_object* v_unused_2805_; 
v_unused_2805_ = lean_ctor_get(v___x_2714_, 1);
lean_dec(v_unused_2805_);
v___x_2717_ = v___x_2714_;
v_isShared_2718_ = v_isSharedCheck_2804_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_fst_2715_);
lean_dec(v___x_2714_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2804_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
uint8_t v_inSubst_2719_; lean_object* v___y_2721_; lean_object* v___x_2730_; uint8_t v___x_2731_; 
v_inSubst_2719_ = 0;
v___x_2730_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2731_ = lean_unbox(v_fst_2668_);
switch(v___x_2731_)
{
case 0:
{
uint8_t v___x_2732_; 
lean_del_object(v___x_2680_);
lean_del_object(v___x_2675_);
lean_del_object(v___x_2671_);
v___x_2732_ = lean_unbox(v_fst_2715_);
switch(v___x_2732_)
{
case 0:
{
lean_object* v___x_2733_; lean_object* v___x_2735_; 
v___x_2733_ = lean_array_get_borrowed(v___x_2730_, v_snd_2651_, v_fst_2677_);
lean_inc(v___x_2733_);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 1, v___x_2733_);
v___x_2735_ = v___x_2717_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_fst_2715_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2736_ = lean_array_push(v___x_2682_, v___x_2735_);
v___x_2737_ = lean_nat_add(v_fst_2677_, v___x_2707_);
lean_dec(v_fst_2677_);
v___x_2738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2737_);
lean_ctor_set(v___x_2738_, 1, v_snd_2678_);
v___x_2739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2739_, 0, v_fst_2673_);
lean_ctor_set(v___x_2739_, 1, v___x_2738_);
v___x_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2736_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v_a_2656_ = v___x_2740_;
goto v___jp_2655_;
}
}
case 1:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
lean_del_object(v___x_2717_);
lean_dec(v_fst_2715_);
lean_dec(v_snd_2678_);
v___x_2742_ = lean_box(0);
v___x_2743_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2677_, v___x_2664_, v_fst_2673_, v___x_2682_, v___x_2742_);
v___y_2661_ = v___x_2743_;
goto v___jp_2660_;
}
default: 
{
lean_object* v___x_2744_; uint8_t v___x_2745_; 
lean_dec(v_fst_2715_);
v___x_2744_ = lean_array_get_borrowed(v___x_2730_, v_snd_2651_, v_fst_2677_);
v___x_2745_ = lean_unbox(v_snd_2678_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2747_; 
lean_inc(v___x_2744_);
lean_inc(v_fst_2668_);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 1, v___x_2744_);
lean_ctor_set(v___x_2717_, 0, v_fst_2668_);
v___x_2747_ = v___x_2717_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_fst_2668_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v___x_2744_);
v___x_2747_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2748_ = lean_mk_empty_array_with_capacity(v___x_2707_);
v___x_2749_ = lean_array_push(v___x_2748_, v___x_2747_);
v___y_2721_ = v___x_2749_;
goto v___jp_2720_;
}
}
else
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
lean_del_object(v___x_2717_);
v___x_2751_ = lean_array_get_borrowed(v___x_2730_, v_snd_2652_, v_fst_2673_);
lean_inc(v___x_2744_);
lean_inc(v___x_2751_);
v___x_2752_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2751_, v___x_2744_);
v___y_2721_ = v___x_2752_;
goto v___jp_2720_;
}
}
}
}
case 1:
{
uint8_t v___x_2753_; 
lean_del_object(v___x_2680_);
lean_del_object(v___x_2675_);
lean_del_object(v___x_2671_);
v___x_2753_ = lean_unbox(v_fst_2715_);
switch(v___x_2753_)
{
case 0:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
lean_del_object(v___x_2717_);
lean_dec(v_fst_2715_);
lean_dec(v_snd_2678_);
v___x_2754_ = lean_box(0);
v___x_2755_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2677_, v___x_2664_, v_fst_2673_, v___x_2682_, v___x_2754_);
v___y_2661_ = v___x_2755_;
goto v___jp_2660_;
}
case 1:
{
lean_object* v___x_2756_; lean_object* v___x_2758_; 
v___x_2756_ = lean_array_get_borrowed(v___x_2730_, v_snd_2652_, v_fst_2673_);
lean_inc(v___x_2756_);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 1, v___x_2756_);
v___x_2758_ = v___x_2717_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_fst_2715_);
lean_ctor_set(v_reuseFailAlloc_2764_, 1, v___x_2756_);
v___x_2758_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2759_ = lean_array_push(v___x_2682_, v___x_2758_);
v___x_2760_ = lean_nat_add(v_fst_2673_, v___x_2707_);
lean_dec(v_fst_2673_);
v___x_2761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2761_, 0, v_fst_2677_);
lean_ctor_set(v___x_2761_, 1, v_snd_2678_);
v___x_2762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2760_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
v___x_2763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2759_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v_a_2656_ = v___x_2763_;
goto v___jp_2655_;
}
}
default: 
{
uint8_t v___x_2768_; 
lean_dec(v_fst_2715_);
v___x_2768_ = lean_unbox(v_snd_2678_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; uint8_t v___x_2773_; 
v___x_2769_ = lean_array_get_borrowed(v___x_2730_, v_snd_2652_, v_fst_2673_);
v___x_2770_ = lean_unsigned_to_nat(0u);
v___x_2771_ = lean_string_utf8_byte_size(v___x_2769_);
lean_inc(v___x_2769_);
v___x_2772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2772_, 0, v___x_2769_);
lean_ctor_set(v___x_2772_, 1, v___x_2770_);
lean_ctor_set(v___x_2772_, 2, v___x_2771_);
v___x_2773_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_2772_);
lean_dec_ref_known(v___x_2772_, 3);
if (v___x_2773_ == 0)
{
lean_object* v___x_2775_; 
lean_inc(v___x_2769_);
lean_inc(v_fst_2668_);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 1, v___x_2769_);
lean_ctor_set(v___x_2717_, 0, v_fst_2668_);
v___x_2775_ = v___x_2717_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_fst_2668_);
lean_ctor_set(v_reuseFailAlloc_2780_, 1, v___x_2769_);
v___x_2775_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2776_ = lean_array_push(v___x_2682_, v___x_2775_);
v___x_2777_ = lean_nat_add(v_fst_2673_, v___x_2707_);
lean_dec(v_fst_2673_);
v___x_2778_ = lean_box(0);
v___x_2779_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2719_, v_snd_2678_, v_fst_2677_, v___x_2778_, v___x_2776_, v___x_2777_);
lean_dec(v_snd_2678_);
v___y_2661_ = v___x_2779_;
goto v___jp_2660_;
}
}
else
{
lean_del_object(v___x_2717_);
goto v___jp_2765_;
}
}
else
{
lean_del_object(v___x_2717_);
goto v___jp_2765_;
}
v___jp_2765_:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = lean_box(0);
v___x_2767_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2719_, v_snd_2678_, v_fst_2677_, v___x_2766_, v___x_2682_, v_fst_2673_);
lean_dec(v_snd_2678_);
v___y_2661_ = v___x_2767_;
goto v___jp_2660_;
}
}
}
}
default: 
{
uint8_t v___x_2781_; 
v___x_2781_ = lean_unbox(v_fst_2715_);
if (v___x_2781_ == 1)
{
lean_object* v___x_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
v___x_2782_ = lean_array_get_borrowed(v___x_2730_, v_snd_2652_, v_fst_2673_);
v___x_2783_ = lean_array_get_size(v_snd_2651_);
v___x_2784_ = lean_nat_dec_lt(v_fst_2677_, v___x_2783_);
if (v___x_2784_ == 0)
{
lean_object* v___x_2786_; 
lean_inc(v___x_2782_);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 1, v___x_2782_);
v___x_2786_ = v___x_2717_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_fst_2715_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v___x_2782_);
v___x_2786_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = lean_mk_empty_array_with_capacity(v___x_2707_);
v___x_2788_ = lean_array_push(v___x_2787_, v___x_2786_);
v___y_2684_ = v___x_2788_;
goto v___jp_2683_;
}
}
else
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
lean_del_object(v___x_2717_);
lean_dec(v_fst_2715_);
v___x_2790_ = lean_array_fget_borrowed(v_snd_2651_, v_fst_2677_);
lean_inc(v___x_2790_);
lean_inc(v___x_2782_);
v___x_2791_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2782_, v___x_2790_);
v___y_2684_ = v___x_2791_;
goto v___jp_2683_;
}
}
else
{
lean_object* v___x_2792_; lean_object* v___x_2793_; uint8_t v___x_2794_; 
lean_dec(v_fst_2715_);
lean_del_object(v___x_2680_);
lean_del_object(v___x_2675_);
lean_del_object(v___x_2671_);
v___x_2792_ = lean_array_get_borrowed(v___x_2730_, v_snd_2651_, v_fst_2677_);
v___x_2793_ = lean_array_get_size(v_snd_2652_);
v___x_2794_ = lean_nat_dec_lt(v_fst_2673_, v___x_2793_);
if (v___x_2794_ == 0)
{
uint8_t v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2798_; 
v___x_2795_ = 0;
v___x_2796_ = lean_box(v___x_2795_);
lean_inc(v___x_2792_);
if (v_isShared_2718_ == 0)
{
lean_ctor_set(v___x_2717_, 1, v___x_2792_);
lean_ctor_set(v___x_2717_, 0, v___x_2796_);
v___x_2798_ = v___x_2717_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2796_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v___x_2792_);
v___x_2798_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = lean_mk_empty_array_with_capacity(v___x_2707_);
v___x_2800_ = lean_array_push(v___x_2799_, v___x_2798_);
v___y_2699_ = v___x_2800_;
goto v___jp_2698_;
}
}
else
{
lean_object* v___x_2802_; lean_object* v___x_2803_; 
lean_del_object(v___x_2717_);
v___x_2802_ = lean_array_fget_borrowed(v_snd_2652_, v_fst_2673_);
lean_inc(v___x_2792_);
lean_inc(v___x_2802_);
v___x_2803_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2802_, v___x_2792_);
v___y_2699_ = v___x_2803_;
goto v___jp_2698_;
}
}
}
}
v___jp_2720_:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; uint8_t v___x_2724_; 
v___x_2722_ = l_Array_append___redArg(v___x_2682_, v___y_2721_);
lean_dec_ref(v___y_2721_);
v___x_2723_ = lean_nat_add(v_fst_2677_, v___x_2707_);
lean_dec(v_fst_2677_);
v___x_2724_ = lean_unbox(v_snd_2678_);
lean_dec(v_snd_2678_);
if (v___x_2724_ == 0)
{
lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2725_ = lean_box(0);
v___x_2726_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2723_, v_inSubst_2719_, v___x_2722_, v___x_2725_, v_fst_2673_);
v___y_2661_ = v___x_2726_;
goto v___jp_2660_;
}
else
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2727_ = lean_nat_add(v_fst_2673_, v___x_2707_);
lean_dec(v_fst_2673_);
v___x_2728_ = lean_box(0);
v___x_2729_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2723_, v_inSubst_2719_, v___x_2722_, v___x_2728_, v___x_2727_);
v___y_2661_ = v___x_2729_;
goto v___jp_2660_;
}
}
}
}
v___jp_2683_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2690_; 
v___x_2685_ = l_Array_append___redArg(v___x_2682_, v___y_2684_);
lean_dec_ref(v___y_2684_);
v___x_2686_ = lean_unsigned_to_nat(1u);
v___x_2687_ = lean_nat_add(v_fst_2673_, v___x_2686_);
lean_dec(v_fst_2673_);
v___x_2688_ = lean_nat_add(v_fst_2677_, v___x_2686_);
lean_dec(v_fst_2677_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 0, v___x_2688_);
v___x_2690_ = v___x_2680_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2688_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v_snd_2678_);
v___x_2690_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
lean_object* v___x_2692_; 
if (v_isShared_2676_ == 0)
{
lean_ctor_set(v___x_2675_, 1, v___x_2690_);
lean_ctor_set(v___x_2675_, 0, v___x_2687_);
v___x_2692_ = v___x_2675_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2687_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v___x_2690_);
v___x_2692_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
lean_object* v___x_2694_; 
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 1, v___x_2692_);
lean_ctor_set(v___x_2671_, 0, v___x_2685_);
v___x_2694_ = v___x_2671_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2685_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v___x_2692_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
v_a_2656_ = v___x_2694_;
goto v___jp_2655_;
}
}
}
}
v___jp_2698_:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2700_ = l_Array_append___redArg(v___x_2682_, v___y_2699_);
lean_dec_ref(v___y_2699_);
v___x_2701_ = lean_unsigned_to_nat(1u);
v___x_2702_ = lean_nat_add(v_fst_2673_, v___x_2701_);
lean_dec(v_fst_2673_);
v___x_2703_ = lean_nat_add(v_fst_2677_, v___x_2701_);
lean_dec(v_fst_2677_);
v___x_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
lean_ctor_set(v___x_2704_, 1, v_snd_2678_);
v___x_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2702_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
v___x_2706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2700_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
v_a_2656_ = v___x_2706_;
goto v___jp_2655_;
}
}
}
}
}
v___jp_2655_:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = lean_unsigned_to_nat(1u);
v___x_2658_ = lean_nat_add(v_a_2653_, v___x_2657_);
lean_dec(v_a_2653_);
v_a_2653_ = v___x_2658_;
v_b_2654_ = v_a_2656_;
goto _start;
}
v___jp_2660_:
{
if (lean_obj_tag(v___y_2661_) == 0)
{
lean_object* v_a_2662_; 
lean_dec(v_a_2653_);
v_a_2662_ = lean_ctor_get(v___y_2661_, 0);
lean_inc(v_a_2662_);
lean_dec_ref_known(v___y_2661_, 1);
return v_a_2662_;
}
else
{
lean_object* v_a_2663_; 
v_a_2663_ = lean_ctor_get(v___y_2661_, 0);
lean_inc(v_a_2663_);
lean_dec_ref_known(v___y_2661_, 1);
v_a_2656_ = v_a_2663_;
goto v___jp_2655_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___boxed(lean_object* v_upperBound_2811_, lean_object* v_diff_2812_, lean_object* v_snd_2813_, lean_object* v_snd_2814_, lean_object* v_a_2815_, lean_object* v_b_2816_){
_start:
{
lean_object* v_res_2817_; 
v_res_2817_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2811_, v_diff_2812_, v_snd_2813_, v_snd_2814_, v_a_2815_, v_b_2816_);
lean_dec_ref(v_snd_2814_);
lean_dec_ref(v_snd_2813_);
lean_dec_ref(v_diff_2812_);
lean_dec(v_upperBound_2811_);
return v_res_2817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(lean_object* v_s_2828_, lean_object* v_s_x27_2829_){
_start:
{
lean_object* v___x_2830_; lean_object* v_fst_2831_; lean_object* v_snd_2832_; lean_object* v___x_2833_; lean_object* v_fst_2834_; lean_object* v_snd_2835_; lean_object* v_diff_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v_fst_2841_; lean_object* v___x_2842_; size_t v_sz_2843_; size_t v___x_2844_; lean_object* v___x_2845_; 
v___x_2830_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_2828_);
v_fst_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_fst_2831_);
v_snd_2832_ = lean_ctor_get(v___x_2830_, 1);
lean_inc(v_snd_2832_);
lean_dec_ref(v___x_2830_);
v___x_2833_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_x27_2829_);
v_fst_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_fst_2834_);
v_snd_2835_ = lean_ctor_get(v___x_2833_, 1);
lean_inc(v_snd_2835_);
lean_dec_ref(v___x_2833_);
v_diff_2836_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(v_fst_2831_, v_fst_2834_);
v___x_2837_ = lean_unsigned_to_nat(0u);
v___x_2838_ = lean_array_get_size(v_diff_2836_);
v___x_2839_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__2));
v___x_2840_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v___x_2838_, v_diff_2836_, v_snd_2835_, v_snd_2832_, v___x_2837_, v___x_2839_);
lean_dec(v_snd_2832_);
lean_dec(v_snd_2835_);
lean_dec_ref(v_diff_2836_);
v_fst_2841_ = lean_ctor_get(v___x_2840_, 0);
lean_inc(v_fst_2841_);
lean_dec_ref(v___x_2840_);
v___x_2842_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_fst_2841_);
lean_dec(v_fst_2841_);
v_sz_2843_ = lean_array_size(v___x_2842_);
v___x_2844_ = ((size_t)0ULL);
v___x_2845_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_2843_, v___x_2844_, v___x_2842_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___boxed(lean_object* v_s_2846_, lean_object* v_s_x27_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_2846_, v_s_x27_2847_);
lean_dec_ref(v_s_x27_2847_);
lean_dec_ref(v_s_2846_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(lean_object* v_upperBound_2849_, lean_object* v_diff_2850_, lean_object* v_snd_2851_, lean_object* v_snd_2852_, lean_object* v_inst_2853_, lean_object* v_R_2854_, lean_object* v_a_2855_, lean_object* v_b_2856_, lean_object* v_c_2857_){
_start:
{
lean_object* v___x_2858_; 
v___x_2858_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2849_, v_diff_2850_, v_snd_2851_, v_snd_2852_, v_a_2855_, v_b_2856_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___boxed(lean_object* v_upperBound_2859_, lean_object* v_diff_2860_, lean_object* v_snd_2861_, lean_object* v_snd_2862_, lean_object* v_inst_2863_, lean_object* v_R_2864_, lean_object* v_a_2865_, lean_object* v_b_2866_, lean_object* v_c_2867_){
_start:
{
lean_object* v_res_2868_; 
v_res_2868_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(v_upperBound_2859_, v_diff_2860_, v_snd_2861_, v_snd_2862_, v_inst_2863_, v_R_2864_, v_a_2865_, v_b_2866_, v_c_2867_);
lean_dec_ref(v_snd_2862_);
lean_dec_ref(v_snd_2861_);
lean_dec_ref(v_diff_2860_);
lean_dec(v_upperBound_2859_);
return v_res_2868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(lean_object* v_original_2869_, lean_object* v___x_2870_, lean_object* v_a_2871_, lean_object* v_inst_2872_, lean_object* v_a_2873_){
_start:
{
lean_object* v___x_2874_; 
v___x_2874_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v_original_2869_, v___x_2870_, v_a_2871_, v_a_2873_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___boxed(lean_object* v_original_2875_, lean_object* v___x_2876_, lean_object* v_a_2877_, lean_object* v_inst_2878_, lean_object* v_a_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(v_original_2875_, v___x_2876_, v_a_2877_, v_inst_2878_, v_a_2879_);
lean_dec_ref(v_a_2877_);
lean_dec(v___x_2876_);
lean_dec_ref(v_original_2875_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(lean_object* v_edited_2881_, lean_object* v___x_2882_, lean_object* v_a_2883_, lean_object* v_inst_2884_, lean_object* v_a_2885_){
_start:
{
lean_object* v___x_2886_; 
v___x_2886_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(v_edited_2881_, v___x_2882_, v_a_2883_, v_a_2885_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___boxed(lean_object* v_edited_2887_, lean_object* v___x_2888_, lean_object* v_a_2889_, lean_object* v_inst_2890_, lean_object* v_a_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v_edited_2887_, v___x_2888_, v_a_2889_, v_inst_2890_, v_a_2891_);
lean_dec_ref(v_a_2889_);
lean_dec(v___x_2888_);
lean_dec_ref(v_edited_2887_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(lean_object* v___x_2893_, lean_object* v_original_2894_, lean_object* v_inst_2895_, lean_object* v_a_2896_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2893_, v_original_2894_, v_a_2896_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___boxed(lean_object* v___x_2898_, lean_object* v_original_2899_, lean_object* v_inst_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(v___x_2898_, v_original_2899_, v_inst_2900_, v_a_2901_);
lean_dec_ref(v_original_2899_);
lean_dec(v___x_2898_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(lean_object* v___x_2903_, lean_object* v_edited_2904_, lean_object* v_inst_2905_, lean_object* v_a_2906_){
_start:
{
lean_object* v___x_2907_; 
v___x_2907_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2903_, v_edited_2904_, v_a_2906_);
return v___x_2907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___boxed(lean_object* v___x_2908_, lean_object* v_edited_2909_, lean_object* v_inst_2910_, lean_object* v_a_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(v___x_2908_, v_edited_2909_, v_inst_2910_, v_a_2911_);
lean_dec_ref(v_edited_2909_);
lean_dec(v___x_2908_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4(lean_object* v_as_2913_, lean_object* v_as_x27_2914_, lean_object* v_b_2915_, lean_object* v_a_2916_){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(v_as_x27_2914_, v_b_2915_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___boxed(lean_object* v_as_2918_, lean_object* v_as_x27_2919_, lean_object* v_b_2920_, lean_object* v_a_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4(v_as_2918_, v_as_x27_2919_, v_b_2920_, v_a_2921_);
lean_dec(v_as_x27_2919_);
lean_dec(v_as_2918_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7(lean_object* v_lsize_2923_, lean_object* v_rsize_2924_, lean_object* v_histogram_2925_, lean_object* v_index_2926_, lean_object* v_val_2927_){
_start:
{
lean_object* v___x_2928_; 
v___x_2928_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(v_histogram_2925_, v_index_2926_, v_val_2927_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___boxed(lean_object* v_lsize_2929_, lean_object* v_rsize_2930_, lean_object* v_histogram_2931_, lean_object* v_index_2932_, lean_object* v_val_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7(v_lsize_2929_, v_rsize_2930_, v_histogram_2931_, v_index_2932_, v_val_2933_);
lean_dec(v_rsize_2930_);
lean_dec(v_lsize_2929_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8(lean_object* v_upperBound_2935_, lean_object* v___x_2936_, lean_object* v_fst_2937_, lean_object* v___x_2938_, lean_object* v_inst_2939_, lean_object* v_R_2940_, lean_object* v_a_2941_, lean_object* v_b_2942_, lean_object* v_c_2943_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(v_upperBound_2935_, v___x_2936_, v_fst_2937_, v___x_2938_, v_a_2941_, v_b_2942_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___boxed(lean_object* v_upperBound_2945_, lean_object* v___x_2946_, lean_object* v_fst_2947_, lean_object* v___x_2948_, lean_object* v_inst_2949_, lean_object* v_R_2950_, lean_object* v_a_2951_, lean_object* v_b_2952_, lean_object* v_c_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8(v_upperBound_2945_, v___x_2946_, v_fst_2947_, v___x_2948_, v_inst_2949_, v_R_2950_, v_a_2951_, v_b_2952_, v_c_2953_);
lean_dec(v___x_2948_);
lean_dec_ref(v_fst_2947_);
lean_dec(v___x_2946_);
lean_dec(v_upperBound_2945_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9(lean_object* v_lsize_2955_, lean_object* v_rsize_2956_, lean_object* v_histogram_2957_, lean_object* v_index_2958_, lean_object* v_val_2959_){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(v_histogram_2957_, v_index_2958_, v_val_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___boxed(lean_object* v_lsize_2961_, lean_object* v_rsize_2962_, lean_object* v_histogram_2963_, lean_object* v_index_2964_, lean_object* v_val_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9(v_lsize_2961_, v_rsize_2962_, v_histogram_2963_, v_index_2964_, v_val_2965_);
lean_dec(v_rsize_2962_);
lean_dec(v_lsize_2961_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10(lean_object* v_upperBound_2967_, lean_object* v_fst_2968_, lean_object* v___x_2969_, lean_object* v_fst_2970_, lean_object* v_inst_2971_, lean_object* v_R_2972_, lean_object* v_a_2973_, lean_object* v_b_2974_, lean_object* v_c_2975_){
_start:
{
lean_object* v___x_2976_; 
v___x_2976_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(v_upperBound_2967_, v_fst_2968_, v___x_2969_, v_fst_2970_, v_a_2973_, v_b_2974_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___boxed(lean_object* v_upperBound_2977_, lean_object* v_fst_2978_, lean_object* v___x_2979_, lean_object* v_fst_2980_, lean_object* v_inst_2981_, lean_object* v_R_2982_, lean_object* v_a_2983_, lean_object* v_b_2984_, lean_object* v_c_2985_){
_start:
{
lean_object* v_res_2986_; 
v_res_2986_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10(v_upperBound_2977_, v_fst_2978_, v___x_2979_, v_fst_2980_, v_inst_2981_, v_R_2982_, v_a_2983_, v_b_2984_, v_c_2985_);
lean_dec_ref(v_fst_2980_);
lean_dec(v___x_2979_);
lean_dec_ref(v_fst_2978_);
lean_dec(v_upperBound_2977_);
return v_res_2986_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11(lean_object* v_00_u03b2_2987_, lean_object* v_m_2988_, lean_object* v_a_2989_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_m_2988_, v_a_2989_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___boxed(lean_object* v_00_u03b2_2991_, lean_object* v_m_2992_, lean_object* v_a_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11(v_00_u03b2_2991_, v_m_2992_, v_a_2993_);
lean_dec_ref(v_a_2993_);
lean_dec_ref(v_m_2992_);
return v_res_2994_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12(lean_object* v_00_u03b2_2995_, lean_object* v_m_2996_, lean_object* v_a_2997_, lean_object* v_b_2998_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_m_2996_, v_a_2997_, v_b_2998_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14(lean_object* v_inst_3000_, lean_object* v_R_3001_, lean_object* v_a_3002_, lean_object* v_b_3003_){
_start:
{
lean_object* v___x_3004_; 
v___x_3004_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v_a_3002_, v_b_3003_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20(lean_object* v_00_u03b2_3005_, lean_object* v_a_3006_, lean_object* v_x_3007_){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(v_a_3006_, v_x_3007_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___boxed(lean_object* v_00_u03b2_3009_, lean_object* v_a_3010_, lean_object* v_x_3011_){
_start:
{
lean_object* v_res_3012_; 
v_res_3012_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20(v_00_u03b2_3009_, v_a_3010_, v_x_3011_);
lean_dec(v_x_3011_);
lean_dec_ref(v_a_3010_);
return v_res_3012_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22(lean_object* v_00_u03b2_3013_, lean_object* v_a_3014_, lean_object* v_x_3015_){
_start:
{
uint8_t v___x_3016_; 
v___x_3016_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(v_a_3014_, v_x_3015_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___boxed(lean_object* v_00_u03b2_3017_, lean_object* v_a_3018_, lean_object* v_x_3019_){
_start:
{
uint8_t v_res_3020_; lean_object* v_r_3021_; 
v_res_3020_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22(v_00_u03b2_3017_, v_a_3018_, v_x_3019_);
lean_dec(v_x_3019_);
lean_dec_ref(v_a_3018_);
v_r_3021_ = lean_box(v_res_3020_);
return v_r_3021_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23(lean_object* v_00_u03b2_3022_, lean_object* v_data_3023_){
_start:
{
lean_object* v___x_3024_; 
v___x_3024_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23___redArg(v_data_3023_);
return v___x_3024_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24(lean_object* v_00_u03b2_3025_, lean_object* v_a_3026_, lean_object* v_b_3027_, lean_object* v_x_3028_){
_start:
{
lean_object* v___x_3029_; 
v___x_3029_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(v_a_3026_, v_b_3027_, v_x_3028_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28(lean_object* v_00_u03b2_3030_, lean_object* v_i_3031_, lean_object* v_source_3032_, lean_object* v_target_3033_){
_start:
{
lean_object* v___x_3034_; 
v___x_3034_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28___redArg(v_i_3031_, v_source_3032_, v_target_3033_);
return v___x_3034_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_3035_, lean_object* v_x_3036_, lean_object* v_x_3037_){
_start:
{
lean_object* v___x_3038_; 
v___x_3038_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29___redArg(v_x_3036_, v_x_3037_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(lean_object* v_s_3039_){
_start:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3040_ = lean_string_data(v_s_3039_);
v___x_3041_ = lean_array_mk(v___x_3040_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(lean_object* v_s_3042_, lean_object* v_s_x27_3043_){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3044_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3042_);
v___x_3045_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3043_);
v___x_3046_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3044_, v___x_3045_);
v___x_3047_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_3046_);
lean_dec_ref(v___x_3046_);
return v___x_3047_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(lean_object* v_s_3048_, lean_object* v_s_x27_3049_){
_start:
{
uint8_t v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; uint8_t v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3050_ = 1;
v___x_3051_ = lean_box(v___x_3050_);
v___x_3052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3051_);
lean_ctor_set(v___x_3052_, 1, v_s_3048_);
v___x_3053_ = 0;
v___x_3054_ = lean_box(v___x_3053_);
v___x_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
lean_ctor_set(v___x_3055_, 1, v_s_x27_3049_);
v___x_3056_ = lean_unsigned_to_nat(2u);
v___x_3057_ = lean_mk_empty_array_with_capacity(v___x_3056_);
v___x_3058_ = lean_array_push(v___x_3057_, v___x_3052_);
v___x_3059_ = lean_array_push(v___x_3058_, v___x_3055_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(lean_object* v_as_3060_, size_t v_i_3061_, size_t v_stop_3062_, lean_object* v_b_3063_){
_start:
{
lean_object* v___y_3065_; uint8_t v___x_3069_; 
v___x_3069_ = lean_usize_dec_eq(v_i_3061_, v_stop_3062_);
if (v___x_3069_ == 0)
{
lean_object* v___x_3070_; lean_object* v_fst_3071_; uint8_t v___x_3072_; uint8_t v___x_3073_; uint8_t v___x_3074_; 
v___x_3070_ = lean_array_uget_borrowed(v_as_3060_, v_i_3061_);
v_fst_3071_ = lean_ctor_get(v___x_3070_, 0);
v___x_3072_ = 2;
v___x_3073_ = lean_unbox(v_fst_3071_);
v___x_3074_ = l_Lean_Diff_instBEqAction_beq(v___x_3073_, v___x_3072_);
if (v___x_3074_ == 0)
{
lean_object* v___x_3075_; 
lean_inc(v___x_3070_);
v___x_3075_ = lean_array_push(v_b_3063_, v___x_3070_);
v___y_3065_ = v___x_3075_;
goto v___jp_3064_;
}
else
{
v___y_3065_ = v_b_3063_;
goto v___jp_3064_;
}
}
else
{
return v_b_3063_;
}
v___jp_3064_:
{
size_t v___x_3066_; size_t v___x_3067_; 
v___x_3066_ = ((size_t)1ULL);
v___x_3067_ = lean_usize_add(v_i_3061_, v___x_3066_);
v_i_3061_ = v___x_3067_;
v_b_3063_ = v___y_3065_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0___boxed(lean_object* v_as_3076_, lean_object* v_i_3077_, lean_object* v_stop_3078_, lean_object* v_b_3079_){
_start:
{
size_t v_i_boxed_3080_; size_t v_stop_boxed_3081_; lean_object* v_res_3082_; 
v_i_boxed_3080_ = lean_unbox_usize(v_i_3077_);
lean_dec(v_i_3077_);
v_stop_boxed_3081_ = lean_unbox_usize(v_stop_3078_);
lean_dec(v_stop_3078_);
v_res_3082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_as_3076_, v_i_boxed_3080_, v_stop_boxed_3081_, v_b_3079_);
lean_dec_ref(v_as_3076_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff(lean_object* v_s_3083_, lean_object* v_s_x27_3084_, uint8_t v_granularity_3085_){
_start:
{
lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; uint8_t v___y_3090_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; 
switch(v_granularity_3085_)
{
case 0:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___y_3132_; uint8_t v___x_3138_; 
v___x_3129_ = lean_string_length(v_s_3083_);
v___x_3130_ = lean_string_length(v_s_x27_3084_);
v___x_3138_ = lean_nat_dec_le(v___x_3129_, v___x_3130_);
if (v___x_3138_ == 0)
{
v___y_3132_ = v___x_3130_;
goto v___jp_3131_;
}
else
{
v___y_3132_ = v___x_3129_;
goto v___jp_3131_;
}
v___jp_3131_:
{
lean_object* v___x_3133_; lean_object* v_maxCharDiffDistance_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; uint8_t v___x_3137_; 
v___x_3133_ = lean_unsigned_to_nat(5u);
v_maxCharDiffDistance_3134_ = lean_nat_div(v___y_3132_, v___x_3133_);
v___x_3135_ = lean_unsigned_to_nat(1u);
v___x_3136_ = lean_nat_shiftr(v___y_3132_, v___x_3135_);
lean_dec(v___y_3132_);
v___x_3137_ = lean_nat_dec_le(v___x_3129_, v___x_3130_);
if (v___x_3137_ == 0)
{
v___y_3109_ = v___x_3135_;
v___y_3110_ = v_maxCharDiffDistance_3134_;
v___y_3111_ = v___x_3136_;
v___y_3112_ = v___x_3129_;
goto v___jp_3108_;
}
else
{
v___y_3109_ = v___x_3135_;
v___y_3110_ = v_maxCharDiffDistance_3134_;
v___y_3111_ = v___x_3136_;
v___y_3112_ = v___x_3130_;
goto v___jp_3108_;
}
}
}
case 1:
{
lean_object* v___x_3139_; 
v___x_3139_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(v_s_3083_, v_s_x27_3084_);
return v___x_3139_;
}
case 2:
{
lean_object* v___x_3140_; 
v___x_3140_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3083_, v_s_x27_3084_);
lean_dec_ref(v_s_x27_3084_);
lean_dec_ref(v_s_3083_);
return v___x_3140_;
}
case 3:
{
lean_object* v___x_3141_; 
v___x_3141_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3083_, v_s_x27_3084_);
return v___x_3141_;
}
default: 
{
uint8_t v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; 
lean_dec_ref(v_s_3083_);
v___x_3142_ = 0;
v___x_3143_ = lean_box(v___x_3142_);
v___x_3144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
lean_ctor_set(v___x_3144_, 1, v_s_x27_3084_);
v___x_3145_ = lean_unsigned_to_nat(1u);
v___x_3146_ = lean_mk_empty_array_with_capacity(v___x_3145_);
v___x_3147_ = lean_array_push(v___x_3146_, v___x_3144_);
return v___x_3147_;
}
}
v___jp_3086_:
{
if (v___y_3090_ == 0)
{
uint8_t v___x_3091_; 
lean_dec_ref(v___y_3087_);
v___x_3091_ = lean_nat_dec_le(v___y_3088_, v___y_3089_);
lean_dec(v___y_3089_);
lean_dec(v___y_3088_);
if (v___x_3091_ == 0)
{
lean_object* v___x_3092_; 
v___x_3092_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3083_, v_s_x27_3084_);
return v___x_3092_;
}
else
{
lean_object* v___x_3093_; 
v___x_3093_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3083_, v_s_x27_3084_);
lean_dec_ref(v_s_x27_3084_);
lean_dec_ref(v_s_3083_);
return v___x_3093_;
}
}
else
{
size_t v_sz_3094_; size_t v___x_3095_; lean_object* v___x_3096_; 
lean_dec(v___y_3089_);
lean_dec(v___y_3088_);
lean_dec_ref(v_s_x27_3084_);
lean_dec_ref(v_s_3083_);
v_sz_3094_ = lean_array_size(v___y_3087_);
v___x_3095_ = ((size_t)0ULL);
v___x_3096_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_3094_, v___x_3095_, v___y_3087_);
return v___x_3096_;
}
}
v___jp_3097_:
{
lean_object* v_approxEditDistance_3102_; lean_object* v_charArrDiff_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; uint8_t v___x_3106_; 
v_approxEditDistance_3102_ = lean_array_get_size(v___y_3101_);
lean_dec_ref(v___y_3101_);
v_charArrDiff_3103_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v___y_3100_);
lean_dec_ref(v___y_3100_);
v___x_3104_ = lean_array_get_size(v_charArrDiff_3103_);
v___x_3105_ = lean_unsigned_to_nat(3u);
v___x_3106_ = lean_nat_dec_le(v___x_3104_, v___x_3105_);
if (v___x_3106_ == 0)
{
uint8_t v___x_3107_; 
v___x_3107_ = lean_nat_dec_le(v_approxEditDistance_3102_, v___y_3098_);
lean_dec(v___y_3098_);
v___y_3087_ = v_charArrDiff_3103_;
v___y_3088_ = v_approxEditDistance_3102_;
v___y_3089_ = v___y_3099_;
v___y_3090_ = v___x_3107_;
goto v___jp_3086_;
}
else
{
lean_dec(v___y_3098_);
v___y_3087_ = v_charArrDiff_3103_;
v___y_3088_ = v_approxEditDistance_3102_;
v___y_3089_ = v___y_3099_;
v___y_3090_ = v___x_3106_;
goto v___jp_3086_;
}
}
v___jp_3108_:
{
lean_object* v___x_3113_; lean_object* v_maxWordDiffDistance_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v_charDiffRaw_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; uint8_t v___x_3121_; 
v___x_3113_ = lean_nat_shiftr(v___y_3112_, v___y_3109_);
lean_dec(v___y_3112_);
v_maxWordDiffDistance_3114_ = lean_nat_add(v___y_3111_, v___x_3113_);
lean_dec(v___x_3113_);
lean_dec(v___y_3111_);
lean_inc_ref(v_s_3083_);
v___x_3115_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3083_);
lean_inc_ref(v_s_x27_3084_);
v___x_3116_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3084_);
v_charDiffRaw_3117_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3115_, v___x_3116_);
v___x_3118_ = lean_unsigned_to_nat(0u);
v___x_3119_ = lean_array_get_size(v_charDiffRaw_3117_);
v___x_3120_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0));
v___x_3121_ = lean_nat_dec_lt(v___x_3118_, v___x_3119_);
if (v___x_3121_ == 0)
{
v___y_3098_ = v___y_3110_;
v___y_3099_ = v_maxWordDiffDistance_3114_;
v___y_3100_ = v_charDiffRaw_3117_;
v___y_3101_ = v___x_3120_;
goto v___jp_3097_;
}
else
{
uint8_t v___x_3122_; 
v___x_3122_ = lean_nat_dec_le(v___x_3119_, v___x_3119_);
if (v___x_3122_ == 0)
{
if (v___x_3121_ == 0)
{
v___y_3098_ = v___y_3110_;
v___y_3099_ = v_maxWordDiffDistance_3114_;
v___y_3100_ = v_charDiffRaw_3117_;
v___y_3101_ = v___x_3120_;
goto v___jp_3097_;
}
else
{
size_t v___x_3123_; size_t v___x_3124_; lean_object* v___x_3125_; 
v___x_3123_ = ((size_t)0ULL);
v___x_3124_ = lean_usize_of_nat(v___x_3119_);
v___x_3125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3117_, v___x_3123_, v___x_3124_, v___x_3120_);
v___y_3098_ = v___y_3110_;
v___y_3099_ = v_maxWordDiffDistance_3114_;
v___y_3100_ = v_charDiffRaw_3117_;
v___y_3101_ = v___x_3125_;
goto v___jp_3097_;
}
}
else
{
size_t v___x_3126_; size_t v___x_3127_; lean_object* v___x_3128_; 
v___x_3126_ = ((size_t)0ULL);
v___x_3127_ = lean_usize_of_nat(v___x_3119_);
v___x_3128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3117_, v___x_3126_, v___x_3127_, v___x_3120_);
v___y_3098_ = v___y_3110_;
v___y_3099_ = v_maxWordDiffDistance_3114_;
v___y_3100_ = v_charDiffRaw_3117_;
v___y_3101_ = v___x_3128_;
goto v___jp_3097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff___boxed(lean_object* v_s_3148_, lean_object* v_s_x27_3149_, lean_object* v_granularity_3150_){
_start:
{
uint8_t v_granularity_boxed_3151_; lean_object* v_res_3152_; 
v_granularity_boxed_3151_ = lean_unbox(v_granularity_3150_);
v_res_3152_ = l_Lean_Meta_Hint_readableDiff(v_s_3148_, v_s_x27_3149_, v_granularity_boxed_3151_);
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(lean_object* v_as_3153_, size_t v_i_3154_, size_t v_stop_3155_, lean_object* v_b_3156_){
_start:
{
uint8_t v___x_3157_; 
v___x_3157_ = lean_usize_dec_eq(v_i_3154_, v_stop_3155_);
if (v___x_3157_ == 0)
{
lean_object* v___x_3158_; lean_object* v_snd_3159_; lean_object* v___x_3160_; size_t v___x_3161_; size_t v___x_3162_; 
v___x_3158_ = lean_array_uget_borrowed(v_as_3153_, v_i_3154_);
v_snd_3159_ = lean_ctor_get(v___x_3158_, 1);
v___x_3160_ = lean_string_append(v_b_3156_, v_snd_3159_);
v___x_3161_ = ((size_t)1ULL);
v___x_3162_ = lean_usize_add(v_i_3154_, v___x_3161_);
v_i_3154_ = v___x_3162_;
v_b_3156_ = v___x_3160_;
goto _start;
}
else
{
return v_b_3156_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0___boxed(lean_object* v_as_3164_, lean_object* v_i_3165_, lean_object* v_stop_3166_, lean_object* v_b_3167_){
_start:
{
size_t v_i_boxed_3168_; size_t v_stop_boxed_3169_; lean_object* v_res_3170_; 
v_i_boxed_3168_ = lean_unbox_usize(v_i_3165_);
lean_dec(v_i_3165_);
v_stop_boxed_3169_ = lean_unbox_usize(v_stop_3166_);
lean_dec(v_stop_3166_);
v_res_3170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v_as_3164_, v_i_boxed_3168_, v_stop_boxed_3169_, v_b_3167_);
lean_dec_ref(v_as_3164_);
return v_res_3170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(lean_object* v_t_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v___x_3174_; lean_object* v_infoState_3175_; uint8_t v_enabled_3176_; 
v___x_3174_ = lean_st_ref_get(v___y_3172_);
v_infoState_3175_ = lean_ctor_get(v___x_3174_, 7);
lean_inc_ref(v_infoState_3175_);
lean_dec(v___x_3174_);
v_enabled_3176_ = lean_ctor_get_uint8(v_infoState_3175_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3175_);
if (v_enabled_3176_ == 0)
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
lean_dec_ref(v_t_3171_);
v___x_3177_ = lean_box(0);
v___x_3178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
return v___x_3178_;
}
else
{
lean_object* v___x_3179_; lean_object* v_infoState_3180_; lean_object* v_env_3181_; lean_object* v_nextMacroScope_3182_; lean_object* v_ngen_3183_; lean_object* v_auxDeclNGen_3184_; lean_object* v_traceState_3185_; lean_object* v_cache_3186_; lean_object* v_messages_3187_; lean_object* v_snapshotTasks_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3210_; 
v___x_3179_ = lean_st_ref_take(v___y_3172_);
v_infoState_3180_ = lean_ctor_get(v___x_3179_, 7);
v_env_3181_ = lean_ctor_get(v___x_3179_, 0);
v_nextMacroScope_3182_ = lean_ctor_get(v___x_3179_, 1);
v_ngen_3183_ = lean_ctor_get(v___x_3179_, 2);
v_auxDeclNGen_3184_ = lean_ctor_get(v___x_3179_, 3);
v_traceState_3185_ = lean_ctor_get(v___x_3179_, 4);
v_cache_3186_ = lean_ctor_get(v___x_3179_, 5);
v_messages_3187_ = lean_ctor_get(v___x_3179_, 6);
v_snapshotTasks_3188_ = lean_ctor_get(v___x_3179_, 8);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3190_ = v___x_3179_;
v_isShared_3191_ = v_isSharedCheck_3210_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_snapshotTasks_3188_);
lean_inc(v_infoState_3180_);
lean_inc(v_messages_3187_);
lean_inc(v_cache_3186_);
lean_inc(v_traceState_3185_);
lean_inc(v_auxDeclNGen_3184_);
lean_inc(v_ngen_3183_);
lean_inc(v_nextMacroScope_3182_);
lean_inc(v_env_3181_);
lean_dec(v___x_3179_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3210_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
uint8_t v_enabled_3192_; lean_object* v_assignment_3193_; lean_object* v_lazyAssignment_3194_; lean_object* v_trees_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3209_; 
v_enabled_3192_ = lean_ctor_get_uint8(v_infoState_3180_, sizeof(void*)*3);
v_assignment_3193_ = lean_ctor_get(v_infoState_3180_, 0);
v_lazyAssignment_3194_ = lean_ctor_get(v_infoState_3180_, 1);
v_trees_3195_ = lean_ctor_get(v_infoState_3180_, 2);
v_isSharedCheck_3209_ = !lean_is_exclusive(v_infoState_3180_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3197_ = v_infoState_3180_;
v_isShared_3198_ = v_isSharedCheck_3209_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_trees_3195_);
lean_inc(v_lazyAssignment_3194_);
lean_inc(v_assignment_3193_);
lean_dec(v_infoState_3180_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3209_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3199_; lean_object* v___x_3201_; 
v___x_3199_ = l_Lean_PersistentArray_push___redArg(v_trees_3195_, v_t_3171_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 2, v___x_3199_);
v___x_3201_ = v___x_3197_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_assignment_3193_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v_lazyAssignment_3194_);
lean_ctor_set(v_reuseFailAlloc_3208_, 2, v___x_3199_);
lean_ctor_set_uint8(v_reuseFailAlloc_3208_, sizeof(void*)*3, v_enabled_3192_);
v___x_3201_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
lean_object* v___x_3203_; 
if (v_isShared_3191_ == 0)
{
lean_ctor_set(v___x_3190_, 7, v___x_3201_);
v___x_3203_ = v___x_3190_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_env_3181_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v_nextMacroScope_3182_);
lean_ctor_set(v_reuseFailAlloc_3207_, 2, v_ngen_3183_);
lean_ctor_set(v_reuseFailAlloc_3207_, 3, v_auxDeclNGen_3184_);
lean_ctor_set(v_reuseFailAlloc_3207_, 4, v_traceState_3185_);
lean_ctor_set(v_reuseFailAlloc_3207_, 5, v_cache_3186_);
lean_ctor_set(v_reuseFailAlloc_3207_, 6, v_messages_3187_);
lean_ctor_set(v_reuseFailAlloc_3207_, 7, v___x_3201_);
lean_ctor_set(v_reuseFailAlloc_3207_, 8, v_snapshotTasks_3188_);
v___x_3203_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v___x_3204_ = lean_st_ref_set(v___y_3172_, v___x_3203_);
v___x_3205_ = lean_box(0);
v___x_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3205_);
return v___x_3206_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg___boxed(lean_object* v_t_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3211_, v___y_3212_);
lean_dec(v___y_3212_);
return v_res_3214_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3215_ = lean_unsigned_to_nat(32u);
v___x_3216_ = lean_mk_empty_array_with_capacity(v___x_3215_);
v___x_3217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
return v___x_3217_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1(void){
_start:
{
size_t v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3218_ = ((size_t)5ULL);
v___x_3219_ = lean_unsigned_to_nat(0u);
v___x_3220_ = lean_unsigned_to_nat(32u);
v___x_3221_ = lean_mk_empty_array_with_capacity(v___x_3220_);
v___x_3222_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0);
v___x_3223_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
lean_ctor_set(v___x_3223_, 1, v___x_3221_);
lean_ctor_set(v___x_3223_, 2, v___x_3219_);
lean_ctor_set(v___x_3223_, 3, v___x_3219_);
lean_ctor_set_usize(v___x_3223_, 4, v___x_3218_);
return v___x_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(lean_object* v_t_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v___x_3228_; lean_object* v_infoState_3229_; uint8_t v_enabled_3230_; 
v___x_3228_ = lean_st_ref_get(v___y_3226_);
v_infoState_3229_ = lean_ctor_get(v___x_3228_, 7);
lean_inc_ref(v_infoState_3229_);
lean_dec(v___x_3228_);
v_enabled_3230_ = lean_ctor_get_uint8(v_infoState_3229_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3229_);
if (v_enabled_3230_ == 0)
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
lean_dec_ref(v_t_3224_);
v___x_3231_ = lean_box(0);
v___x_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
return v___x_3232_;
}
else
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3233_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1);
v___x_3234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3234_, 0, v_t_3224_);
lean_ctor_set(v___x_3234_, 1, v___x_3233_);
v___x_3235_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v___x_3234_, v___y_3226_);
return v___x_3235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___boxed(lean_object* v_t_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v_t_3236_, v___y_3237_, v___y_3238_);
lean_dec(v___y_3238_);
lean_dec_ref(v___y_3237_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0(lean_object* v___x_3241_, lean_object* v___y_3242_){
_start:
{
lean_object* v___x_3243_; 
v___x_3243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3241_);
lean_ctor_set(v___x_3243_, 1, v___y_3242_);
return v___x_3243_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__0));
v___x_3246_ = l_Lean_stringToMessageData(v___x_3245_);
return v___x_3246_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3248_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__2));
v___x_3249_ = l_Lean_stringToMessageData(v___x_3248_);
return v___x_3249_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29(void){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3298_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__28));
v___x_3299_ = l_Lean_Json_mkObj(v___x_3298_);
return v___x_3299_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30(void){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3300_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29);
v___x_3301_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__19));
v___x_3302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
lean_ctor_set(v___x_3302_, 1, v___x_3300_);
return v___x_3302_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31(void){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3303_ = lean_box(0);
v___x_3304_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30);
v___x_3305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3304_);
lean_ctor_set(v___x_3305_, 1, v___x_3303_);
return v___x_3305_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33(void){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3308_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__32));
v___x_3309_ = l_Lean_MessageData_ofFormat(v___x_3308_);
return v___x_3309_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35(void){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3311_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__34));
v___x_3312_ = l_Lean_stringToMessageData(v___x_3311_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(lean_object* v_suggestions_3314_, uint8_t v_forceList_3315_, lean_object* v_codeActionPrefix_x3f_3316_, lean_object* v_ref_3317_, lean_object* v_as_3318_, size_t v_sz_3319_, size_t v_i_3320_, lean_object* v_b_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v_a_3326_; lean_object* v___y_3331_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3342_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; uint8_t v___x_3370_; 
v___x_3370_ = lean_usize_dec_lt(v_i_3320_, v_sz_3319_);
if (v___x_3370_ == 0)
{
lean_object* v___x_3371_; 
lean_dec(v_ref_3317_);
lean_dec(v_codeActionPrefix_x3f_3316_);
v___x_3371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3371_, 0, v_b_3321_);
return v___x_3371_;
}
else
{
lean_object* v_a_3372_; lean_object* v_span_x3f_3373_; lean_object* v___x_3374_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; uint8_t v___y_3381_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; uint8_t v___y_3416_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; uint8_t v___y_3462_; lean_object* v___y_3465_; lean_object* v___y_3466_; uint8_t v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; uint8_t v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3475_; lean_object* v___y_3476_; uint8_t v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v_postInfo_x3f_3480_; lean_object* v___y_3481_; uint8_t v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3486_; uint8_t v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; uint8_t v___y_3491_; lean_object* v_edits_3492_; lean_object* v___y_3498_; lean_object* v_stop_3499_; uint8_t v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; uint8_t v___y_3506_; lean_object* v_edits_3507_; lean_object* v___y_3516_; lean_object* v___y_3517_; uint8_t v___y_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v___y_3523_; uint8_t v___y_3524_; lean_object* v_edits_3525_; lean_object* v___y_3526_; lean_object* v___x_3550_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; uint8_t v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; uint8_t v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3597_; lean_object* v___y_3598_; uint8_t v___y_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; uint8_t v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3615_; 
v_a_3372_ = lean_array_uget_borrowed(v_as_3318_, v_i_3320_);
v_span_x3f_3373_ = lean_ctor_get(v_a_3372_, 1);
v___x_3374_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_3550_ = l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_;
if (lean_obj_tag(v_span_x3f_3373_) == 0)
{
lean_inc(v_ref_3317_);
v___y_3615_ = v_ref_3317_;
goto v___jp_3614_;
}
else
{
lean_object* v_val_3636_; 
v_val_3636_ = lean_ctor_get(v_span_x3f_3373_, 0);
lean_inc(v_val_3636_);
v___y_3615_ = v_val_3636_;
goto v___jp_3614_;
}
v___jp_3375_:
{
lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___f_3396_; 
lean_inc_ref(v___y_3378_);
v___x_3382_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson(v___y_3378_);
v___x_3383_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__9));
v___x_3384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3383_);
lean_ctor_set(v___x_3384_, 1, v___x_3382_);
v___x_3385_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3386_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3386_, 0, v___y_3377_);
v___x_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3385_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
v___x_3388_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3389_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3380_);
v___x_3390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3388_);
lean_ctor_set(v___x_3390_, 1, v___x_3389_);
v___x_3391_ = lean_box(0);
v___x_3392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3390_);
lean_ctor_set(v___x_3392_, 1, v___x_3391_);
v___x_3393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3387_);
lean_ctor_set(v___x_3393_, 1, v___x_3392_);
v___x_3394_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3384_);
lean_ctor_set(v___x_3394_, 1, v___x_3393_);
v___x_3395_ = l_Lean_Json_mkObj(v___x_3394_);
lean_dec_ref_known(v___x_3394_, 2);
v___f_3396_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3396_, 0, v___x_3395_);
if (v___y_3381_ == 0)
{
lean_object* v___x_3397_; 
v___x_3397_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString(v___y_3378_);
v___y_3350_ = v___y_3379_;
v___y_3351_ = v___y_3376_;
v___y_3352_ = v___f_3396_;
v___y_3353_ = v___x_3397_;
goto v___jp_3349_;
}
else
{
lean_object* v___x_3398_; lean_object* v___x_3399_; uint8_t v___x_3400_; 
v___x_3398_ = lean_unsigned_to_nat(0u);
v___x_3399_ = lean_array_get_size(v___y_3378_);
v___x_3400_ = lean_nat_dec_lt(v___x_3398_, v___x_3399_);
if (v___x_3400_ == 0)
{
lean_dec_ref(v___y_3378_);
v___y_3350_ = v___y_3379_;
v___y_3351_ = v___y_3376_;
v___y_3352_ = v___f_3396_;
v___y_3353_ = v___x_3374_;
goto v___jp_3349_;
}
else
{
uint8_t v___x_3401_; 
v___x_3401_ = lean_nat_dec_le(v___x_3399_, v___x_3399_);
if (v___x_3401_ == 0)
{
if (v___x_3400_ == 0)
{
lean_dec_ref(v___y_3378_);
v___y_3350_ = v___y_3379_;
v___y_3351_ = v___y_3376_;
v___y_3352_ = v___f_3396_;
v___y_3353_ = v___x_3374_;
goto v___jp_3349_;
}
else
{
size_t v___x_3402_; size_t v___x_3403_; lean_object* v___x_3404_; 
v___x_3402_ = ((size_t)0ULL);
v___x_3403_ = lean_usize_of_nat(v___x_3399_);
v___x_3404_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3378_, v___x_3402_, v___x_3403_, v___x_3374_);
lean_dec_ref(v___y_3378_);
v___y_3350_ = v___y_3379_;
v___y_3351_ = v___y_3376_;
v___y_3352_ = v___f_3396_;
v___y_3353_ = v___x_3404_;
goto v___jp_3349_;
}
}
else
{
size_t v___x_3405_; size_t v___x_3406_; lean_object* v___x_3407_; 
v___x_3405_ = ((size_t)0ULL);
v___x_3406_ = lean_usize_of_nat(v___x_3399_);
v___x_3407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3378_, v___x_3405_, v___x_3406_, v___x_3374_);
lean_dec_ref(v___y_3378_);
v___y_3350_ = v___y_3379_;
v___y_3351_ = v___y_3376_;
v___y_3352_ = v___f_3396_;
v___y_3353_ = v___x_3407_;
goto v___jp_3349_;
}
}
}
}
v___jp_3408_:
{
if (lean_obj_tag(v___y_3412_) == 0)
{
lean_object* v___x_3417_; uint64_t v_javascriptHash_3418_; lean_object* v_suggestion_3419_; lean_object* v_messageData_x3f_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___f_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
lean_dec_ref(v___y_3411_);
v___x_3417_ = l_Lean_Meta_Hint_textInsertionWidget;
v_javascriptHash_3418_ = lean_ctor_get_uint64(v___x_3417_, sizeof(void*)*1);
v_suggestion_3419_ = lean_ctor_get(v___y_3413_, 0);
lean_inc_ref(v_suggestion_3419_);
v_messageData_x3f_3420_ = lean_ctor_get(v___y_3413_, 4);
lean_inc(v_messageData_x3f_3420_);
lean_dec_ref(v___y_3413_);
v___x_3421_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18));
v___x_3422_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3423_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3415_);
v___x_3424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3422_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
v___x_3425_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3426_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3426_, 0, v___y_3410_);
v___x_3427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3425_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
v___x_3428_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31);
v___x_3429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3427_);
lean_ctor_set(v___x_3429_, 1, v___x_3428_);
v___x_3430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3424_);
lean_ctor_set(v___x_3430_, 1, v___x_3429_);
v___x_3431_ = l_Lean_Json_mkObj(v___x_3430_);
lean_dec_ref_known(v___x_3430_, 2);
v___f_3432_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3432_, 0, v___x_3431_);
v___x_3433_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3433_, 0, v___x_3421_);
lean_ctor_set(v___x_3433_, 1, v___f_3432_);
lean_ctor_set_uint64(v___x_3433_, sizeof(void*)*2, v_javascriptHash_3418_);
v___x_3434_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33);
v___x_3435_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3435_, 0, v___x_3433_);
lean_ctor_set(v___x_3435_, 1, v___x_3434_);
v___x_3436_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3436_);
lean_ctor_set(v___x_3437_, 1, v___x_3435_);
v___x_3438_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35);
v___x_3439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3439_, 0, v___x_3437_);
lean_ctor_set(v___x_3439_, 1, v___x_3438_);
v___x_3440_ = l_Lean_stringToMessageData(v___y_3414_);
v___x_3441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3439_);
lean_ctor_set(v___x_3441_, 1, v___x_3440_);
if (lean_obj_tag(v_messageData_x3f_3420_) == 0)
{
if (lean_obj_tag(v_suggestion_3419_) == 0)
{
lean_object* v_a_3442_; lean_object* v___x_3443_; 
v_a_3442_ = lean_ctor_get(v_suggestion_3419_, 1);
lean_inc(v_a_3442_);
lean_dec_ref_known(v_suggestion_3419_, 2);
v___x_3443_ = l_Lean_MessageData_ofSyntax(v_a_3442_);
v___y_3335_ = v___y_3409_;
v___y_3336_ = v___x_3441_;
v___y_3337_ = v___x_3443_;
goto v___jp_3334_;
}
else
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3452_; 
v_a_3444_ = lean_ctor_get(v_suggestion_3419_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v_suggestion_3419_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3446_ = v_suggestion_3419_;
v_isShared_3447_ = v_isSharedCheck_3452_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v_suggestion_3419_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3452_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
lean_ctor_set_tag(v___x_3446_, 3);
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3444_);
v___x_3449_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
lean_object* v___x_3450_; 
v___x_3450_ = l_Lean_MessageData_ofFormat(v___x_3449_);
v___y_3335_ = v___y_3409_;
v___y_3336_ = v___x_3441_;
v___y_3337_ = v___x_3450_;
goto v___jp_3334_;
}
}
}
}
else
{
lean_object* v_val_3453_; 
lean_dec_ref(v_suggestion_3419_);
v_val_3453_ = lean_ctor_get(v_messageData_x3f_3420_, 0);
lean_inc(v_val_3453_);
lean_dec_ref_known(v_messageData_x3f_3420_, 1);
v___y_3335_ = v___y_3409_;
v___y_3336_ = v___x_3441_;
v___y_3337_ = v_val_3453_;
goto v___jp_3334_;
}
}
else
{
lean_dec_ref_known(v___y_3412_, 1);
lean_dec_ref(v___y_3413_);
v___y_3376_ = v___y_3409_;
v___y_3377_ = v___y_3410_;
v___y_3378_ = v___y_3411_;
v___y_3379_ = v___y_3414_;
v___y_3380_ = v___y_3415_;
v___y_3381_ = v___y_3416_;
goto v___jp_3375_;
}
}
v___jp_3454_:
{
if (v___y_3462_ == 0)
{
lean_object* v_messageData_x3f_3463_; 
v_messageData_x3f_3463_ = lean_ctor_get(v___y_3459_, 4);
if (lean_obj_tag(v_messageData_x3f_3463_) == 0)
{
lean_dec_ref(v___y_3459_);
lean_dec(v___y_3458_);
v___y_3376_ = v___y_3455_;
v___y_3377_ = v___y_3456_;
v___y_3378_ = v___y_3457_;
v___y_3379_ = v___y_3461_;
v___y_3380_ = v___y_3460_;
v___y_3381_ = v___y_3462_;
goto v___jp_3375_;
}
else
{
v___y_3409_ = v___y_3455_;
v___y_3410_ = v___y_3456_;
v___y_3411_ = v___y_3457_;
v___y_3412_ = v___y_3458_;
v___y_3413_ = v___y_3459_;
v___y_3414_ = v___y_3461_;
v___y_3415_ = v___y_3460_;
v___y_3416_ = v___y_3462_;
goto v___jp_3408_;
}
}
else
{
v___y_3409_ = v___y_3455_;
v___y_3410_ = v___y_3456_;
v___y_3411_ = v___y_3457_;
v___y_3412_ = v___y_3458_;
v___y_3413_ = v___y_3459_;
v___y_3414_ = v___y_3461_;
v___y_3415_ = v___y_3460_;
v___y_3416_ = v___y_3462_;
goto v___jp_3408_;
}
}
v___jp_3464_:
{
if (v___y_3472_ == 4)
{
v___y_3455_ = v___y_3473_;
v___y_3456_ = v___y_3465_;
v___y_3457_ = v___y_3466_;
v___y_3458_ = v___y_3468_;
v___y_3459_ = v___y_3471_;
v___y_3460_ = v___y_3470_;
v___y_3461_ = v___y_3469_;
v___y_3462_ = v___x_3370_;
goto v___jp_3454_;
}
else
{
v___y_3455_ = v___y_3473_;
v___y_3456_ = v___y_3465_;
v___y_3457_ = v___y_3466_;
v___y_3458_ = v___y_3468_;
v___y_3459_ = v___y_3471_;
v___y_3460_ = v___y_3470_;
v___y_3461_ = v___y_3469_;
v___y_3462_ = v___y_3467_;
goto v___jp_3454_;
}
}
v___jp_3474_:
{
if (lean_obj_tag(v_postInfo_x3f_3480_) == 0)
{
v___y_3465_ = v___y_3475_;
v___y_3466_ = v___y_3476_;
v___y_3467_ = v___y_3477_;
v___y_3468_ = v___y_3478_;
v___y_3469_ = v___y_3483_;
v___y_3470_ = v___y_3481_;
v___y_3471_ = v___y_3479_;
v___y_3472_ = v___y_3482_;
v___y_3473_ = v___x_3374_;
goto v___jp_3464_;
}
else
{
lean_object* v_val_3484_; 
v_val_3484_ = lean_ctor_get(v_postInfo_x3f_3480_, 0);
lean_inc(v_val_3484_);
lean_dec_ref_known(v_postInfo_x3f_3480_, 1);
v___y_3465_ = v___y_3475_;
v___y_3466_ = v___y_3476_;
v___y_3467_ = v___y_3477_;
v___y_3468_ = v___y_3478_;
v___y_3469_ = v___y_3483_;
v___y_3470_ = v___y_3481_;
v___y_3471_ = v___y_3479_;
v___y_3472_ = v___y_3482_;
v___y_3473_ = v_val_3484_;
goto v___jp_3464_;
}
}
v___jp_3485_:
{
lean_object* v_preInfo_x3f_3493_; 
v_preInfo_x3f_3493_ = lean_ctor_get(v___y_3490_, 1);
if (lean_obj_tag(v_preInfo_x3f_3493_) == 0)
{
lean_object* v_postInfo_x3f_3494_; 
v_postInfo_x3f_3494_ = lean_ctor_get(v___y_3490_, 2);
lean_inc(v_postInfo_x3f_3494_);
v___y_3475_ = v___y_3486_;
v___y_3476_ = v_edits_3492_;
v___y_3477_ = v___y_3487_;
v___y_3478_ = v___y_3488_;
v___y_3479_ = v___y_3490_;
v_postInfo_x3f_3480_ = v_postInfo_x3f_3494_;
v___y_3481_ = v___y_3489_;
v___y_3482_ = v___y_3491_;
v___y_3483_ = v___x_3374_;
goto v___jp_3474_;
}
else
{
lean_object* v_postInfo_x3f_3495_; lean_object* v_val_3496_; 
v_postInfo_x3f_3495_ = lean_ctor_get(v___y_3490_, 2);
lean_inc(v_postInfo_x3f_3495_);
v_val_3496_ = lean_ctor_get(v_preInfo_x3f_3493_, 0);
lean_inc(v_val_3496_);
v___y_3475_ = v___y_3486_;
v___y_3476_ = v_edits_3492_;
v___y_3477_ = v___y_3487_;
v___y_3478_ = v___y_3488_;
v___y_3479_ = v___y_3490_;
v_postInfo_x3f_3480_ = v_postInfo_x3f_3495_;
v___y_3481_ = v___y_3489_;
v___y_3482_ = v___y_3491_;
v___y_3483_ = v_val_3496_;
goto v___jp_3474_;
}
}
v___jp_3497_:
{
uint8_t v___x_3508_; 
v___x_3508_ = lean_nat_dec_lt(v___y_3502_, v_stop_3499_);
if (v___x_3508_ == 0)
{
lean_dec(v___y_3502_);
lean_dec(v_stop_3499_);
v___y_3486_ = v___y_3498_;
v___y_3487_ = v___y_3500_;
v___y_3488_ = v___y_3501_;
v___y_3489_ = v___y_3505_;
v___y_3490_ = v___y_3504_;
v___y_3491_ = v___y_3506_;
v_edits_3492_ = v_edits_3507_;
goto v___jp_3485_;
}
else
{
lean_object* v_source_3509_; uint8_t v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v_source_3509_ = lean_ctor_get(v___y_3503_, 0);
v___x_3510_ = 2;
v___x_3511_ = lean_string_utf8_extract(v_source_3509_, v___y_3502_, v_stop_3499_);
lean_dec(v_stop_3499_);
lean_dec(v___y_3502_);
v___x_3512_ = lean_box(v___x_3510_);
v___x_3513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3512_);
lean_ctor_set(v___x_3513_, 1, v___x_3511_);
v___x_3514_ = lean_array_push(v_edits_3507_, v___x_3513_);
v___y_3486_ = v___y_3498_;
v___y_3487_ = v___y_3500_;
v___y_3488_ = v___y_3501_;
v___y_3489_ = v___y_3505_;
v___y_3490_ = v___y_3504_;
v___y_3491_ = v___y_3506_;
v_edits_3492_ = v___x_3514_;
goto v___jp_3485_;
}
}
v___jp_3515_:
{
if (lean_obj_tag(v___y_3521_) == 0)
{
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec(v___y_3517_);
v___y_3486_ = v___y_3516_;
v___y_3487_ = v___y_3518_;
v___y_3488_ = v___y_3521_;
v___y_3489_ = v___y_3523_;
v___y_3490_ = v___y_3522_;
v___y_3491_ = v___y_3524_;
v_edits_3492_ = v_edits_3525_;
goto v___jp_3485_;
}
else
{
lean_object* v_val_3527_; lean_object* v___x_3528_; 
v_val_3527_ = lean_ctor_get(v___y_3521_, 0);
v___x_3528_ = l_Lean_Syntax_getRange_x3f(v_val_3527_, v___y_3518_);
if (lean_obj_tag(v___x_3528_) == 1)
{
lean_object* v_val_3529_; uint8_t v___x_3530_; 
v_val_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_val_3529_);
lean_dec_ref_known(v___x_3528_, 1);
v___x_3530_ = l_Lean_Syntax_Range_includes(v_val_3529_, v___y_3520_, v___y_3518_, v___y_3518_);
lean_dec_ref(v___y_3520_);
if (v___x_3530_ == 0)
{
lean_dec(v_val_3529_);
lean_dec(v___y_3519_);
lean_dec(v___y_3517_);
v___y_3486_ = v___y_3516_;
v___y_3487_ = v___y_3518_;
v___y_3488_ = v___y_3521_;
v___y_3489_ = v___y_3523_;
v___y_3490_ = v___y_3522_;
v___y_3491_ = v___y_3524_;
v_edits_3492_ = v_edits_3525_;
goto v___jp_3485_;
}
else
{
lean_object* v_fileMap_3531_; lean_object* v_start_3532_; lean_object* v_stop_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3549_; 
v_fileMap_3531_ = lean_ctor_get(v___y_3526_, 1);
v_start_3532_ = lean_ctor_get(v_val_3529_, 0);
v_stop_3533_ = lean_ctor_get(v_val_3529_, 1);
v_isSharedCheck_3549_ = !lean_is_exclusive(v_val_3529_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3535_ = v_val_3529_;
v_isShared_3536_ = v_isSharedCheck_3549_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_stop_3533_);
lean_inc(v_start_3532_);
lean_dec(v_val_3529_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3549_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
uint8_t v___x_3537_; 
v___x_3537_ = lean_nat_dec_lt(v_start_3532_, v___y_3517_);
if (v___x_3537_ == 0)
{
lean_del_object(v___x_3535_);
lean_dec(v_start_3532_);
lean_dec(v___y_3517_);
v___y_3498_ = v___y_3516_;
v_stop_3499_ = v_stop_3533_;
v___y_3500_ = v___y_3518_;
v___y_3501_ = v___y_3521_;
v___y_3502_ = v___y_3519_;
v___y_3503_ = v_fileMap_3531_;
v___y_3504_ = v___y_3522_;
v___y_3505_ = v___y_3523_;
v___y_3506_ = v___y_3524_;
v_edits_3507_ = v_edits_3525_;
goto v___jp_3497_;
}
else
{
lean_object* v_source_3538_; uint8_t v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___x_3543_; 
v_source_3538_ = lean_ctor_get(v_fileMap_3531_, 0);
v___x_3539_ = 2;
v___x_3540_ = lean_string_utf8_extract(v_source_3538_, v_start_3532_, v___y_3517_);
lean_dec(v___y_3517_);
lean_dec(v_start_3532_);
v___x_3541_ = lean_box(v___x_3539_);
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 1, v___x_3540_);
lean_ctor_set(v___x_3535_, 0, v___x_3541_);
v___x_3543_ = v___x_3535_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3541_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v___x_3540_);
v___x_3543_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3544_ = lean_unsigned_to_nat(1u);
v___x_3545_ = lean_mk_empty_array_with_capacity(v___x_3544_);
v___x_3546_ = lean_array_push(v___x_3545_, v___x_3543_);
v___x_3547_ = l_Array_append___redArg(v___x_3546_, v_edits_3525_);
lean_dec_ref(v_edits_3525_);
v___y_3498_ = v___y_3516_;
v_stop_3499_ = v_stop_3533_;
v___y_3500_ = v___y_3518_;
v___y_3501_ = v___y_3521_;
v___y_3502_ = v___y_3519_;
v___y_3503_ = v_fileMap_3531_;
v___y_3504_ = v___y_3522_;
v___y_3505_ = v___y_3523_;
v___y_3506_ = v___y_3524_;
v_edits_3507_ = v___x_3547_;
goto v___jp_3497_;
}
}
}
}
}
else
{
lean_dec(v___x_3528_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec(v___y_3517_);
v___y_3486_ = v___y_3516_;
v___y_3487_ = v___y_3518_;
v___y_3488_ = v___y_3521_;
v___y_3489_ = v___y_3523_;
v___y_3490_ = v___y_3522_;
v___y_3491_ = v___y_3524_;
v_edits_3492_ = v_edits_3525_;
goto v___jp_3485_;
}
}
}
v___jp_3551_:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
lean_inc_ref(v___y_3559_);
v___x_3562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3562_, 0, v___y_3554_);
lean_ctor_set(v___x_3562_, 1, v___y_3561_);
lean_ctor_set(v___x_3562_, 2, v___y_3559_);
v___x_3563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3550_);
lean_ctor_set(v___x_3563_, 1, v___x_3562_);
v___x_3564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3564_, 0, v___y_3552_);
lean_ctor_set(v___x_3564_, 1, v___x_3563_);
v___x_3565_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3564_);
v___x_3566_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v___x_3565_, v___y_3322_, v___y_3323_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_object* v_messageData_x3f_3567_; 
lean_dec_ref_known(v___x_3566_, 1);
v_messageData_x3f_3567_ = lean_ctor_get(v___y_3559_, 4);
if (lean_obj_tag(v_messageData_x3f_3567_) == 1)
{
lean_object* v_start_3568_; lean_object* v_stop_3569_; lean_object* v_val_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; uint8_t v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v_start_3568_ = lean_ctor_get(v___y_3557_, 0);
lean_inc(v_start_3568_);
v_stop_3569_ = lean_ctor_get(v___y_3557_, 1);
lean_inc(v_stop_3569_);
v_val_3570_ = lean_ctor_get(v_messageData_x3f_3567_, 0);
v___x_3571_ = lean_box(0);
lean_inc(v_val_3570_);
v___x_3572_ = l_Lean_MessageData_format(v_val_3570_, v___x_3571_);
v___x_3573_ = 0;
v___x_3574_ = l_Std_Format_defWidth;
v___x_3575_ = lean_unsigned_to_nat(0u);
v___x_3576_ = l_Std_Format_pretty(v___x_3572_, v___x_3574_, v___x_3575_, v___x_3575_);
v___x_3577_ = lean_box(v___x_3573_);
v___x_3578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
lean_ctor_set(v___x_3578_, 1, v___x_3576_);
v___x_3579_ = lean_unsigned_to_nat(1u);
v___x_3580_ = lean_mk_empty_array_with_capacity(v___x_3579_);
v___x_3581_ = lean_array_push(v___x_3580_, v___x_3578_);
v___y_3516_ = v___y_3553_;
v___y_3517_ = v_start_3568_;
v___y_3518_ = v___y_3555_;
v___y_3519_ = v_stop_3569_;
v___y_3520_ = v___y_3557_;
v___y_3521_ = v___y_3556_;
v___y_3522_ = v___y_3559_;
v___y_3523_ = v___y_3558_;
v___y_3524_ = v___y_3560_;
v_edits_3525_ = v___x_3581_;
v___y_3526_ = v___y_3322_;
goto v___jp_3515_;
}
else
{
lean_object* v_fileMap_3582_; lean_object* v_start_3583_; lean_object* v_stop_3584_; lean_object* v_source_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v_fileMap_3582_ = lean_ctor_get(v___y_3322_, 1);
v_start_3583_ = lean_ctor_get(v___y_3557_, 0);
lean_inc(v_start_3583_);
v_stop_3584_ = lean_ctor_get(v___y_3557_, 1);
lean_inc(v_stop_3584_);
v_source_3585_ = lean_ctor_get(v_fileMap_3582_, 0);
v___x_3586_ = lean_string_utf8_extract(v_source_3585_, v_start_3583_, v_stop_3584_);
lean_inc_ref(v___y_3553_);
v___x_3587_ = l_Lean_Meta_Hint_readableDiff(v___x_3586_, v___y_3553_, v___y_3560_);
v___y_3516_ = v___y_3553_;
v___y_3517_ = v_start_3583_;
v___y_3518_ = v___y_3555_;
v___y_3519_ = v_stop_3584_;
v___y_3520_ = v___y_3557_;
v___y_3521_ = v___y_3556_;
v___y_3522_ = v___y_3559_;
v___y_3523_ = v___y_3558_;
v___y_3524_ = v___y_3560_;
v_edits_3525_ = v___x_3587_;
v___y_3526_ = v___y_3322_;
goto v___jp_3515_;
}
}
else
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3595_; 
lean_dec_ref(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3553_);
lean_dec_ref(v_b_3321_);
lean_dec(v_ref_3317_);
lean_dec(v_codeActionPrefix_x3f_3316_);
v_a_3588_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3590_ = v___x_3566_;
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3566_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3595_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3593_; 
if (v_isShared_3591_ == 0)
{
v___x_3593_ = v___x_3590_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_a_3588_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
v___jp_3596_:
{
lean_object* v_toCodeActionTitle_x3f_3606_; lean_object* v___x_3607_; 
v_toCodeActionTitle_x3f_3606_ = lean_ctor_get(v___y_3602_, 5);
v___x_3607_ = l_Lean_Syntax_ofRange(v___y_3605_, v___x_3370_);
if (lean_obj_tag(v_toCodeActionTitle_x3f_3606_) == 0)
{
if (lean_obj_tag(v_codeActionPrefix_x3f_3316_) == 0)
{
lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3608_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__36));
v___x_3609_ = lean_string_append(v___x_3608_, v___y_3597_);
v___y_3552_ = v___x_3607_;
v___y_3553_ = v___y_3597_;
v___y_3554_ = v___y_3598_;
v___y_3555_ = v___y_3599_;
v___y_3556_ = v___y_3601_;
v___y_3557_ = v___y_3600_;
v___y_3558_ = v___y_3603_;
v___y_3559_ = v___y_3602_;
v___y_3560_ = v___y_3604_;
v___y_3561_ = v___x_3609_;
goto v___jp_3551_;
}
else
{
lean_object* v_val_3610_; lean_object* v___x_3611_; 
v_val_3610_ = lean_ctor_get(v_codeActionPrefix_x3f_3316_, 0);
lean_inc(v_val_3610_);
v___x_3611_ = lean_string_append(v_val_3610_, v___y_3597_);
v___y_3552_ = v___x_3607_;
v___y_3553_ = v___y_3597_;
v___y_3554_ = v___y_3598_;
v___y_3555_ = v___y_3599_;
v___y_3556_ = v___y_3601_;
v___y_3557_ = v___y_3600_;
v___y_3558_ = v___y_3603_;
v___y_3559_ = v___y_3602_;
v___y_3560_ = v___y_3604_;
v___y_3561_ = v___x_3611_;
goto v___jp_3551_;
}
}
else
{
lean_object* v_val_3612_; lean_object* v___x_3613_; 
v_val_3612_ = lean_ctor_get(v_toCodeActionTitle_x3f_3606_, 0);
lean_inc(v_val_3612_);
lean_inc_ref(v___y_3597_);
v___x_3613_ = lean_apply_1(v_val_3612_, v___y_3597_);
v___y_3552_ = v___x_3607_;
v___y_3553_ = v___y_3597_;
v___y_3554_ = v___y_3598_;
v___y_3555_ = v___y_3599_;
v___y_3556_ = v___y_3601_;
v___y_3557_ = v___y_3600_;
v___y_3558_ = v___y_3603_;
v___y_3559_ = v___y_3602_;
v___y_3560_ = v___y_3604_;
v___y_3561_ = v___x_3613_;
goto v___jp_3551_;
}
}
v___jp_3614_:
{
uint8_t v___x_3616_; lean_object* v___x_3617_; 
v___x_3616_ = 0;
v___x_3617_ = l_Lean_Syntax_getRange_x3f(v___y_3615_, v___x_3616_);
lean_dec(v___y_3615_);
if (lean_obj_tag(v___x_3617_) == 1)
{
lean_object* v_val_3618_; lean_object* v_toTryThisSuggestion_3619_; lean_object* v_previewSpan_x3f_3620_; uint8_t v_diffGranularity_3621_; lean_object* v___x_3622_; 
v_val_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc_n(v_val_3618_, 2);
lean_dec_ref_known(v___x_3617_, 1);
v_toTryThisSuggestion_3619_ = lean_ctor_get(v_a_3372_, 0);
v_previewSpan_x3f_3620_ = lean_ctor_get(v_a_3372_, 2);
v_diffGranularity_3621_ = lean_ctor_get_uint8(v_a_3372_, sizeof(void*)*3);
lean_inc_ref(v_toTryThisSuggestion_3619_);
v___x_3622_ = l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(v_toTryThisSuggestion_3619_, v_val_3618_, v___y_3322_, v___y_3323_);
if (lean_obj_tag(v___x_3622_) == 0)
{
lean_object* v_a_3623_; lean_object* v_range_3624_; lean_object* v_newText_3625_; lean_object* v___x_3626_; 
v_a_3623_ = lean_ctor_get(v___x_3622_, 0);
lean_inc(v_a_3623_);
lean_dec_ref_known(v___x_3622_, 1);
v_range_3624_ = lean_ctor_get(v_a_3623_, 0);
lean_inc_ref(v_range_3624_);
v_newText_3625_ = lean_ctor_get(v_a_3623_, 1);
lean_inc_ref(v_newText_3625_);
v___x_3626_ = l_Lean_Syntax_getRange_x3f(v_ref_3317_, v___x_3616_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_inc_ref(v_toTryThisSuggestion_3619_);
lean_inc(v_previewSpan_x3f_3620_);
lean_inc(v_val_3618_);
v___y_3597_ = v_newText_3625_;
v___y_3598_ = v_a_3623_;
v___y_3599_ = v___x_3616_;
v___y_3600_ = v_val_3618_;
v___y_3601_ = v_previewSpan_x3f_3620_;
v___y_3602_ = v_toTryThisSuggestion_3619_;
v___y_3603_ = v_range_3624_;
v___y_3604_ = v_diffGranularity_3621_;
v___y_3605_ = v_val_3618_;
goto v___jp_3596_;
}
else
{
lean_object* v_val_3627_; 
v_val_3627_ = lean_ctor_get(v___x_3626_, 0);
lean_inc(v_val_3627_);
lean_dec_ref_known(v___x_3626_, 1);
lean_inc_ref(v_toTryThisSuggestion_3619_);
lean_inc(v_previewSpan_x3f_3620_);
v___y_3597_ = v_newText_3625_;
v___y_3598_ = v_a_3623_;
v___y_3599_ = v___x_3616_;
v___y_3600_ = v_val_3618_;
v___y_3601_ = v_previewSpan_x3f_3620_;
v___y_3602_ = v_toTryThisSuggestion_3619_;
v___y_3603_ = v_range_3624_;
v___y_3604_ = v_diffGranularity_3621_;
v___y_3605_ = v_val_3627_;
goto v___jp_3596_;
}
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
lean_dec(v_val_3618_);
lean_dec_ref(v_b_3321_);
lean_dec(v_ref_3317_);
lean_dec(v_codeActionPrefix_x3f_3316_);
v_a_3628_ = lean_ctor_get(v___x_3622_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3622_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___x_3622_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3622_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
if (v_isShared_3631_ == 0)
{
v___x_3633_ = v___x_3630_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3628_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
else
{
lean_dec(v___x_3617_);
v_a_3326_ = v_b_3321_;
goto v___jp_3325_;
}
}
}
v___jp_3325_:
{
size_t v___x_3327_; size_t v___x_3328_; 
v___x_3327_ = ((size_t)1ULL);
v___x_3328_ = lean_usize_add(v_i_3320_, v___x_3327_);
v_i_3320_ = v___x_3328_;
v_b_3321_ = v_a_3326_;
goto _start;
}
v___jp_3330_:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3332_ = l_Lean_MessageData_nestD(v___y_3331_);
v___x_3333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3333_, 0, v_b_3321_);
lean_ctor_set(v___x_3333_, 1, v___x_3332_);
v_a_3326_ = v___x_3333_;
goto v___jp_3325_;
}
v___jp_3334_:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3338_, 0, v___y_3336_);
lean_ctor_set(v___x_3338_, 1, v___y_3337_);
v___x_3339_ = l_Lean_stringToMessageData(v___y_3335_);
v___x_3340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3338_);
lean_ctor_set(v___x_3340_, 1, v___x_3339_);
v___y_3331_ = v___x_3340_;
goto v___jp_3330_;
}
v___jp_3341_:
{
lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3343_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3344_ = lean_unsigned_to_nat(2u);
v___x_3345_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3);
v___x_3346_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3345_);
lean_ctor_set(v___x_3346_, 1, v___y_3342_);
v___x_3347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3344_);
lean_ctor_set(v___x_3347_, 1, v___x_3346_);
v___x_3348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3343_);
lean_ctor_set(v___x_3348_, 1, v___x_3347_);
v___y_3331_ = v___x_3348_;
goto v___jp_3330_;
}
v___jp_3349_:
{
lean_object* v___x_3354_; uint64_t v_javascriptHash_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; uint8_t v___x_3367_; 
v___x_3354_ = l_Lean_Meta_Hint_tryThisDiffWidget;
v_javascriptHash_3355_ = lean_ctor_get_uint64(v___x_3354_, sizeof(void*)*1);
v___x_3356_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8));
v___x_3357_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3357_, 0, v___x_3356_);
lean_ctor_set(v___x_3357_, 1, v___y_3352_);
lean_ctor_set_uint64(v___x_3357_, sizeof(void*)*2, v_javascriptHash_3355_);
v___x_3358_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3358_, 0, v___y_3353_);
v___x_3359_ = l_Lean_MessageData_ofFormat(v___x_3358_);
v___x_3360_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3360_, 0, v___x_3357_);
lean_ctor_set(v___x_3360_, 1, v___x_3359_);
v___x_3361_ = l_Lean_stringToMessageData(v___y_3350_);
v___x_3362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3361_);
lean_ctor_set(v___x_3362_, 1, v___x_3360_);
v___x_3363_ = l_Lean_stringToMessageData(v___y_3351_);
v___x_3364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3362_);
lean_ctor_set(v___x_3364_, 1, v___x_3363_);
v___x_3365_ = lean_array_get_size(v_suggestions_3314_);
v___x_3366_ = lean_unsigned_to_nat(1u);
v___x_3367_ = lean_nat_dec_eq(v___x_3365_, v___x_3366_);
if (v___x_3367_ == 0)
{
v___y_3342_ = v___x_3364_;
goto v___jp_3341_;
}
else
{
if (v_forceList_3315_ == 0)
{
if (v___x_3367_ == 0)
{
v___y_3342_ = v___x_3364_;
goto v___jp_3341_;
}
else
{
lean_object* v___x_3368_; lean_object* v___x_3369_; 
v___x_3368_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3369_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
lean_ctor_set(v___x_3369_, 1, v___x_3364_);
v___y_3331_ = v___x_3369_;
goto v___jp_3330_;
}
}
else
{
v___y_3342_ = v___x_3364_;
goto v___jp_3341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___boxed(lean_object* v_suggestions_3637_, lean_object* v_forceList_3638_, lean_object* v_codeActionPrefix_x3f_3639_, lean_object* v_ref_3640_, lean_object* v_as_3641_, lean_object* v_sz_3642_, lean_object* v_i_3643_, lean_object* v_b_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
uint8_t v_forceList_boxed_3648_; size_t v_sz_boxed_3649_; size_t v_i_boxed_3650_; lean_object* v_res_3651_; 
v_forceList_boxed_3648_ = lean_unbox(v_forceList_3638_);
v_sz_boxed_3649_ = lean_unbox_usize(v_sz_3642_);
lean_dec(v_sz_3642_);
v_i_boxed_3650_ = lean_unbox_usize(v_i_3643_);
lean_dec(v_i_3643_);
v_res_3651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3637_, v_forceList_boxed_3648_, v_codeActionPrefix_x3f_3639_, v_ref_3640_, v_as_3641_, v_sz_boxed_3649_, v_i_boxed_3650_, v_b_3644_, v___y_3645_, v___y_3646_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec_ref(v_as_3641_);
lean_dec_ref(v_suggestions_3637_);
return v_res_3651_;
}
}
static lean_object* _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0(void){
_start:
{
lean_object* v___x_3652_; lean_object* v_msg_3653_; 
v___x_3652_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v_msg_3653_ = l_Lean_stringToMessageData(v___x_3652_);
return v_msg_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage(lean_object* v_suggestions_3654_, lean_object* v_ref_3655_, lean_object* v_codeActionPrefix_x3f_3656_, uint8_t v_forceList_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_){
_start:
{
lean_object* v_msg_3661_; size_t v_sz_3662_; size_t v___x_3663_; lean_object* v___x_3664_; 
v_msg_3661_ = lean_obj_once(&l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0, &l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0_once, _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0);
v_sz_3662_ = lean_array_size(v_suggestions_3654_);
v___x_3663_ = ((size_t)0ULL);
v___x_3664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3654_, v_forceList_3657_, v_codeActionPrefix_x3f_3656_, v_ref_3655_, v_suggestions_3654_, v_sz_3662_, v___x_3663_, v_msg_3661_, v_a_3658_, v_a_3659_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage___boxed(lean_object* v_suggestions_3665_, lean_object* v_ref_3666_, lean_object* v_codeActionPrefix_x3f_3667_, lean_object* v_forceList_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_){
_start:
{
uint8_t v_forceList_boxed_3672_; lean_object* v_res_3673_; 
v_forceList_boxed_3672_ = lean_unbox(v_forceList_3668_);
v_res_3673_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3665_, v_ref_3666_, v_codeActionPrefix_x3f_3667_, v_forceList_boxed_3672_, v_a_3669_, v_a_3670_);
lean_dec(v_a_3670_);
lean_dec_ref(v_a_3669_);
lean_dec_ref(v_suggestions_3665_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(lean_object* v_t_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_){
_start:
{
lean_object* v___x_3678_; 
v___x_3678_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3674_, v___y_3676_);
return v___x_3678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___boxed(lean_object* v_t_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_){
_start:
{
lean_object* v_res_3683_; 
v_res_3683_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(v_t_3679_, v___y_3680_, v___y_3681_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
return v_res_3683_;
}
}
static lean_object* _init_l_Lean_MessageData_hint___closed__3(void){
_start:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3688_ = ((lean_object*)(l_Lean_MessageData_hint___closed__2));
v___x_3689_ = l_Lean_stringToMessageData(v___x_3688_);
return v___x_3689_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint(lean_object* v_hint_3690_, lean_object* v_suggestions_3691_, lean_object* v_ref_x3f_3692_, lean_object* v_codeActionPrefix_x3f_3693_, uint8_t v_forceList_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_){
_start:
{
lean_object* v___y_3699_; 
if (lean_obj_tag(v_ref_x3f_3692_) == 0)
{
lean_object* v_ref_3714_; 
v_ref_3714_ = lean_ctor_get(v_a_3695_, 5);
lean_inc(v_ref_3714_);
v___y_3699_ = v_ref_3714_;
goto v___jp_3698_;
}
else
{
lean_object* v_val_3715_; 
v_val_3715_ = lean_ctor_get(v_ref_x3f_3692_, 0);
lean_inc(v_val_3715_);
lean_dec_ref_known(v_ref_x3f_3692_, 1);
v___y_3699_ = v_val_3715_;
goto v___jp_3698_;
}
v___jp_3698_:
{
lean_object* v___x_3700_; 
v___x_3700_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3691_, v___y_3699_, v_codeActionPrefix_x3f_3693_, v_forceList_3694_, v_a_3695_, v_a_3696_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3713_; 
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3703_ = v___x_3700_;
v_isShared_3704_ = v_isSharedCheck_3713_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3700_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3713_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3711_; 
v___x_3705_ = ((lean_object*)(l_Lean_MessageData_hint___closed__1));
v___x_3706_ = lean_obj_once(&l_Lean_MessageData_hint___closed__3, &l_Lean_MessageData_hint___closed__3_once, _init_l_Lean_MessageData_hint___closed__3);
v___x_3707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3706_);
lean_ctor_set(v___x_3707_, 1, v_hint_3690_);
v___x_3708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3707_);
lean_ctor_set(v___x_3708_, 1, v_a_3701_);
v___x_3709_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3705_);
lean_ctor_set(v___x_3709_, 1, v___x_3708_);
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 0, v___x_3709_);
v___x_3711_ = v___x_3703_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v___x_3709_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
else
{
lean_dec_ref(v_hint_3690_);
return v___x_3700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint___boxed(lean_object* v_hint_3716_, lean_object* v_suggestions_3717_, lean_object* v_ref_x3f_3718_, lean_object* v_codeActionPrefix_x3f_3719_, lean_object* v_forceList_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_){
_start:
{
uint8_t v_forceList_boxed_3724_; lean_object* v_res_3725_; 
v_forceList_boxed_3724_ = lean_unbox(v_forceList_3720_);
v_res_3725_ = l_Lean_MessageData_hint(v_hint_3716_, v_suggestions_3717_, v_ref_x3f_3718_, v_codeActionPrefix_x3f_3719_, v_forceList_boxed_3724_, v_a_3721_, v_a_3722_);
lean_dec(v_a_3722_);
lean_dec_ref(v_a_3721_);
lean_dec_ref(v_suggestions_3717_);
return v_res_3725_;
}
}
lean_object* runtime_initialize_Lean_Meta_TryThis(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Diff(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Hint(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
