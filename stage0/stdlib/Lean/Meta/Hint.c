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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint32_to_uint64(uint32_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
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
lean_object* lean_array_push(lean_object*, lean_object*);
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
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_83_);
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
lean_dec_ref(v___x_93_);
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
lean_dec_ref(v___x_103_);
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
lean_dec_ref(v_suggestion_325_);
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
lean_dec_ref(v_messageData_x3f_324_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(lean_object* v___x_488_, lean_object* v_edited_489_, lean_object* v_b_490_){
_start:
{
lean_object* v_fst_491_; lean_object* v_snd_492_; lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_511_; 
v_fst_491_ = lean_ctor_get(v_b_490_, 0);
v_snd_492_ = lean_ctor_get(v_b_490_, 1);
v_isSharedCheck_511_ = !lean_is_exclusive(v_b_490_);
if (v_isSharedCheck_511_ == 0)
{
v___x_494_ = v_b_490_;
v_isShared_495_ = v_isSharedCheck_511_;
goto v_resetjp_493_;
}
else
{
lean_inc(v_snd_492_);
lean_inc(v_fst_491_);
lean_dec(v_b_490_);
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
v___x_500_ = 0;
v___x_501_ = lean_array_fget_borrowed(v_edited_489_, v_snd_492_);
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
v_b_490_ = v___x_508_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___boxed(lean_object* v___x_512_, lean_object* v_edited_513_, lean_object* v_b_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(v___x_512_, v_edited_513_, v_b_514_);
lean_dec_ref(v_edited_513_);
lean_dec(v___x_512_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(lean_object* v___x_516_, lean_object* v_original_517_, lean_object* v_b_518_){
_start:
{
lean_object* v_fst_519_; lean_object* v_snd_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_539_; 
v_fst_519_ = lean_ctor_get(v_b_518_, 0);
v_snd_520_ = lean_ctor_get(v_b_518_, 1);
v_isSharedCheck_539_ = !lean_is_exclusive(v_b_518_);
if (v_isSharedCheck_539_ == 0)
{
v___x_522_ = v_b_518_;
v_isShared_523_ = v_isSharedCheck_539_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_snd_520_);
lean_inc(v_fst_519_);
lean_dec(v_b_518_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_539_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
uint8_t v___x_524_; 
v___x_524_ = lean_nat_dec_lt(v_snd_520_, v___x_516_);
if (v___x_524_ == 0)
{
lean_object* v___x_526_; 
if (v_isShared_523_ == 0)
{
v___x_526_ = v___x_522_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_fst_519_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_snd_520_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
else
{
uint8_t v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_528_ = 1;
v___x_529_ = lean_array_fget_borrowed(v_original_517_, v_snd_520_);
v___x_530_ = lean_box(v___x_528_);
lean_inc(v___x_529_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 1, v___x_529_);
lean_ctor_set(v___x_522_, 0, v___x_530_);
v___x_532_ = v___x_522_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_530_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v___x_529_);
v___x_532_ = v_reuseFailAlloc_538_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_533_ = lean_array_push(v_fst_519_, v___x_532_);
v___x_534_ = lean_unsigned_to_nat(1u);
v___x_535_ = lean_nat_add(v_snd_520_, v___x_534_);
lean_dec(v_snd_520_);
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_533_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v_b_518_ = v___x_536_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___boxed(lean_object* v___x_540_, lean_object* v_original_541_, lean_object* v_b_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(v___x_540_, v_original_541_, v_b_542_);
lean_dec_ref(v_original_541_);
lean_dec(v___x_540_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg(uint32_t v_a_544_, lean_object* v_x_545_){
_start:
{
if (lean_obj_tag(v_x_545_) == 0)
{
lean_object* v___x_546_; 
v___x_546_ = lean_box(0);
return v___x_546_;
}
else
{
lean_object* v_key_547_; lean_object* v_value_548_; lean_object* v_tail_549_; uint32_t v___x_550_; uint8_t v___x_551_; 
v_key_547_ = lean_ctor_get(v_x_545_, 0);
v_value_548_ = lean_ctor_get(v_x_545_, 1);
v_tail_549_ = lean_ctor_get(v_x_545_, 2);
v___x_550_ = lean_unbox_uint32(v_key_547_);
v___x_551_ = lean_uint32_dec_eq(v___x_550_, v_a_544_);
if (v___x_551_ == 0)
{
v_x_545_ = v_tail_549_;
goto _start;
}
else
{
lean_object* v___x_553_; 
lean_inc(v_value_548_);
v___x_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_553_, 0, v_value_548_);
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg___boxed(lean_object* v_a_554_, lean_object* v_x_555_){
_start:
{
uint32_t v_a_boxed_556_; lean_object* v_res_557_; 
v_a_boxed_556_ = lean_unbox_uint32(v_a_554_);
lean_dec(v_a_554_);
v_res_557_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg(v_a_boxed_556_, v_x_555_);
lean_dec(v_x_555_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(lean_object* v_m_558_, uint32_t v_a_559_){
_start:
{
lean_object* v_buckets_560_; lean_object* v___x_561_; uint64_t v___x_562_; uint64_t v___x_563_; uint64_t v___x_564_; uint64_t v_fold_565_; uint64_t v___x_566_; uint64_t v___x_567_; uint64_t v___x_568_; size_t v___x_569_; size_t v___x_570_; size_t v___x_571_; size_t v___x_572_; size_t v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_buckets_560_ = lean_ctor_get(v_m_558_, 1);
v___x_561_ = lean_array_get_size(v_buckets_560_);
v___x_562_ = lean_uint32_to_uint64(v_a_559_);
v___x_563_ = 32ULL;
v___x_564_ = lean_uint64_shift_right(v___x_562_, v___x_563_);
v_fold_565_ = lean_uint64_xor(v___x_562_, v___x_564_);
v___x_566_ = 16ULL;
v___x_567_ = lean_uint64_shift_right(v_fold_565_, v___x_566_);
v___x_568_ = lean_uint64_xor(v_fold_565_, v___x_567_);
v___x_569_ = lean_uint64_to_usize(v___x_568_);
v___x_570_ = lean_usize_of_nat(v___x_561_);
v___x_571_ = ((size_t)1ULL);
v___x_572_ = lean_usize_sub(v___x_570_, v___x_571_);
v___x_573_ = lean_usize_land(v___x_569_, v___x_572_);
v___x_574_ = lean_array_uget_borrowed(v_buckets_560_, v___x_573_);
v___x_575_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg(v_a_559_, v___x_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg___boxed(lean_object* v_m_576_, lean_object* v_a_577_){
_start:
{
uint32_t v_a_boxed_578_; lean_object* v_res_579_; 
v_a_boxed_578_ = lean_unbox_uint32(v_a_577_);
lean_dec(v_a_577_);
v_res_579_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(v_m_576_, v_a_boxed_578_);
lean_dec_ref(v_m_576_);
return v_res_579_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg(uint32_t v_a_580_, lean_object* v_x_581_){
_start:
{
if (lean_obj_tag(v_x_581_) == 0)
{
uint8_t v___x_582_; 
v___x_582_ = 0;
return v___x_582_;
}
else
{
lean_object* v_key_583_; lean_object* v_tail_584_; uint32_t v___x_585_; uint8_t v___x_586_; 
v_key_583_ = lean_ctor_get(v_x_581_, 0);
v_tail_584_ = lean_ctor_get(v_x_581_, 2);
v___x_585_ = lean_unbox_uint32(v_key_583_);
v___x_586_ = lean_uint32_dec_eq(v___x_585_, v_a_580_);
if (v___x_586_ == 0)
{
v_x_581_ = v_tail_584_;
goto _start;
}
else
{
return v___x_586_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg___boxed(lean_object* v_a_588_, lean_object* v_x_589_){
_start:
{
uint32_t v_a_boxed_590_; uint8_t v_res_591_; lean_object* v_r_592_; 
v_a_boxed_590_ = lean_unbox_uint32(v_a_588_);
lean_dec(v_a_588_);
v_res_591_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg(v_a_boxed_590_, v_x_589_);
lean_dec(v_x_589_);
v_r_592_ = lean_box(v_res_591_);
return v_r_592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(uint32_t v_a_593_, lean_object* v_b_594_, lean_object* v_x_595_){
_start:
{
if (lean_obj_tag(v_x_595_) == 0)
{
lean_dec(v_b_594_);
return v_x_595_;
}
else
{
lean_object* v_key_596_; lean_object* v_value_597_; lean_object* v_tail_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_612_; 
v_key_596_ = lean_ctor_get(v_x_595_, 0);
v_value_597_ = lean_ctor_get(v_x_595_, 1);
v_tail_598_ = lean_ctor_get(v_x_595_, 2);
v_isSharedCheck_612_ = !lean_is_exclusive(v_x_595_);
if (v_isSharedCheck_612_ == 0)
{
v___x_600_ = v_x_595_;
v_isShared_601_ = v_isSharedCheck_612_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_tail_598_);
lean_inc(v_value_597_);
lean_inc(v_key_596_);
lean_dec(v_x_595_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_612_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
uint32_t v___x_602_; uint8_t v___x_603_; 
v___x_602_ = lean_unbox_uint32(v_key_596_);
v___x_603_ = lean_uint32_dec_eq(v___x_602_, v_a_593_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_604_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(v_a_593_, v_b_594_, v_tail_598_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 2, v___x_604_);
v___x_606_ = v___x_600_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_key_596_);
lean_ctor_set(v_reuseFailAlloc_607_, 1, v_value_597_);
lean_ctor_set(v_reuseFailAlloc_607_, 2, v___x_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
else
{
lean_object* v___x_608_; lean_object* v___x_610_; 
lean_dec(v_value_597_);
lean_dec(v_key_596_);
v___x_608_ = lean_box_uint32(v_a_593_);
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 1, v_b_594_);
lean_ctor_set(v___x_600_, 0, v___x_608_);
v___x_610_ = v___x_600_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_608_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_b_594_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_tail_598_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg___boxed(lean_object* v_a_613_, lean_object* v_b_614_, lean_object* v_x_615_){
_start:
{
uint32_t v_a_boxed_616_; lean_object* v_res_617_; 
v_a_boxed_616_ = lean_unbox_uint32(v_a_613_);
lean_dec(v_a_613_);
v_res_617_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(v_a_boxed_616_, v_b_614_, v_x_615_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29___redArg(lean_object* v_x_618_, lean_object* v_x_619_){
_start:
{
if (lean_obj_tag(v_x_619_) == 0)
{
return v_x_618_;
}
else
{
lean_object* v_key_620_; lean_object* v_value_621_; lean_object* v_tail_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_646_; 
v_key_620_ = lean_ctor_get(v_x_619_, 0);
v_value_621_ = lean_ctor_get(v_x_619_, 1);
v_tail_622_ = lean_ctor_get(v_x_619_, 2);
v_isSharedCheck_646_ = !lean_is_exclusive(v_x_619_);
if (v_isSharedCheck_646_ == 0)
{
v___x_624_ = v_x_619_;
v_isShared_625_ = v_isSharedCheck_646_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_tail_622_);
lean_inc(v_value_621_);
lean_inc(v_key_620_);
lean_dec(v_x_619_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_646_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; uint32_t v___x_627_; uint64_t v___x_628_; uint64_t v___x_629_; uint64_t v___x_630_; uint64_t v_fold_631_; uint64_t v___x_632_; uint64_t v___x_633_; uint64_t v___x_634_; size_t v___x_635_; size_t v___x_636_; size_t v___x_637_; size_t v___x_638_; size_t v___x_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
v___x_626_ = lean_array_get_size(v_x_618_);
v___x_627_ = lean_unbox_uint32(v_key_620_);
v___x_628_ = lean_uint32_to_uint64(v___x_627_);
v___x_629_ = 32ULL;
v___x_630_ = lean_uint64_shift_right(v___x_628_, v___x_629_);
v_fold_631_ = lean_uint64_xor(v___x_628_, v___x_630_);
v___x_632_ = 16ULL;
v___x_633_ = lean_uint64_shift_right(v_fold_631_, v___x_632_);
v___x_634_ = lean_uint64_xor(v_fold_631_, v___x_633_);
v___x_635_ = lean_uint64_to_usize(v___x_634_);
v___x_636_ = lean_usize_of_nat(v___x_626_);
v___x_637_ = ((size_t)1ULL);
v___x_638_ = lean_usize_sub(v___x_636_, v___x_637_);
v___x_639_ = lean_usize_land(v___x_635_, v___x_638_);
v___x_640_ = lean_array_uget_borrowed(v_x_618_, v___x_639_);
lean_inc(v___x_640_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 2, v___x_640_);
v___x_642_ = v___x_624_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_key_620_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_value_621_);
lean_ctor_set(v_reuseFailAlloc_645_, 2, v___x_640_);
v___x_642_ = v_reuseFailAlloc_645_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_643_; 
v___x_643_ = lean_array_uset(v_x_618_, v___x_639_, v___x_642_);
v_x_618_ = v___x_643_;
v_x_619_ = v_tail_622_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28___redArg(lean_object* v_i_647_, lean_object* v_source_648_, lean_object* v_target_649_){
_start:
{
lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_650_ = lean_array_get_size(v_source_648_);
v___x_651_ = lean_nat_dec_lt(v_i_647_, v___x_650_);
if (v___x_651_ == 0)
{
lean_dec_ref(v_source_648_);
lean_dec(v_i_647_);
return v_target_649_;
}
else
{
lean_object* v_es_652_; lean_object* v___x_653_; lean_object* v_source_654_; lean_object* v_target_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v_es_652_ = lean_array_fget(v_source_648_, v_i_647_);
v___x_653_ = lean_box(0);
v_source_654_ = lean_array_fset(v_source_648_, v_i_647_, v___x_653_);
v_target_655_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29___redArg(v_target_649_, v_es_652_);
v___x_656_ = lean_unsigned_to_nat(1u);
v___x_657_ = lean_nat_add(v_i_647_, v___x_656_);
lean_dec(v_i_647_);
v_i_647_ = v___x_657_;
v_source_648_ = v_source_654_;
v_target_649_ = v_target_655_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23___redArg(lean_object* v_data_659_){
_start:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v_nbuckets_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_660_ = lean_array_get_size(v_data_659_);
v___x_661_ = lean_unsigned_to_nat(2u);
v_nbuckets_662_ = lean_nat_mul(v___x_660_, v___x_661_);
v___x_663_ = lean_unsigned_to_nat(0u);
v___x_664_ = lean_box(0);
v___x_665_ = lean_mk_array(v_nbuckets_662_, v___x_664_);
v___x_666_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28___redArg(v___x_663_, v_data_659_, v___x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(lean_object* v_m_667_, uint32_t v_a_668_, lean_object* v_b_669_){
_start:
{
lean_object* v_size_670_; lean_object* v_buckets_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_715_; 
v_size_670_ = lean_ctor_get(v_m_667_, 0);
v_buckets_671_ = lean_ctor_get(v_m_667_, 1);
v_isSharedCheck_715_ = !lean_is_exclusive(v_m_667_);
if (v_isSharedCheck_715_ == 0)
{
v___x_673_ = v_m_667_;
v_isShared_674_ = v_isSharedCheck_715_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_buckets_671_);
lean_inc(v_size_670_);
lean_dec(v_m_667_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_715_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; uint64_t v___x_676_; uint64_t v___x_677_; uint64_t v___x_678_; uint64_t v_fold_679_; uint64_t v___x_680_; uint64_t v___x_681_; uint64_t v___x_682_; size_t v___x_683_; size_t v___x_684_; size_t v___x_685_; size_t v___x_686_; size_t v___x_687_; lean_object* v_bkt_688_; uint8_t v___x_689_; 
v___x_675_ = lean_array_get_size(v_buckets_671_);
v___x_676_ = lean_uint32_to_uint64(v_a_668_);
v___x_677_ = 32ULL;
v___x_678_ = lean_uint64_shift_right(v___x_676_, v___x_677_);
v_fold_679_ = lean_uint64_xor(v___x_676_, v___x_678_);
v___x_680_ = 16ULL;
v___x_681_ = lean_uint64_shift_right(v_fold_679_, v___x_680_);
v___x_682_ = lean_uint64_xor(v_fold_679_, v___x_681_);
v___x_683_ = lean_uint64_to_usize(v___x_682_);
v___x_684_ = lean_usize_of_nat(v___x_675_);
v___x_685_ = ((size_t)1ULL);
v___x_686_ = lean_usize_sub(v___x_684_, v___x_685_);
v___x_687_ = lean_usize_land(v___x_683_, v___x_686_);
v_bkt_688_ = lean_array_uget_borrowed(v_buckets_671_, v___x_687_);
v___x_689_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg(v_a_668_, v_bkt_688_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; lean_object* v_size_x27_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v_buckets_x27_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_690_ = lean_unsigned_to_nat(1u);
v_size_x27_691_ = lean_nat_add(v_size_670_, v___x_690_);
lean_dec(v_size_670_);
v___x_692_ = lean_box_uint32(v_a_668_);
lean_inc(v_bkt_688_);
v___x_693_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
lean_ctor_set(v___x_693_, 1, v_b_669_);
lean_ctor_set(v___x_693_, 2, v_bkt_688_);
v_buckets_x27_694_ = lean_array_uset(v_buckets_671_, v___x_687_, v___x_693_);
v___x_695_ = lean_unsigned_to_nat(4u);
v___x_696_ = lean_nat_mul(v_size_x27_691_, v___x_695_);
v___x_697_ = lean_unsigned_to_nat(3u);
v___x_698_ = lean_nat_div(v___x_696_, v___x_697_);
lean_dec(v___x_696_);
v___x_699_ = lean_array_get_size(v_buckets_x27_694_);
v___x_700_ = lean_nat_dec_le(v___x_698_, v___x_699_);
lean_dec(v___x_698_);
if (v___x_700_ == 0)
{
lean_object* v_val_701_; lean_object* v___x_703_; 
v_val_701_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23___redArg(v_buckets_x27_694_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 1, v_val_701_);
lean_ctor_set(v___x_673_, 0, v_size_x27_691_);
v___x_703_ = v___x_673_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_size_x27_691_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_val_701_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
else
{
lean_object* v___x_706_; 
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 1, v_buckets_x27_694_);
lean_ctor_set(v___x_673_, 0, v_size_x27_691_);
v___x_706_ = v___x_673_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_size_x27_691_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v_buckets_x27_694_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
else
{
lean_object* v___x_708_; lean_object* v_buckets_x27_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_713_; 
lean_inc(v_bkt_688_);
v___x_708_ = lean_box(0);
v_buckets_x27_709_ = lean_array_uset(v_buckets_671_, v___x_687_, v___x_708_);
v___x_710_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(v_a_668_, v_b_669_, v_bkt_688_);
v___x_711_ = lean_array_uset(v_buckets_x27_709_, v___x_687_, v___x_710_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 1, v___x_711_);
v___x_713_ = v___x_673_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_size_670_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg___boxed(lean_object* v_m_716_, lean_object* v_a_717_, lean_object* v_b_718_){
_start:
{
uint32_t v_a_boxed_719_; lean_object* v_res_720_; 
v_a_boxed_719_ = lean_unbox_uint32(v_a_717_);
lean_dec(v_a_717_);
v_res_720_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_m_716_, v_a_boxed_719_, v_b_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(lean_object* v_histogram_721_, lean_object* v_index_722_, uint32_t v_val_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(v_histogram_721_, v_val_723_);
if (lean_obj_tag(v___x_724_) == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_725_ = lean_unsigned_to_nat(0u);
v___x_726_ = lean_box(0);
v___x_727_ = lean_unsigned_to_nat(1u);
v___x_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_728_, 0, v_index_722_);
v___x_729_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_729_, 0, v___x_725_);
lean_ctor_set(v___x_729_, 1, v___x_726_);
lean_ctor_set(v___x_729_, 2, v___x_727_);
lean_ctor_set(v___x_729_, 3, v___x_728_);
v___x_730_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_histogram_721_, v_val_723_, v___x_729_);
return v___x_730_;
}
else
{
lean_object* v_val_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_752_; 
v_val_731_ = lean_ctor_get(v___x_724_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_724_);
if (v_isSharedCheck_752_ == 0)
{
v___x_733_ = v___x_724_;
v_isShared_734_ = v_isSharedCheck_752_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_val_731_);
lean_dec(v___x_724_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_752_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v_leftCount_735_; lean_object* v_leftIndex_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_749_; 
v_leftCount_735_ = lean_ctor_get(v_val_731_, 0);
v_leftIndex_736_ = lean_ctor_get(v_val_731_, 1);
v_isSharedCheck_749_ = !lean_is_exclusive(v_val_731_);
if (v_isSharedCheck_749_ == 0)
{
lean_object* v_unused_750_; lean_object* v_unused_751_; 
v_unused_750_ = lean_ctor_get(v_val_731_, 3);
lean_dec(v_unused_750_);
v_unused_751_ = lean_ctor_get(v_val_731_, 2);
lean_dec(v_unused_751_);
v___x_738_ = v_val_731_;
v_isShared_739_ = v_isSharedCheck_749_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_leftIndex_736_);
lean_inc(v_leftCount_735_);
lean_dec(v_val_731_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_749_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_743_; 
v___x_740_ = lean_unsigned_to_nat(1u);
v___x_741_ = lean_nat_add(v_leftCount_735_, v___x_740_);
if (v_isShared_734_ == 0)
{
lean_ctor_set(v___x_733_, 0, v_index_722_);
v___x_743_ = v___x_733_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_index_722_);
v___x_743_ = v_reuseFailAlloc_748_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_745_; 
if (v_isShared_739_ == 0)
{
lean_ctor_set(v___x_738_, 3, v___x_743_);
lean_ctor_set(v___x_738_, 2, v___x_741_);
v___x_745_ = v___x_738_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_leftCount_735_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v_leftIndex_736_);
lean_ctor_set(v_reuseFailAlloc_747_, 2, v___x_741_);
lean_ctor_set(v_reuseFailAlloc_747_, 3, v___x_743_);
v___x_745_ = v_reuseFailAlloc_747_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
lean_object* v___x_746_; 
v___x_746_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_histogram_721_, v_val_723_, v___x_745_);
return v___x_746_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg___boxed(lean_object* v_histogram_753_, lean_object* v_index_754_, lean_object* v_val_755_){
_start:
{
uint32_t v_val_boxed_756_; lean_object* v_res_757_; 
v_val_boxed_756_ = lean_unbox_uint32(v_val_755_);
lean_dec(v_val_755_);
v_res_757_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(v_histogram_753_, v_index_754_, v_val_boxed_756_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(lean_object* v_upperBound_758_, lean_object* v___x_759_, lean_object* v_fst_760_, lean_object* v___x_761_, lean_object* v_a_762_, lean_object* v_b_763_){
_start:
{
uint8_t v___x_764_; 
v___x_764_ = lean_nat_dec_lt(v_a_762_, v_upperBound_758_);
if (v___x_764_ == 0)
{
lean_dec(v_a_762_);
return v_b_763_;
}
else
{
lean_object* v___x_765_; uint32_t v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_765_ = l_Subarray_get___redArg(v_fst_760_, v_a_762_);
v___x_766_ = lean_unbox_uint32(v___x_765_);
lean_dec(v___x_765_);
lean_inc(v_a_762_);
v___x_767_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(v_b_763_, v_a_762_, v___x_766_);
v___x_768_ = lean_unsigned_to_nat(1u);
v___x_769_ = lean_nat_add(v_a_762_, v___x_768_);
lean_dec(v_a_762_);
v_a_762_ = v___x_769_;
v_b_763_ = v___x_767_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg___boxed(lean_object* v_upperBound_771_, lean_object* v___x_772_, lean_object* v_fst_773_, lean_object* v___x_774_, lean_object* v_a_775_, lean_object* v_b_776_){
_start:
{
lean_object* v_res_777_; 
v_res_777_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(v_upperBound_771_, v___x_772_, v_fst_773_, v___x_774_, v_a_775_, v_b_776_);
lean_dec(v___x_774_);
lean_dec_ref(v_fst_773_);
lean_dec(v___x_772_);
lean_dec(v_upperBound_771_);
return v_res_777_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg(lean_object* v_as_x27_778_, lean_object* v_b_779_){
_start:
{
if (lean_obj_tag(v_as_x27_778_) == 0)
{
return v_b_779_;
}
else
{
lean_object* v_head_780_; lean_object* v_snd_781_; lean_object* v_leftIndex_782_; 
v_head_780_ = lean_ctor_get(v_as_x27_778_, 0);
v_snd_781_ = lean_ctor_get(v_head_780_, 1);
v_leftIndex_782_ = lean_ctor_get(v_snd_781_, 1);
if (lean_obj_tag(v_leftIndex_782_) == 1)
{
lean_object* v_rightIndex_783_; 
v_rightIndex_783_ = lean_ctor_get(v_snd_781_, 3);
if (lean_obj_tag(v_rightIndex_783_) == 1)
{
if (lean_obj_tag(v_b_779_) == 0)
{
lean_object* v_tail_784_; lean_object* v_fst_785_; lean_object* v_leftCount_786_; lean_object* v_rightCount_787_; lean_object* v_val_788_; lean_object* v_val_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v_tail_784_ = lean_ctor_get(v_as_x27_778_, 1);
v_fst_785_ = lean_ctor_get(v_head_780_, 0);
v_leftCount_786_ = lean_ctor_get(v_snd_781_, 0);
v_rightCount_787_ = lean_ctor_get(v_snd_781_, 2);
v_val_788_ = lean_ctor_get(v_leftIndex_782_, 0);
v_val_789_ = lean_ctor_get(v_rightIndex_783_, 0);
v___x_790_ = lean_nat_add(v_leftCount_786_, v_rightCount_787_);
lean_inc(v_val_789_);
lean_inc(v_val_788_);
v___x_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_791_, 0, v_val_788_);
lean_ctor_set(v___x_791_, 1, v_val_789_);
lean_inc(v_fst_785_);
v___x_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_792_, 0, v_fst_785_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_790_);
lean_ctor_set(v___x_793_, 1, v___x_792_);
v___x_794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
v_as_x27_778_ = v_tail_784_;
v_b_779_ = v___x_794_;
goto _start;
}
else
{
lean_object* v_val_796_; lean_object* v_tail_797_; lean_object* v_fst_798_; lean_object* v_leftCount_799_; lean_object* v_rightCount_800_; lean_object* v_val_801_; lean_object* v_val_802_; lean_object* v_fst_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_824_; 
v_val_796_ = lean_ctor_get(v_b_779_, 0);
lean_inc(v_val_796_);
v_tail_797_ = lean_ctor_get(v_as_x27_778_, 1);
v_fst_798_ = lean_ctor_get(v_head_780_, 0);
v_leftCount_799_ = lean_ctor_get(v_snd_781_, 0);
v_rightCount_800_ = lean_ctor_get(v_snd_781_, 2);
v_val_801_ = lean_ctor_get(v_leftIndex_782_, 0);
v_val_802_ = lean_ctor_get(v_rightIndex_783_, 0);
v_fst_803_ = lean_ctor_get(v_val_796_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v_val_796_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; 
v_unused_825_ = lean_ctor_get(v_val_796_, 1);
lean_dec(v_unused_825_);
v___x_805_ = v_val_796_;
v_isShared_806_ = v_isSharedCheck_824_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_fst_803_);
lean_dec(v_val_796_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_824_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_807_ = lean_nat_add(v_leftCount_799_, v_rightCount_800_);
v___x_808_ = lean_nat_dec_lt(v___x_807_, v_fst_803_);
lean_dec(v_fst_803_);
if (v___x_808_ == 0)
{
lean_dec(v___x_807_);
lean_del_object(v___x_805_);
v_as_x27_778_ = v_tail_797_;
goto _start;
}
else
{
lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_822_; 
v_isSharedCheck_822_ = !lean_is_exclusive(v_b_779_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v_b_779_, 0);
lean_dec(v_unused_823_);
v___x_811_ = v_b_779_;
v_isShared_812_ = v_isSharedCheck_822_;
goto v_resetjp_810_;
}
else
{
lean_dec(v_b_779_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_822_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
lean_inc(v_val_802_);
lean_inc(v_val_801_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 1, v_val_802_);
lean_ctor_set(v___x_805_, 0, v_val_801_);
v___x_814_ = v___x_805_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_val_801_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_val_802_);
v___x_814_ = v_reuseFailAlloc_821_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_818_; 
lean_inc(v_fst_798_);
v___x_815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_815_, 0, v_fst_798_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_807_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
if (v_isShared_812_ == 0)
{
lean_ctor_set(v___x_811_, 0, v___x_816_);
v___x_818_ = v___x_811_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_816_);
v___x_818_ = v_reuseFailAlloc_820_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
v_as_x27_778_ = v_tail_797_;
v_b_779_ = v___x_818_;
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
lean_object* v_tail_826_; 
v_tail_826_ = lean_ctor_get(v_as_x27_778_, 1);
v_as_x27_778_ = v_tail_826_;
goto _start;
}
}
else
{
lean_object* v_tail_828_; 
v_tail_828_ = lean_ctor_get(v_as_x27_778_, 1);
v_as_x27_778_ = v_tail_828_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_as_x27_830_, lean_object* v_b_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg(v_as_x27_830_, v_b_831_);
lean_dec(v_as_x27_830_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3_spec__4(lean_object* v_left_833_, lean_object* v_right_834_, lean_object* v_pref_835_){
_start:
{
lean_object* v_start_836_; lean_object* v_stop_837_; lean_object* v_i_838_; lean_object* v___x_844_; uint8_t v___x_845_; 
v_start_836_ = lean_ctor_get(v_left_833_, 1);
v_stop_837_ = lean_ctor_get(v_left_833_, 2);
v_i_838_ = lean_array_get_size(v_pref_835_);
v___x_844_ = lean_nat_sub(v_stop_837_, v_start_836_);
v___x_845_ = lean_nat_dec_lt(v_i_838_, v___x_844_);
lean_dec(v___x_844_);
if (v___x_845_ == 0)
{
goto v___jp_839_;
}
else
{
lean_object* v_start_846_; lean_object* v_stop_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
v_start_846_ = lean_ctor_get(v_right_834_, 1);
v_stop_847_ = lean_ctor_get(v_right_834_, 2);
v___x_848_ = lean_nat_sub(v_stop_847_, v_start_846_);
v___x_849_ = lean_nat_dec_lt(v_i_838_, v___x_848_);
lean_dec(v___x_848_);
if (v___x_849_ == 0)
{
goto v___jp_839_;
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; uint32_t v___x_852_; uint32_t v___x_853_; uint8_t v___x_854_; 
v___x_850_ = l_Subarray_get___redArg(v_left_833_, v_i_838_);
v___x_851_ = l_Subarray_get___redArg(v_right_834_, v_i_838_);
v___x_852_ = lean_unbox_uint32(v___x_850_);
v___x_853_ = lean_unbox_uint32(v___x_851_);
lean_dec(v___x_851_);
v___x_854_ = lean_uint32_dec_eq(v___x_852_, v___x_853_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec(v___x_850_);
v___x_855_ = l_Subarray_drop___redArg(v_left_833_, v_i_838_);
v___x_856_ = l_Subarray_drop___redArg(v_right_834_, v_i_838_);
v___x_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_855_);
lean_ctor_set(v___x_857_, 1, v___x_856_);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v_pref_835_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
return v___x_858_;
}
else
{
lean_object* v___x_859_; 
v___x_859_ = lean_array_push(v_pref_835_, v___x_850_);
v_pref_835_ = v___x_859_;
goto _start;
}
}
}
v___jp_839_:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_840_ = l_Subarray_drop___redArg(v_left_833_, v_i_838_);
v___x_841_ = l_Subarray_drop___redArg(v_right_834_, v_i_838_);
v___x_842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_840_);
lean_ctor_set(v___x_842_, 1, v___x_841_);
v___x_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_843_, 0, v_pref_835_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
return v___x_843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3(lean_object* v_left_861_, lean_object* v_right_862_){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_864_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3_spec__4(v_left_861_, v_right_862_, v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(lean_object* v_a_865_, lean_object* v_b_866_){
_start:
{
lean_object* v_array_867_; lean_object* v_start_868_; lean_object* v_stop_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_882_; 
v_array_867_ = lean_ctor_get(v_a_865_, 0);
v_start_868_ = lean_ctor_get(v_a_865_, 1);
v_stop_869_ = lean_ctor_get(v_a_865_, 2);
v_isSharedCheck_882_ = !lean_is_exclusive(v_a_865_);
if (v_isSharedCheck_882_ == 0)
{
v___x_871_ = v_a_865_;
v_isShared_872_ = v_isSharedCheck_882_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_stop_869_);
lean_inc(v_start_868_);
lean_inc(v_array_867_);
lean_dec(v_a_865_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_882_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
uint8_t v___x_873_; 
v___x_873_ = lean_nat_dec_lt(v_start_868_, v_stop_869_);
if (v___x_873_ == 0)
{
lean_del_object(v___x_871_);
lean_dec(v_stop_869_);
lean_dec(v_start_868_);
lean_dec_ref(v_array_867_);
return v_b_866_;
}
else
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_874_ = lean_unsigned_to_nat(1u);
v___x_875_ = lean_nat_add(v_start_868_, v___x_874_);
lean_inc_ref(v_array_867_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 1, v___x_875_);
v___x_877_ = v___x_871_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_array_867_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_881_, 2, v_stop_869_);
v___x_877_ = v_reuseFailAlloc_881_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = lean_array_fget(v_array_867_, v_start_868_);
lean_dec(v_start_868_);
lean_dec_ref(v_array_867_);
v___x_879_ = lean_array_push(v_b_866_, v___x_878_);
v_a_865_ = v___x_877_;
v_b_866_ = v___x_879_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6(lean_object* v_left_883_, lean_object* v_right_884_, lean_object* v_i_885_){
_start:
{
lean_object* v_start_886_; lean_object* v_stop_887_; lean_object* v___x_888_; uint8_t v___x_902_; 
v_start_886_ = lean_ctor_get(v_left_883_, 1);
v_stop_887_ = lean_ctor_get(v_left_883_, 2);
v___x_888_ = lean_nat_sub(v_stop_887_, v_start_886_);
v___x_902_ = lean_nat_dec_lt(v_i_885_, v___x_888_);
if (v___x_902_ == 0)
{
goto v___jp_889_;
}
else
{
lean_object* v_start_903_; lean_object* v_stop_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v_start_903_ = lean_ctor_get(v_right_884_, 1);
v_stop_904_ = lean_ctor_get(v_right_884_, 2);
v___x_905_ = lean_nat_sub(v_stop_904_, v_start_903_);
v___x_906_ = lean_nat_dec_lt(v_i_885_, v___x_905_);
if (v___x_906_ == 0)
{
lean_dec(v___x_905_);
goto v___jp_889_;
}
else
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; uint32_t v___x_914_; uint32_t v___x_915_; uint8_t v___x_916_; 
v___x_907_ = lean_nat_sub(v___x_888_, v_i_885_);
lean_dec(v___x_888_);
v___x_908_ = lean_unsigned_to_nat(1u);
v___x_909_ = lean_nat_sub(v___x_907_, v___x_908_);
v___x_910_ = l_Subarray_get___redArg(v_left_883_, v___x_909_);
lean_dec(v___x_909_);
v___x_911_ = lean_nat_sub(v___x_905_, v_i_885_);
lean_dec(v___x_905_);
v___x_912_ = lean_nat_sub(v___x_911_, v___x_908_);
v___x_913_ = l_Subarray_get___redArg(v_right_884_, v___x_912_);
lean_dec(v___x_912_);
v___x_914_ = lean_unbox_uint32(v___x_910_);
lean_dec(v___x_910_);
v___x_915_ = lean_unbox_uint32(v___x_913_);
lean_dec(v___x_913_);
v___x_916_ = lean_uint32_dec_eq(v___x_914_, v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
lean_dec(v_i_885_);
lean_inc_ref(v_left_883_);
v___x_917_ = l_Subarray_take___redArg(v_left_883_, v___x_907_);
v___x_918_ = l_Subarray_take___redArg(v_right_884_, v___x_911_);
lean_dec(v___x_911_);
v___x_919_ = l_Subarray_drop___redArg(v_left_883_, v___x_907_);
lean_dec(v___x_907_);
v___x_920_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_921_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(v___x_919_, v___x_920_);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_918_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_917_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
return v___x_923_;
}
else
{
lean_object* v___x_924_; 
lean_dec(v___x_911_);
lean_dec(v___x_907_);
v___x_924_ = lean_nat_add(v_i_885_, v___x_908_);
lean_dec(v_i_885_);
v_i_885_ = v___x_924_;
goto _start;
}
}
}
v___jp_889_:
{
lean_object* v_start_890_; lean_object* v_stop_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v_start_890_ = lean_ctor_get(v_right_884_, 1);
v_stop_891_ = lean_ctor_get(v_right_884_, 2);
v___x_892_ = lean_nat_sub(v___x_888_, v_i_885_);
lean_dec(v___x_888_);
lean_inc_ref(v_left_883_);
v___x_893_ = l_Subarray_take___redArg(v_left_883_, v___x_892_);
v___x_894_ = lean_nat_sub(v_stop_891_, v_start_890_);
v___x_895_ = lean_nat_sub(v___x_894_, v_i_885_);
lean_dec(v_i_885_);
lean_dec(v___x_894_);
v___x_896_ = l_Subarray_take___redArg(v_right_884_, v___x_895_);
lean_dec(v___x_895_);
v___x_897_ = l_Subarray_drop___redArg(v_left_883_, v___x_892_);
lean_dec(v___x_892_);
v___x_898_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_899_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(v___x_897_, v___x_898_);
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_896_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v___x_893_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
return v___x_901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4(lean_object* v_left_926_, lean_object* v_right_927_){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6(v_left_926_, v_right_927_, v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(lean_object* v_x_930_, lean_object* v_x_931_){
_start:
{
if (lean_obj_tag(v_x_931_) == 0)
{
lean_inc(v_x_930_);
return v_x_930_;
}
else
{
lean_object* v_key_932_; lean_object* v_value_933_; lean_object* v_tail_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
v_key_932_ = lean_ctor_get(v_x_931_, 0);
v_value_933_ = lean_ctor_get(v_x_931_, 1);
v_tail_934_ = lean_ctor_get(v_x_931_, 2);
v___x_935_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(v_x_930_, v_tail_934_);
lean_inc(v_value_933_);
lean_inc(v_key_932_);
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v_key_932_);
lean_ctor_set(v___x_936_, 1, v_value_933_);
v___x_937_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
lean_ctor_set(v___x_937_, 1, v___x_935_);
return v___x_937_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6___boxed(lean_object* v_x_938_, lean_object* v_x_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(v_x_938_, v_x_939_);
lean_dec(v_x_939_);
lean_dec(v_x_938_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7(lean_object* v_as_941_, size_t v_i_942_, size_t v_stop_943_, lean_object* v_b_944_){
_start:
{
uint8_t v___x_945_; 
v___x_945_ = lean_usize_dec_eq(v_i_942_, v_stop_943_);
if (v___x_945_ == 0)
{
size_t v___x_946_; size_t v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_946_ = ((size_t)1ULL);
v___x_947_ = lean_usize_sub(v_i_942_, v___x_946_);
v___x_948_ = lean_array_uget_borrowed(v_as_941_, v___x_947_);
v___x_949_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(v_b_944_, v___x_948_);
lean_dec(v_b_944_);
v_i_942_ = v___x_947_;
v_b_944_ = v___x_949_;
goto _start;
}
else
{
return v_b_944_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7___boxed(lean_object* v_as_951_, lean_object* v_i_952_, lean_object* v_stop_953_, lean_object* v_b_954_){
_start:
{
size_t v_i_boxed_955_; size_t v_stop_boxed_956_; lean_object* v_res_957_; 
v_i_boxed_955_ = lean_unbox_usize(v_i_952_);
lean_dec(v_i_952_);
v_stop_boxed_956_ = lean_unbox_usize(v_stop_953_);
lean_dec(v_stop_953_);
v_res_957_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7(v_as_951_, v_i_boxed_955_, v_stop_boxed_956_, v_b_954_);
lean_dec_ref(v_as_951_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(lean_object* v_histogram_958_, lean_object* v_index_959_, uint32_t v_val_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(v_histogram_958_, v_val_960_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_962_ = lean_unsigned_to_nat(1u);
v___x_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_963_, 0, v_index_959_);
v___x_964_ = lean_unsigned_to_nat(0u);
v___x_965_ = lean_box(0);
v___x_966_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_966_, 0, v___x_962_);
lean_ctor_set(v___x_966_, 1, v___x_963_);
lean_ctor_set(v___x_966_, 2, v___x_964_);
lean_ctor_set(v___x_966_, 3, v___x_965_);
v___x_967_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_histogram_958_, v_val_960_, v___x_966_);
return v___x_967_;
}
else
{
lean_object* v_val_968_; lean_object* v___x_970_; uint8_t v_isShared_971_; uint8_t v_isSharedCheck_989_; 
v_val_968_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_989_ == 0)
{
v___x_970_ = v___x_961_;
v_isShared_971_ = v_isSharedCheck_989_;
goto v_resetjp_969_;
}
else
{
lean_inc(v_val_968_);
lean_dec(v___x_961_);
v___x_970_ = lean_box(0);
v_isShared_971_ = v_isSharedCheck_989_;
goto v_resetjp_969_;
}
v_resetjp_969_:
{
lean_object* v_leftCount_972_; lean_object* v_rightCount_973_; lean_object* v_rightIndex_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_987_; 
v_leftCount_972_ = lean_ctor_get(v_val_968_, 0);
v_rightCount_973_ = lean_ctor_get(v_val_968_, 2);
v_rightIndex_974_ = lean_ctor_get(v_val_968_, 3);
v_isSharedCheck_987_ = !lean_is_exclusive(v_val_968_);
if (v_isSharedCheck_987_ == 0)
{
lean_object* v_unused_988_; 
v_unused_988_ = lean_ctor_get(v_val_968_, 1);
lean_dec(v_unused_988_);
v___x_976_ = v_val_968_;
v_isShared_977_ = v_isSharedCheck_987_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_rightIndex_974_);
lean_inc(v_rightCount_973_);
lean_inc(v_leftCount_972_);
lean_dec(v_val_968_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_987_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_981_; 
v___x_978_ = lean_unsigned_to_nat(1u);
v___x_979_ = lean_nat_add(v_leftCount_972_, v___x_978_);
lean_dec(v_leftCount_972_);
if (v_isShared_971_ == 0)
{
lean_ctor_set(v___x_970_, 0, v_index_959_);
v___x_981_ = v___x_970_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_index_959_);
v___x_981_ = v_reuseFailAlloc_986_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_983_; 
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 1, v___x_981_);
lean_ctor_set(v___x_976_, 0, v___x_979_);
v___x_983_ = v___x_976_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_985_, 1, v___x_981_);
lean_ctor_set(v_reuseFailAlloc_985_, 2, v_rightCount_973_);
lean_ctor_set(v_reuseFailAlloc_985_, 3, v_rightIndex_974_);
v___x_983_ = v_reuseFailAlloc_985_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
lean_object* v___x_984_; 
v___x_984_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_histogram_958_, v_val_960_, v___x_983_);
return v___x_984_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg___boxed(lean_object* v_histogram_990_, lean_object* v_index_991_, lean_object* v_val_992_){
_start:
{
uint32_t v_val_boxed_993_; lean_object* v_res_994_; 
v_val_boxed_993_ = lean_unbox_uint32(v_val_992_);
lean_dec(v_val_992_);
v_res_994_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(v_histogram_990_, v_index_991_, v_val_boxed_993_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg(lean_object* v_upperBound_995_, lean_object* v_fst_996_, lean_object* v___x_997_, lean_object* v_fst_998_, lean_object* v_a_999_, lean_object* v_b_1000_){
_start:
{
uint8_t v___x_1001_; 
v___x_1001_ = lean_nat_dec_lt(v_a_999_, v_upperBound_995_);
if (v___x_1001_ == 0)
{
lean_dec(v_a_999_);
return v_b_1000_;
}
else
{
lean_object* v___x_1002_; uint32_t v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1002_ = l_Subarray_get___redArg(v_fst_998_, v_a_999_);
v___x_1003_ = lean_unbox_uint32(v___x_1002_);
lean_dec(v___x_1002_);
lean_inc(v_a_999_);
v___x_1004_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(v_b_1000_, v_a_999_, v___x_1003_);
v___x_1005_ = lean_unsigned_to_nat(1u);
v___x_1006_ = lean_nat_add(v_a_999_, v___x_1005_);
lean_dec(v_a_999_);
v_a_999_ = v___x_1006_;
v_b_1000_ = v___x_1004_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg___boxed(lean_object* v_upperBound_1008_, lean_object* v_fst_1009_, lean_object* v___x_1010_, lean_object* v_fst_1011_, lean_object* v_a_1012_, lean_object* v_b_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg(v_upperBound_1008_, v_fst_1009_, v___x_1010_, v_fst_1011_, v_a_1012_, v_b_1013_);
lean_dec_ref(v_fst_1011_);
lean_dec(v___x_1010_);
lean_dec_ref(v_fst_1009_);
lean_dec(v_upperBound_1008_);
return v_res_1014_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1015_ = lean_box(0);
v___x_1016_ = lean_unsigned_to_nat(16u);
v___x_1017_ = lean_mk_array(v___x_1016_, v___x_1015_);
return v___x_1017_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v_hist_1020_; 
v___x_1018_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0);
v___x_1019_ = lean_unsigned_to_nat(0u);
v_hist_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_1020_, 0, v___x_1019_);
lean_ctor_set(v_hist_1020_, 1, v___x_1018_);
return v_hist_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(lean_object* v_left_1021_, lean_object* v_right_1022_){
_start:
{
lean_object* v___x_1023_; lean_object* v_snd_1024_; lean_object* v_fst_1025_; lean_object* v_fst_1026_; lean_object* v_snd_1027_; lean_object* v___x_1028_; lean_object* v_snd_1029_; lean_object* v_fst_1030_; lean_object* v_fst_1031_; lean_object* v_snd_1032_; lean_object* v_start_1033_; lean_object* v_stop_1034_; lean_object* v___x_1035_; lean_object* v_hist_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v_start_1039_; lean_object* v_stop_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v_buckets_1043_; lean_object* v___x_1044_; lean_object* v___y_1046_; lean_object* v___x_1072_; lean_object* v___x_1073_; uint8_t v___x_1074_; 
v___x_1023_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3(v_left_1021_, v_right_1022_);
v_snd_1024_ = lean_ctor_get(v___x_1023_, 1);
lean_inc(v_snd_1024_);
v_fst_1025_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_fst_1025_);
lean_dec_ref(v___x_1023_);
v_fst_1026_ = lean_ctor_get(v_snd_1024_, 0);
lean_inc(v_fst_1026_);
v_snd_1027_ = lean_ctor_get(v_snd_1024_, 1);
lean_inc(v_snd_1027_);
lean_dec(v_snd_1024_);
v___x_1028_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4(v_fst_1026_, v_snd_1027_);
v_snd_1029_ = lean_ctor_get(v___x_1028_, 1);
lean_inc(v_snd_1029_);
v_fst_1030_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_fst_1030_);
lean_dec_ref(v___x_1028_);
v_fst_1031_ = lean_ctor_get(v_snd_1029_, 0);
lean_inc(v_fst_1031_);
v_snd_1032_ = lean_ctor_get(v_snd_1029_, 1);
lean_inc(v_snd_1032_);
lean_dec(v_snd_1029_);
v_start_1033_ = lean_ctor_get(v_fst_1030_, 1);
v_stop_1034_ = lean_ctor_get(v_fst_1030_, 2);
v___x_1035_ = lean_unsigned_to_nat(0u);
v_hist_1036_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1);
v___x_1037_ = lean_nat_sub(v_stop_1034_, v_start_1033_);
v___x_1038_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg(v___x_1037_, v_fst_1031_, v___x_1037_, v_fst_1030_, v___x_1035_, v_hist_1036_);
v_start_1039_ = lean_ctor_get(v_fst_1031_, 1);
v_stop_1040_ = lean_ctor_get(v_fst_1031_, 2);
v___x_1041_ = lean_nat_sub(v_stop_1040_, v_start_1039_);
v___x_1042_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(v___x_1041_, v___x_1041_, v_fst_1031_, v___x_1037_, v___x_1035_, v___x_1038_);
lean_dec(v___x_1037_);
lean_dec(v___x_1041_);
v_buckets_1043_ = lean_ctor_get(v___x_1042_, 1);
lean_inc_ref(v_buckets_1043_);
lean_dec_ref(v___x_1042_);
v___x_1044_ = lean_box(0);
v___x_1072_ = lean_box(0);
v___x_1073_ = lean_array_get_size(v_buckets_1043_);
v___x_1074_ = lean_nat_dec_lt(v___x_1035_, v___x_1073_);
if (v___x_1074_ == 0)
{
lean_dec_ref(v_buckets_1043_);
v___y_1046_ = v___x_1072_;
goto v___jp_1045_;
}
else
{
size_t v___x_1075_; size_t v___x_1076_; lean_object* v___x_1077_; 
v___x_1075_ = lean_usize_of_nat(v___x_1073_);
v___x_1076_ = ((size_t)0ULL);
v___x_1077_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7(v_buckets_1043_, v___x_1075_, v___x_1076_, v___x_1072_);
lean_dec_ref(v_buckets_1043_);
v___y_1046_ = v___x_1077_;
goto v___jp_1045_;
}
v___jp_1045_:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg(v___y_1046_, v___x_1044_);
lean_dec(v___y_1046_);
if (lean_obj_tag(v___x_1047_) == 1)
{
lean_object* v_val_1048_; lean_object* v_snd_1049_; lean_object* v_snd_1050_; lean_object* v_fst_1051_; lean_object* v_fst_1052_; lean_object* v_snd_1053_; lean_object* v___x_1054_; lean_object* v_fst_1055_; lean_object* v_snd_1056_; lean_object* v___x_1057_; lean_object* v_fst_1058_; lean_object* v_snd_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_val_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_val_1048_);
lean_dec_ref(v___x_1047_);
v_snd_1049_ = lean_ctor_get(v_val_1048_, 1);
lean_inc(v_snd_1049_);
lean_dec(v_val_1048_);
v_snd_1050_ = lean_ctor_get(v_snd_1049_, 1);
lean_inc(v_snd_1050_);
v_fst_1051_ = lean_ctor_get(v_snd_1049_, 0);
lean_inc(v_fst_1051_);
lean_dec(v_snd_1049_);
v_fst_1052_ = lean_ctor_get(v_snd_1050_, 0);
lean_inc(v_fst_1052_);
v_snd_1053_ = lean_ctor_get(v_snd_1050_, 1);
lean_inc(v_snd_1053_);
lean_dec(v_snd_1050_);
v___x_1054_ = l_Subarray_split___redArg(v_fst_1030_, v_fst_1052_);
lean_dec(v_fst_1052_);
v_fst_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_fst_1055_);
v_snd_1056_ = lean_ctor_get(v___x_1054_, 1);
lean_inc(v_snd_1056_);
lean_dec_ref(v___x_1054_);
v___x_1057_ = l_Subarray_split___redArg(v_fst_1031_, v_snd_1053_);
lean_dec(v_snd_1053_);
v_fst_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_fst_1058_);
v_snd_1059_ = lean_ctor_get(v___x_1057_, 1);
lean_inc(v_snd_1059_);
lean_dec_ref(v___x_1057_);
v___x_1060_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v_fst_1055_, v_fst_1058_);
v___x_1061_ = l_Array_append___redArg(v_fst_1025_, v___x_1060_);
lean_dec_ref(v___x_1060_);
v___x_1062_ = lean_unsigned_to_nat(1u);
v___x_1063_ = lean_mk_empty_array_with_capacity(v___x_1062_);
v___x_1064_ = lean_array_push(v___x_1063_, v_fst_1051_);
v___x_1065_ = l_Array_append___redArg(v___x_1061_, v___x_1064_);
lean_dec_ref(v___x_1064_);
v___x_1066_ = l_Subarray_drop___redArg(v_snd_1056_, v___x_1062_);
v___x_1067_ = l_Subarray_drop___redArg(v_snd_1059_, v___x_1062_);
v___x_1068_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v___x_1066_, v___x_1067_);
v___x_1069_ = l_Array_append___redArg(v___x_1065_, v___x_1068_);
lean_dec_ref(v___x_1068_);
v___x_1070_ = l_Array_append___redArg(v___x_1069_, v_snd_1032_);
lean_dec(v_snd_1032_);
return v___x_1070_;
}
else
{
lean_object* v___x_1071_; 
lean_dec(v___x_1047_);
lean_dec(v_fst_1031_);
lean_dec(v_fst_1030_);
v___x_1071_ = l_Array_append___redArg(v_fst_1025_, v_snd_1032_);
lean_dec(v_snd_1032_);
return v___x_1071_;
}
}
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
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed__const__1(void){
_start:
{
uint32_t v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = 65;
v___x_1099_ = lean_box_uint32(v___x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(lean_object* v_edited_1100_, lean_object* v___x_1101_, uint32_t v_a_1102_, lean_object* v_b_1103_){
_start:
{
lean_object* v_fst_1104_; lean_object* v_snd_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1132_; 
v_fst_1104_ = lean_ctor_get(v_b_1103_, 0);
v_snd_1105_ = lean_ctor_get(v_b_1103_, 1);
v_isSharedCheck_1132_ = !lean_is_exclusive(v_b_1103_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1107_ = v_b_1103_;
v_isShared_1108_ = v_isSharedCheck_1132_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_snd_1105_);
lean_inc(v_fst_1104_);
lean_dec(v_b_1103_);
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
v___x_1127_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed__const__1;
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
v___x_1115_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed__const__1;
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
v_b_1103_ = v___x_1123_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed(lean_object* v_edited_1133_, lean_object* v___x_1134_, lean_object* v_a_1135_, lean_object* v_b_1136_){
_start:
{
uint32_t v_a_boxed_1137_; lean_object* v_res_1138_; 
v_a_boxed_1137_ = lean_unbox_uint32(v_a_1135_);
lean_dec(v_a_1135_);
v_res_1138_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v_edited_1133_, v___x_1134_, v_a_boxed_1137_, v_b_1136_);
lean_dec(v___x_1134_);
lean_dec_ref(v_edited_1133_);
return v_res_1138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(lean_object* v_original_1139_, lean_object* v___x_1140_, uint32_t v_a_1141_, lean_object* v_b_1142_){
_start:
{
lean_object* v_fst_1143_; lean_object* v_snd_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1171_; 
v_fst_1143_ = lean_ctor_get(v_b_1142_, 0);
v_snd_1144_ = lean_ctor_get(v_b_1142_, 1);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_b_1142_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1146_ = v_b_1142_;
v_isShared_1147_ = v_isSharedCheck_1171_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_snd_1144_);
lean_inc(v_fst_1143_);
lean_dec(v_b_1142_);
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
v___x_1166_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed__const__1;
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
v___x_1154_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed__const__1;
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
v_b_1142_ = v___x_1162_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___boxed(lean_object* v_original_1172_, lean_object* v___x_1173_, lean_object* v_a_1174_, lean_object* v_b_1175_){
_start:
{
uint32_t v_a_boxed_1176_; lean_object* v_res_1177_; 
v_a_boxed_1176_ = lean_unbox_uint32(v_a_1174_);
lean_dec(v_a_1174_);
v_res_1177_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(v_original_1172_, v___x_1173_, v_a_boxed_1176_, v_b_1175_);
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
v___x_1201_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(v_original_1178_, v___x_1179_, v___x_1200_, v___x_1199_);
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
v___x_1210_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v_edited_1180_, v___x_1181_, v___x_1209_, v___x_1208_);
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
v___x_1272_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(v_original_1251_, v___x_1252_, v___x_1271_, v___x_1270_);
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
v___x_1281_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v_edited_1249_, v___x_1250_, v___x_1280_, v___x_1279_);
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
v___x_1356_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(v___x_1330_, v_original_1327_, v___x_1355_);
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
v___x_1363_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(v___x_1335_, v_edited_1328_, v___x_1362_);
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
lean_dec_ref(v___x_1402_);
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5(lean_object* v_as_1432_, lean_object* v_as_x27_1433_, lean_object* v_b_1434_, lean_object* v_a_1435_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg(v_as_x27_1433_, v_b_1434_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___boxed(lean_object* v_as_1437_, lean_object* v_as_x27_1438_, lean_object* v_b_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5(v_as_1437_, v_as_x27_1438_, v_b_1439_, v_a_1440_);
lean_dec(v_as_x27_1438_);
lean_dec(v_as_1437_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8(lean_object* v_lsize_1442_, lean_object* v_rsize_1443_, lean_object* v_histogram_1444_, lean_object* v_index_1445_, uint32_t v_val_1446_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(v_histogram_1444_, v_index_1445_, v_val_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___boxed(lean_object* v_lsize_1448_, lean_object* v_rsize_1449_, lean_object* v_histogram_1450_, lean_object* v_index_1451_, lean_object* v_val_1452_){
_start:
{
uint32_t v_val_boxed_1453_; lean_object* v_res_1454_; 
v_val_boxed_1453_ = lean_unbox_uint32(v_val_1452_);
lean_dec(v_val_1452_);
v_res_1454_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8(v_lsize_1448_, v_rsize_1449_, v_histogram_1450_, v_index_1451_, v_val_boxed_1453_);
lean_dec(v_rsize_1449_);
lean_dec(v_lsize_1448_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9(lean_object* v_upperBound_1455_, lean_object* v___x_1456_, lean_object* v_fst_1457_, lean_object* v___x_1458_, lean_object* v_inst_1459_, lean_object* v_R_1460_, lean_object* v_a_1461_, lean_object* v_b_1462_, lean_object* v_c_1463_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(v_upperBound_1455_, v___x_1456_, v_fst_1457_, v___x_1458_, v_a_1461_, v_b_1462_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___boxed(lean_object* v_upperBound_1465_, lean_object* v___x_1466_, lean_object* v_fst_1467_, lean_object* v___x_1468_, lean_object* v_inst_1469_, lean_object* v_R_1470_, lean_object* v_a_1471_, lean_object* v_b_1472_, lean_object* v_c_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9(v_upperBound_1465_, v___x_1466_, v_fst_1467_, v___x_1468_, v_inst_1469_, v_R_1470_, v_a_1471_, v_b_1472_, v_c_1473_);
lean_dec(v___x_1468_);
lean_dec_ref(v_fst_1467_);
lean_dec(v___x_1466_);
lean_dec(v_upperBound_1465_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10(lean_object* v_lsize_1475_, lean_object* v_rsize_1476_, lean_object* v_histogram_1477_, lean_object* v_index_1478_, uint32_t v_val_1479_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(v_histogram_1477_, v_index_1478_, v_val_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___boxed(lean_object* v_lsize_1481_, lean_object* v_rsize_1482_, lean_object* v_histogram_1483_, lean_object* v_index_1484_, lean_object* v_val_1485_){
_start:
{
uint32_t v_val_boxed_1486_; lean_object* v_res_1487_; 
v_val_boxed_1486_ = lean_unbox_uint32(v_val_1485_);
lean_dec(v_val_1485_);
v_res_1487_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10(v_lsize_1481_, v_rsize_1482_, v_histogram_1483_, v_index_1484_, v_val_boxed_1486_);
lean_dec(v_rsize_1482_);
lean_dec(v_lsize_1481_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11(lean_object* v_upperBound_1488_, lean_object* v_fst_1489_, lean_object* v___x_1490_, lean_object* v_fst_1491_, lean_object* v_inst_1492_, lean_object* v_R_1493_, lean_object* v_a_1494_, lean_object* v_b_1495_, lean_object* v_c_1496_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg(v_upperBound_1488_, v_fst_1489_, v___x_1490_, v_fst_1491_, v_a_1494_, v_b_1495_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___boxed(lean_object* v_upperBound_1498_, lean_object* v_fst_1499_, lean_object* v___x_1500_, lean_object* v_fst_1501_, lean_object* v_inst_1502_, lean_object* v_R_1503_, lean_object* v_a_1504_, lean_object* v_b_1505_, lean_object* v_c_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11(v_upperBound_1498_, v_fst_1499_, v___x_1500_, v_fst_1501_, v_inst_1502_, v_R_1503_, v_a_1504_, v_b_1505_, v_c_1506_);
lean_dec_ref(v_fst_1501_);
lean_dec(v___x_1500_);
lean_dec_ref(v_fst_1499_);
lean_dec(v_upperBound_1498_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11(lean_object* v_00_u03b2_1508_, lean_object* v_m_1509_, uint32_t v_a_1510_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(v_m_1509_, v_a_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___boxed(lean_object* v_00_u03b2_1512_, lean_object* v_m_1513_, lean_object* v_a_1514_){
_start:
{
uint32_t v_a_boxed_1515_; lean_object* v_res_1516_; 
v_a_boxed_1515_ = lean_unbox_uint32(v_a_1514_);
lean_dec(v_a_1514_);
v_res_1516_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11(v_00_u03b2_1512_, v_m_1513_, v_a_boxed_1515_);
lean_dec_ref(v_m_1513_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12(lean_object* v_00_u03b2_1517_, lean_object* v_m_1518_, uint32_t v_a_1519_, lean_object* v_b_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_m_1518_, v_a_1519_, v_b_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___boxed(lean_object* v_00_u03b2_1522_, lean_object* v_m_1523_, lean_object* v_a_1524_, lean_object* v_b_1525_){
_start:
{
uint32_t v_a_boxed_1526_; lean_object* v_res_1527_; 
v_a_boxed_1526_ = lean_unbox_uint32(v_a_1524_);
lean_dec(v_a_1524_);
v_res_1527_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12(v_00_u03b2_1522_, v_m_1523_, v_a_boxed_1526_, v_b_1525_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14(lean_object* v_inst_1528_, lean_object* v_R_1529_, lean_object* v_a_1530_, lean_object* v_b_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(v_a_1530_, v_b_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20(lean_object* v_00_u03b2_1533_, uint32_t v_a_1534_, lean_object* v_x_1535_){
_start:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg(v_a_1534_, v_x_1535_);
return v___x_1536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___boxed(lean_object* v_00_u03b2_1537_, lean_object* v_a_1538_, lean_object* v_x_1539_){
_start:
{
uint32_t v_a_boxed_1540_; lean_object* v_res_1541_; 
v_a_boxed_1540_ = lean_unbox_uint32(v_a_1538_);
lean_dec(v_a_1538_);
v_res_1541_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20(v_00_u03b2_1537_, v_a_boxed_1540_, v_x_1539_);
lean_dec(v_x_1539_);
return v_res_1541_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22(lean_object* v_00_u03b2_1542_, uint32_t v_a_1543_, lean_object* v_x_1544_){
_start:
{
uint8_t v___x_1545_; 
v___x_1545_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg(v_a_1543_, v_x_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___boxed(lean_object* v_00_u03b2_1546_, lean_object* v_a_1547_, lean_object* v_x_1548_){
_start:
{
uint32_t v_a_boxed_1549_; uint8_t v_res_1550_; lean_object* v_r_1551_; 
v_a_boxed_1549_ = lean_unbox_uint32(v_a_1547_);
lean_dec(v_a_1547_);
v_res_1550_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22(v_00_u03b2_1546_, v_a_boxed_1549_, v_x_1548_);
lean_dec(v_x_1548_);
v_r_1551_ = lean_box(v_res_1550_);
return v_r_1551_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23(lean_object* v_00_u03b2_1552_, lean_object* v_data_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23___redArg(v_data_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24(lean_object* v_00_u03b2_1555_, uint32_t v_a_1556_, lean_object* v_b_1557_, lean_object* v_x_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(v_a_1556_, v_b_1557_, v_x_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___boxed(lean_object* v_00_u03b2_1560_, lean_object* v_a_1561_, lean_object* v_b_1562_, lean_object* v_x_1563_){
_start:
{
uint32_t v_a_boxed_1564_; lean_object* v_res_1565_; 
v_a_boxed_1564_ = lean_unbox_uint32(v_a_1561_);
lean_dec(v_a_1561_);
v_res_1565_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24(v_00_u03b2_1560_, v_a_boxed_1564_, v_b_1562_, v_x_1563_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28(lean_object* v_00_u03b2_1566_, lean_object* v_i_1567_, lean_object* v_source_1568_, lean_object* v_target_1569_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28___redArg(v_i_1567_, v_source_1568_, v_target_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_1571_, lean_object* v_x_1572_, lean_object* v_x_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29___redArg(v_x_1572_, v_x_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(lean_object* v_s_1575_, lean_object* v_stopPos_1576_, lean_object* v_i_1577_){
_start:
{
uint8_t v___y_1582_; uint8_t v___x_1583_; 
v___x_1583_ = lean_nat_dec_lt(v_i_1577_, v_stopPos_1576_);
if (v___x_1583_ == 0)
{
return v_i_1577_;
}
else
{
uint32_t v___x_1584_; uint8_t v___y_1586_; uint32_t v___x_1591_; uint8_t v___x_1592_; 
v___x_1584_ = lean_string_utf8_get(v_s_1575_, v_i_1577_);
v___x_1591_ = 32;
v___x_1592_ = lean_uint32_dec_eq(v___x_1584_, v___x_1591_);
if (v___x_1592_ == 0)
{
uint32_t v___x_1593_; uint8_t v___x_1594_; 
v___x_1593_ = 9;
v___x_1594_ = lean_uint32_dec_eq(v___x_1584_, v___x_1593_);
v___y_1586_ = v___x_1594_;
goto v___jp_1585_;
}
else
{
v___y_1586_ = v___x_1592_;
goto v___jp_1585_;
}
v___jp_1585_:
{
if (v___y_1586_ == 0)
{
uint32_t v___x_1587_; uint8_t v___x_1588_; 
v___x_1587_ = 13;
v___x_1588_ = lean_uint32_dec_eq(v___x_1584_, v___x_1587_);
if (v___x_1588_ == 0)
{
uint32_t v___x_1589_; uint8_t v___x_1590_; 
v___x_1589_ = 10;
v___x_1590_ = lean_uint32_dec_eq(v___x_1584_, v___x_1589_);
v___y_1582_ = v___x_1590_;
goto v___jp_1581_;
}
else
{
v___y_1582_ = v___x_1588_;
goto v___jp_1581_;
}
}
else
{
goto v___jp_1578_;
}
}
}
v___jp_1578_:
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_string_utf8_next(v_s_1575_, v_i_1577_);
lean_dec(v_i_1577_);
v_i_1577_ = v___x_1579_;
goto _start;
}
v___jp_1581_:
{
if (v___y_1582_ == 0)
{
return v_i_1577_;
}
else
{
goto v___jp_1578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0___boxed(lean_object* v_s_1595_, lean_object* v_stopPos_1596_, lean_object* v_i_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1595_, v_stopPos_1596_, v_i_1597_);
lean_dec(v_stopPos_1596_);
lean_dec_ref(v_s_1595_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(lean_object* v_s_1599_, lean_object* v_b_1600_, lean_object* v_i_1601_, lean_object* v_r_1602_, lean_object* v_ws_1603_){
_start:
{
uint8_t v___y_1613_; uint8_t v___x_1616_; 
v___x_1616_ = lean_string_utf8_at_end(v_s_1599_, v_i_1601_);
if (v___x_1616_ == 0)
{
uint32_t v___x_1617_; uint8_t v___y_1619_; uint32_t v___x_1624_; uint8_t v___x_1625_; 
v___x_1617_ = lean_string_utf8_get(v_s_1599_, v_i_1601_);
v___x_1624_ = 32;
v___x_1625_ = lean_uint32_dec_eq(v___x_1617_, v___x_1624_);
if (v___x_1625_ == 0)
{
uint32_t v___x_1626_; uint8_t v___x_1627_; 
v___x_1626_ = 9;
v___x_1627_ = lean_uint32_dec_eq(v___x_1617_, v___x_1626_);
v___y_1619_ = v___x_1627_;
goto v___jp_1618_;
}
else
{
v___y_1619_ = v___x_1625_;
goto v___jp_1618_;
}
v___jp_1618_:
{
if (v___y_1619_ == 0)
{
uint32_t v___x_1620_; uint8_t v___x_1621_; 
v___x_1620_ = 13;
v___x_1621_ = lean_uint32_dec_eq(v___x_1617_, v___x_1620_);
if (v___x_1621_ == 0)
{
uint32_t v___x_1622_; uint8_t v___x_1623_; 
v___x_1622_ = 10;
v___x_1623_ = lean_uint32_dec_eq(v___x_1617_, v___x_1622_);
v___y_1613_ = v___x_1623_;
goto v___jp_1612_;
}
else
{
v___y_1613_ = v___x_1621_;
goto v___jp_1612_;
}
}
else
{
goto v___jp_1604_;
}
}
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1628_ = lean_string_utf8_extract(v_s_1599_, v_b_1600_, v_i_1601_);
lean_dec(v_i_1601_);
lean_dec(v_b_1600_);
v___x_1629_ = lean_array_push(v_r_1602_, v___x_1628_);
v___x_1630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1630_, 0, v___x_1629_);
lean_ctor_set(v___x_1630_, 1, v_ws_1603_);
return v___x_1630_;
}
v___jp_1604_:
{
lean_object* v___x_1605_; lean_object* v_e_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1605_ = lean_string_utf8_byte_size(v_s_1599_);
lean_inc(v_i_1601_);
v_e_1606_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1599_, v___x_1605_, v_i_1601_);
v___x_1607_ = lean_string_utf8_extract(v_s_1599_, v_b_1600_, v_i_1601_);
lean_dec(v_b_1600_);
v___x_1608_ = lean_array_push(v_r_1602_, v___x_1607_);
v___x_1609_ = lean_string_utf8_extract(v_s_1599_, v_i_1601_, v_e_1606_);
lean_dec(v_i_1601_);
v___x_1610_ = lean_array_push(v_ws_1603_, v___x_1609_);
lean_inc(v_e_1606_);
v_b_1600_ = v_e_1606_;
v_i_1601_ = v_e_1606_;
v_r_1602_ = v___x_1608_;
v_ws_1603_ = v___x_1610_;
goto _start;
}
v___jp_1612_:
{
if (v___y_1613_ == 0)
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_string_utf8_next(v_s_1599_, v_i_1601_);
lean_dec(v_i_1601_);
v_i_1601_ = v___x_1614_;
goto _start;
}
else
{
goto v___jp_1604_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux___boxed(lean_object* v_s_1631_, lean_object* v_b_1632_, lean_object* v_i_1633_, lean_object* v_r_1634_, lean_object* v_ws_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1631_, v_b_1632_, v_i_1633_, v_r_1634_, v_ws_1635_);
lean_dec_ref(v_s_1631_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(lean_object* v_s_1639_){
_start:
{
lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1640_ = lean_unsigned_to_nat(0u);
v___x_1641_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_1642_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1639_, v___x_1640_, v___x_1640_, v___x_1641_, v___x_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___boxed(lean_object* v_s_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_1643_);
lean_dec_ref(v_s_1643_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(size_t v_sz_1645_, size_t v_i_1646_, lean_object* v_bs_1647_){
_start:
{
uint8_t v___x_1648_; 
v___x_1648_ = lean_usize_dec_lt(v_i_1646_, v_sz_1645_);
if (v___x_1648_ == 0)
{
return v_bs_1647_;
}
else
{
lean_object* v_v_1649_; lean_object* v_fst_1650_; lean_object* v_snd_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1685_; 
v_v_1649_ = lean_array_uget(v_bs_1647_, v_i_1646_);
v_fst_1650_ = lean_ctor_get(v_v_1649_, 0);
v_snd_1651_ = lean_ctor_get(v_v_1649_, 1);
v_isSharedCheck_1685_ = !lean_is_exclusive(v_v_1649_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1653_ = v_v_1649_;
v_isShared_1654_ = v_isSharedCheck_1685_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_snd_1651_);
lean_inc(v_fst_1650_);
lean_dec(v_v_1649_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1685_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v_bs_x27_1656_; lean_object* v___y_1658_; lean_object* v___x_1663_; lean_object* v___x_1664_; uint8_t v___x_1665_; 
v___x_1655_ = lean_unsigned_to_nat(0u);
v_bs_x27_1656_ = lean_array_uset(v_bs_1647_, v_i_1646_, v___x_1655_);
v___x_1663_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_1664_ = lean_array_get_size(v_snd_1651_);
v___x_1665_ = lean_nat_dec_lt(v___x_1655_, v___x_1664_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1667_; 
lean_dec(v_snd_1651_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 1, v___x_1663_);
v___x_1667_ = v___x_1653_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_fst_1650_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v___x_1663_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
v___y_1658_ = v___x_1667_;
goto v___jp_1657_;
}
}
else
{
uint8_t v___x_1669_; 
v___x_1669_ = lean_nat_dec_le(v___x_1664_, v___x_1664_);
if (v___x_1669_ == 0)
{
if (v___x_1665_ == 0)
{
lean_object* v___x_1671_; 
lean_dec(v_snd_1651_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 1, v___x_1663_);
v___x_1671_ = v___x_1653_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_fst_1650_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v___x_1663_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
v___y_1658_ = v___x_1671_;
goto v___jp_1657_;
}
}
else
{
size_t v___x_1673_; size_t v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1673_ = ((size_t)0ULL);
v___x_1674_ = lean_usize_of_nat(v___x_1664_);
v___x_1675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_1651_, v___x_1673_, v___x_1674_, v___x_1663_);
lean_dec(v_snd_1651_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 1, v___x_1675_);
v___x_1677_ = v___x_1653_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_fst_1650_);
lean_ctor_set(v_reuseFailAlloc_1678_, 1, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
v___y_1658_ = v___x_1677_;
goto v___jp_1657_;
}
}
}
else
{
size_t v___x_1679_; size_t v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1679_ = ((size_t)0ULL);
v___x_1680_ = lean_usize_of_nat(v___x_1664_);
v___x_1681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_1651_, v___x_1679_, v___x_1680_, v___x_1663_);
lean_dec(v_snd_1651_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 1, v___x_1681_);
v___x_1683_ = v___x_1653_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_fst_1650_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
v___y_1658_ = v___x_1683_;
goto v___jp_1657_;
}
}
}
v___jp_1657_:
{
size_t v___x_1659_; size_t v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = ((size_t)1ULL);
v___x_1660_ = lean_usize_add(v_i_1646_, v___x_1659_);
v___x_1661_ = lean_array_uset(v_bs_x27_1656_, v_i_1646_, v___y_1658_);
v_i_1646_ = v___x_1660_;
v_bs_1647_ = v___x_1661_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0___boxed(lean_object* v_sz_1686_, lean_object* v_i_1687_, lean_object* v_bs_1688_){
_start:
{
size_t v_sz_boxed_1689_; size_t v_i_boxed_1690_; lean_object* v_res_1691_; 
v_sz_boxed_1689_ = lean_unbox_usize(v_sz_1686_);
lean_dec(v_sz_1686_);
v_i_boxed_1690_ = lean_unbox_usize(v_i_1687_);
lean_dec(v_i_1687_);
v_res_1691_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_boxed_1689_, v_i_boxed_1690_, v_bs_1688_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(size_t v_sz_1692_, size_t v_i_1693_, lean_object* v_bs_1694_){
_start:
{
uint8_t v___x_1695_; 
v___x_1695_ = lean_usize_dec_lt(v_i_1693_, v_sz_1692_);
if (v___x_1695_ == 0)
{
return v_bs_1694_;
}
else
{
lean_object* v_v_1696_; lean_object* v___x_1697_; lean_object* v_bs_x27_1698_; uint8_t v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; size_t v___x_1702_; size_t v___x_1703_; lean_object* v___x_1704_; 
v_v_1696_ = lean_array_uget(v_bs_1694_, v_i_1693_);
v___x_1697_ = lean_unsigned_to_nat(0u);
v_bs_x27_1698_ = lean_array_uset(v_bs_1694_, v_i_1693_, v___x_1697_);
v___x_1699_ = 0;
v___x_1700_ = lean_box(v___x_1699_);
v___x_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1700_);
lean_ctor_set(v___x_1701_, 1, v_v_1696_);
v___x_1702_ = ((size_t)1ULL);
v___x_1703_ = lean_usize_add(v_i_1693_, v___x_1702_);
v___x_1704_ = lean_array_uset(v_bs_x27_1698_, v_i_1693_, v___x_1701_);
v_i_1693_ = v___x_1703_;
v_bs_1694_ = v___x_1704_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8___boxed(lean_object* v_sz_1706_, lean_object* v_i_1707_, lean_object* v_bs_1708_){
_start:
{
size_t v_sz_boxed_1709_; size_t v_i_boxed_1710_; lean_object* v_res_1711_; 
v_sz_boxed_1709_ = lean_unbox_usize(v_sz_1706_);
lean_dec(v_sz_1706_);
v_i_boxed_1710_ = lean_unbox_usize(v_i_1707_);
lean_dec(v_i_1707_);
v_res_1711_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_boxed_1709_, v_i_boxed_1710_, v_bs_1708_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(lean_object* v_original_1712_, lean_object* v___x_1713_, lean_object* v_a_1714_, lean_object* v_b_1715_){
_start:
{
lean_object* v_fst_1716_; lean_object* v_snd_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1742_; 
v_fst_1716_ = lean_ctor_get(v_b_1715_, 0);
v_snd_1717_ = lean_ctor_get(v_b_1715_, 1);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_b_1715_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1719_ = v_b_1715_;
v_isShared_1720_ = v_isSharedCheck_1742_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_snd_1717_);
lean_inc(v_fst_1716_);
lean_dec(v_b_1715_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1742_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; uint8_t v___y_1723_; uint8_t v___x_1738_; 
v___x_1721_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_1738_ = lean_nat_dec_lt(v_snd_1717_, v___x_1713_);
if (v___x_1738_ == 0)
{
v___y_1723_ = v___x_1738_;
goto v___jp_1722_;
}
else
{
lean_object* v___x_1739_; uint8_t v___x_1740_; 
v___x_1739_ = lean_array_get_borrowed(v___x_1721_, v_original_1712_, v_snd_1717_);
v___x_1740_ = lean_string_dec_eq(v___x_1739_, v_a_1714_);
if (v___x_1740_ == 0)
{
v___y_1723_ = v___x_1738_;
goto v___jp_1722_;
}
else
{
lean_object* v___x_1741_; 
lean_del_object(v___x_1719_);
v___x_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1741_, 0, v_fst_1716_);
lean_ctor_set(v___x_1741_, 1, v_snd_1717_);
return v___x_1741_;
}
}
v___jp_1722_:
{
if (v___y_1723_ == 0)
{
lean_object* v___x_1725_; 
if (v_isShared_1720_ == 0)
{
v___x_1725_ = v___x_1719_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_fst_1716_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_snd_1717_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
else
{
uint8_t v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1727_ = 1;
v___x_1728_ = lean_array_get_borrowed(v___x_1721_, v_original_1712_, v_snd_1717_);
v___x_1729_ = lean_box(v___x_1727_);
lean_inc(v___x_1728_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 1, v___x_1728_);
lean_ctor_set(v___x_1719_, 0, v___x_1729_);
v___x_1731_ = v___x_1719_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1737_, 1, v___x_1728_);
v___x_1731_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1732_ = lean_array_push(v_fst_1716_, v___x_1731_);
v___x_1733_ = lean_unsigned_to_nat(1u);
v___x_1734_ = lean_nat_add(v_snd_1717_, v___x_1733_);
lean_dec(v_snd_1717_);
v___x_1735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1735_, 0, v___x_1732_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
v_b_1715_ = v___x_1735_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___boxed(lean_object* v_original_1743_, lean_object* v___x_1744_, lean_object* v_a_1745_, lean_object* v_b_1746_){
_start:
{
lean_object* v_res_1747_; 
v_res_1747_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(v_original_1743_, v___x_1744_, v_a_1745_, v_b_1746_);
lean_dec_ref(v_a_1745_);
lean_dec(v___x_1744_);
lean_dec_ref(v_original_1743_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(lean_object* v_edited_1748_, lean_object* v___x_1749_, lean_object* v_a_1750_, lean_object* v_b_1751_){
_start:
{
lean_object* v_fst_1752_; lean_object* v_snd_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1778_; 
v_fst_1752_ = lean_ctor_get(v_b_1751_, 0);
v_snd_1753_ = lean_ctor_get(v_b_1751_, 1);
v_isSharedCheck_1778_ = !lean_is_exclusive(v_b_1751_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1755_ = v_b_1751_;
v_isShared_1756_ = v_isSharedCheck_1778_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_snd_1753_);
lean_inc(v_fst_1752_);
lean_dec(v_b_1751_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1778_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1757_; uint8_t v___y_1759_; uint8_t v___x_1774_; 
v___x_1757_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_1774_ = lean_nat_dec_lt(v_snd_1753_, v___x_1749_);
if (v___x_1774_ == 0)
{
v___y_1759_ = v___x_1774_;
goto v___jp_1758_;
}
else
{
lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1775_ = lean_array_get_borrowed(v___x_1757_, v_edited_1748_, v_snd_1753_);
v___x_1776_ = lean_string_dec_eq(v___x_1775_, v_a_1750_);
if (v___x_1776_ == 0)
{
v___y_1759_ = v___x_1774_;
goto v___jp_1758_;
}
else
{
lean_object* v___x_1777_; 
lean_del_object(v___x_1755_);
v___x_1777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1777_, 0, v_fst_1752_);
lean_ctor_set(v___x_1777_, 1, v_snd_1753_);
return v___x_1777_;
}
}
v___jp_1758_:
{
if (v___y_1759_ == 0)
{
lean_object* v___x_1761_; 
if (v_isShared_1756_ == 0)
{
v___x_1761_ = v___x_1755_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_fst_1752_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_snd_1753_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
else
{
uint8_t v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1767_; 
v___x_1763_ = 0;
v___x_1764_ = lean_array_get_borrowed(v___x_1757_, v_edited_1748_, v_snd_1753_);
v___x_1765_ = lean_box(v___x_1763_);
lean_inc(v___x_1764_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 1, v___x_1764_);
lean_ctor_set(v___x_1755_, 0, v___x_1765_);
v___x_1767_ = v___x_1755_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v___x_1765_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v___x_1764_);
v___x_1767_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1768_ = lean_array_push(v_fst_1752_, v___x_1767_);
v___x_1769_ = lean_unsigned_to_nat(1u);
v___x_1770_ = lean_nat_add(v_snd_1753_, v___x_1769_);
lean_dec(v_snd_1753_);
v___x_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1768_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
v_b_1751_ = v___x_1771_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___boxed(lean_object* v_edited_1779_, lean_object* v___x_1780_, lean_object* v_a_1781_, lean_object* v_b_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v_edited_1779_, v___x_1780_, v_a_1781_, v_b_1782_);
lean_dec_ref(v_a_1781_);
lean_dec(v___x_1780_);
lean_dec_ref(v_edited_1779_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(lean_object* v_original_1784_, lean_object* v___x_1785_, lean_object* v_edited_1786_, lean_object* v___x_1787_, lean_object* v_as_1788_, size_t v_sz_1789_, size_t v_i_1790_, lean_object* v_b_1791_){
_start:
{
uint8_t v___x_1792_; 
v___x_1792_ = lean_usize_dec_lt(v_i_1790_, v_sz_1789_);
if (v___x_1792_ == 0)
{
return v_b_1791_;
}
else
{
lean_object* v_snd_1793_; lean_object* v_fst_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1841_; 
v_snd_1793_ = lean_ctor_get(v_b_1791_, 1);
v_fst_1794_ = lean_ctor_get(v_b_1791_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v_b_1791_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1796_ = v_b_1791_;
v_isShared_1797_ = v_isSharedCheck_1841_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_snd_1793_);
lean_inc(v_fst_1794_);
lean_dec(v_b_1791_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1841_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v_fst_1798_; lean_object* v_snd_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1840_; 
v_fst_1798_ = lean_ctor_get(v_snd_1793_, 0);
v_snd_1799_ = lean_ctor_get(v_snd_1793_, 1);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_snd_1793_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1801_ = v_snd_1793_;
v_isShared_1802_ = v_isSharedCheck_1840_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_snd_1799_);
lean_inc(v_fst_1798_);
lean_dec(v_snd_1793_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1840_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v_a_1803_; lean_object* v___x_1805_; 
v_a_1803_ = lean_array_uget_borrowed(v_as_1788_, v_i_1790_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v_fst_1798_);
lean_ctor_set(v___x_1801_, 0, v_fst_1794_);
v___x_1805_ = v___x_1801_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_fst_1794_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_fst_1798_);
v___x_1805_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
lean_object* v___x_1806_; lean_object* v_fst_1807_; lean_object* v_snd_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1838_; 
v___x_1806_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(v_original_1784_, v___x_1785_, v_a_1803_, v___x_1805_);
v_fst_1807_ = lean_ctor_get(v___x_1806_, 0);
v_snd_1808_ = lean_ctor_get(v___x_1806_, 1);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1806_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1810_ = v___x_1806_;
v_isShared_1811_ = v_isSharedCheck_1838_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_snd_1808_);
lean_inc(v_fst_1807_);
lean_dec(v___x_1806_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1838_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 1, v_snd_1799_);
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_fst_1807_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_snd_1799_);
v___x_1813_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1814_; lean_object* v_fst_1815_; lean_object* v_snd_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1836_; 
v___x_1814_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v_edited_1786_, v___x_1787_, v_a_1803_, v___x_1813_);
v_fst_1815_ = lean_ctor_get(v___x_1814_, 0);
v_snd_1816_ = lean_ctor_get(v___x_1814_, 1);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1818_ = v___x_1814_;
v_isShared_1819_ = v_isSharedCheck_1836_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_snd_1816_);
lean_inc(v_fst_1815_);
lean_dec(v___x_1814_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1836_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
uint8_t v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1823_; 
v___x_1820_ = 2;
v___x_1821_ = lean_box(v___x_1820_);
lean_inc(v_a_1803_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 1, v_a_1803_);
lean_ctor_set(v___x_1818_, 0, v___x_1821_);
v___x_1823_ = v___x_1818_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1821_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_a_1803_);
v___x_1823_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1829_; 
v___x_1824_ = lean_array_push(v_fst_1815_, v___x_1823_);
v___x_1825_ = lean_unsigned_to_nat(1u);
v___x_1826_ = lean_nat_add(v_snd_1808_, v___x_1825_);
lean_dec(v_snd_1808_);
v___x_1827_ = lean_nat_add(v_snd_1816_, v___x_1825_);
lean_dec(v_snd_1816_);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 1, v___x_1827_);
lean_ctor_set(v___x_1796_, 0, v___x_1826_);
v___x_1829_ = v___x_1796_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1826_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
lean_object* v___x_1830_; size_t v___x_1831_; size_t v___x_1832_; 
v___x_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1824_);
lean_ctor_set(v___x_1830_, 1, v___x_1829_);
v___x_1831_ = ((size_t)1ULL);
v___x_1832_ = lean_usize_add(v_i_1790_, v___x_1831_);
v_i_1790_ = v___x_1832_;
v_b_1791_ = v___x_1830_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14___boxed(lean_object* v_original_1842_, lean_object* v___x_1843_, lean_object* v_edited_1844_, lean_object* v___x_1845_, lean_object* v_as_1846_, lean_object* v_sz_1847_, lean_object* v_i_1848_, lean_object* v_b_1849_){
_start:
{
size_t v_sz_boxed_1850_; size_t v_i_boxed_1851_; lean_object* v_res_1852_; 
v_sz_boxed_1850_ = lean_unbox_usize(v_sz_1847_);
lean_dec(v_sz_1847_);
v_i_boxed_1851_ = lean_unbox_usize(v_i_1848_);
lean_dec(v_i_1848_);
v_res_1852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v_original_1842_, v___x_1843_, v_edited_1844_, v___x_1845_, v_as_1846_, v_sz_boxed_1850_, v_i_boxed_1851_, v_b_1849_);
lean_dec_ref(v_as_1846_);
lean_dec(v___x_1845_);
lean_dec_ref(v_edited_1844_);
lean_dec(v___x_1843_);
lean_dec_ref(v_original_1842_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(lean_object* v_edited_1853_, lean_object* v___x_1854_, lean_object* v_original_1855_, lean_object* v___x_1856_, lean_object* v_as_1857_, size_t v_sz_1858_, size_t v_i_1859_, lean_object* v_b_1860_){
_start:
{
uint8_t v___x_1861_; 
v___x_1861_ = lean_usize_dec_lt(v_i_1859_, v_sz_1858_);
if (v___x_1861_ == 0)
{
return v_b_1860_;
}
else
{
lean_object* v_snd_1862_; lean_object* v_fst_1863_; lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1910_; 
v_snd_1862_ = lean_ctor_get(v_b_1860_, 1);
v_fst_1863_ = lean_ctor_get(v_b_1860_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v_b_1860_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1865_ = v_b_1860_;
v_isShared_1866_ = v_isSharedCheck_1910_;
goto v_resetjp_1864_;
}
else
{
lean_inc(v_snd_1862_);
lean_inc(v_fst_1863_);
lean_dec(v_b_1860_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1910_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
lean_object* v_fst_1867_; lean_object* v_snd_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1909_; 
v_fst_1867_ = lean_ctor_get(v_snd_1862_, 0);
v_snd_1868_ = lean_ctor_get(v_snd_1862_, 1);
v_isSharedCheck_1909_ = !lean_is_exclusive(v_snd_1862_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1870_ = v_snd_1862_;
v_isShared_1871_ = v_isSharedCheck_1909_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_snd_1868_);
lean_inc(v_fst_1867_);
lean_dec(v_snd_1862_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1909_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v_a_1872_; lean_object* v___x_1874_; 
v_a_1872_ = lean_array_uget_borrowed(v_as_1857_, v_i_1859_);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 1, v_fst_1867_);
lean_ctor_set(v___x_1870_, 0, v_fst_1863_);
v___x_1874_ = v___x_1870_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_fst_1863_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_fst_1867_);
v___x_1874_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1875_; lean_object* v_fst_1876_; lean_object* v_snd_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1907_; 
v___x_1875_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(v_original_1855_, v___x_1856_, v_a_1872_, v___x_1874_);
v_fst_1876_ = lean_ctor_get(v___x_1875_, 0);
v_snd_1877_ = lean_ctor_get(v___x_1875_, 1);
v_isSharedCheck_1907_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1907_ == 0)
{
v___x_1879_ = v___x_1875_;
v_isShared_1880_ = v_isSharedCheck_1907_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_snd_1877_);
lean_inc(v_fst_1876_);
lean_dec(v___x_1875_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1907_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 1, v_snd_1868_);
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1906_; 
v_reuseFailAlloc_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_fst_1876_);
lean_ctor_set(v_reuseFailAlloc_1906_, 1, v_snd_1868_);
v___x_1882_ = v_reuseFailAlloc_1906_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
lean_object* v___x_1883_; lean_object* v_fst_1884_; lean_object* v_snd_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1905_; 
v___x_1883_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v_edited_1853_, v___x_1854_, v_a_1872_, v___x_1882_);
v_fst_1884_ = lean_ctor_get(v___x_1883_, 0);
v_snd_1885_ = lean_ctor_get(v___x_1883_, 1);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1887_ = v___x_1883_;
v_isShared_1888_ = v_isSharedCheck_1905_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_snd_1885_);
lean_inc(v_fst_1884_);
lean_dec(v___x_1883_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1905_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
uint8_t v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1892_; 
v___x_1889_ = 2;
v___x_1890_ = lean_box(v___x_1889_);
lean_inc(v_a_1872_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 1, v_a_1872_);
lean_ctor_set(v___x_1887_, 0, v___x_1890_);
v___x_1892_ = v___x_1887_;
goto v_reusejp_1891_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1890_);
lean_ctor_set(v_reuseFailAlloc_1904_, 1, v_a_1872_);
v___x_1892_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1891_;
}
v_reusejp_1891_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1898_; 
v___x_1893_ = lean_array_push(v_fst_1884_, v___x_1892_);
v___x_1894_ = lean_unsigned_to_nat(1u);
v___x_1895_ = lean_nat_add(v_snd_1877_, v___x_1894_);
lean_dec(v_snd_1877_);
v___x_1896_ = lean_nat_add(v_snd_1885_, v___x_1894_);
lean_dec(v_snd_1885_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 1, v___x_1896_);
lean_ctor_set(v___x_1865_, 0, v___x_1895_);
v___x_1898_ = v___x_1865_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1895_);
lean_ctor_set(v_reuseFailAlloc_1903_, 1, v___x_1896_);
v___x_1898_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
lean_object* v___x_1899_; size_t v___x_1900_; size_t v___x_1901_; lean_object* v___x_1902_; 
v___x_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___x_1893_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = ((size_t)1ULL);
v___x_1901_ = lean_usize_add(v_i_1859_, v___x_1900_);
v___x_1902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v_original_1855_, v___x_1856_, v_edited_1853_, v___x_1854_, v_as_1857_, v_sz_1858_, v___x_1901_, v___x_1899_);
return v___x_1902_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4___boxed(lean_object* v_edited_1911_, lean_object* v___x_1912_, lean_object* v_original_1913_, lean_object* v___x_1914_, lean_object* v_as_1915_, lean_object* v_sz_1916_, lean_object* v_i_1917_, lean_object* v_b_1918_){
_start:
{
size_t v_sz_boxed_1919_; size_t v_i_boxed_1920_; lean_object* v_res_1921_; 
v_sz_boxed_1919_ = lean_unbox_usize(v_sz_1916_);
lean_dec(v_sz_1916_);
v_i_boxed_1920_ = lean_unbox_usize(v_i_1917_);
lean_dec(v_i_1917_);
v_res_1921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v_edited_1911_, v___x_1912_, v_original_1913_, v___x_1914_, v_as_1915_, v_sz_boxed_1919_, v_i_boxed_1920_, v_b_1918_);
lean_dec_ref(v_as_1915_);
lean_dec(v___x_1914_);
lean_dec_ref(v_original_1913_);
lean_dec(v___x_1912_);
lean_dec_ref(v_edited_1911_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(lean_object* v_a_1922_, lean_object* v_b_1923_){
_start:
{
lean_object* v_array_1924_; lean_object* v_start_1925_; lean_object* v_stop_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1939_; 
v_array_1924_ = lean_ctor_get(v_a_1922_, 0);
v_start_1925_ = lean_ctor_get(v_a_1922_, 1);
v_stop_1926_ = lean_ctor_get(v_a_1922_, 2);
v_isSharedCheck_1939_ = !lean_is_exclusive(v_a_1922_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1928_ = v_a_1922_;
v_isShared_1929_ = v_isSharedCheck_1939_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_stop_1926_);
lean_inc(v_start_1925_);
lean_inc(v_array_1924_);
lean_dec(v_a_1922_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1939_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
uint8_t v___x_1930_; 
v___x_1930_ = lean_nat_dec_lt(v_start_1925_, v_stop_1926_);
if (v___x_1930_ == 0)
{
lean_del_object(v___x_1928_);
lean_dec(v_stop_1926_);
lean_dec(v_start_1925_);
lean_dec_ref(v_array_1924_);
return v_b_1923_;
}
else
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1931_ = lean_unsigned_to_nat(1u);
v___x_1932_ = lean_nat_add(v_start_1925_, v___x_1931_);
lean_inc_ref(v_array_1924_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 1, v___x_1932_);
v___x_1934_ = v___x_1928_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_array_1924_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v___x_1932_);
lean_ctor_set(v_reuseFailAlloc_1938_, 2, v_stop_1926_);
v___x_1934_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_array_fget(v_array_1924_, v_start_1925_);
lean_dec(v_start_1925_);
lean_dec_ref(v_array_1924_);
v___x_1936_ = lean_array_push(v_b_1923_, v___x_1935_);
v_a_1922_ = v___x_1934_;
v_b_1923_ = v___x_1936_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6(lean_object* v_left_1940_, lean_object* v_right_1941_, lean_object* v_i_1942_){
_start:
{
lean_object* v_start_1943_; lean_object* v_stop_1944_; lean_object* v___x_1945_; uint8_t v___x_1959_; 
v_start_1943_ = lean_ctor_get(v_left_1940_, 1);
v_stop_1944_ = lean_ctor_get(v_left_1940_, 2);
v___x_1945_ = lean_nat_sub(v_stop_1944_, v_start_1943_);
v___x_1959_ = lean_nat_dec_lt(v_i_1942_, v___x_1945_);
if (v___x_1959_ == 0)
{
goto v___jp_1946_;
}
else
{
lean_object* v_start_1960_; lean_object* v_stop_1961_; lean_object* v___x_1962_; uint8_t v___x_1963_; 
v_start_1960_ = lean_ctor_get(v_right_1941_, 1);
v_stop_1961_ = lean_ctor_get(v_right_1941_, 2);
v___x_1962_ = lean_nat_sub(v_stop_1961_, v_start_1960_);
v___x_1963_ = lean_nat_dec_lt(v_i_1942_, v___x_1962_);
if (v___x_1963_ == 0)
{
lean_dec(v___x_1962_);
goto v___jp_1946_;
}
else
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; 
v___x_1964_ = lean_nat_sub(v___x_1945_, v_i_1942_);
lean_dec(v___x_1945_);
v___x_1965_ = lean_unsigned_to_nat(1u);
v___x_1966_ = lean_nat_sub(v___x_1964_, v___x_1965_);
v___x_1967_ = l_Subarray_get___redArg(v_left_1940_, v___x_1966_);
lean_dec(v___x_1966_);
v___x_1968_ = lean_nat_sub(v___x_1962_, v_i_1942_);
lean_dec(v___x_1962_);
v___x_1969_ = lean_nat_sub(v___x_1968_, v___x_1965_);
v___x_1970_ = l_Subarray_get___redArg(v_right_1941_, v___x_1969_);
lean_dec(v___x_1969_);
v___x_1971_ = lean_string_dec_eq(v___x_1967_, v___x_1970_);
lean_dec(v___x_1970_);
lean_dec(v___x_1967_);
if (v___x_1971_ == 0)
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
lean_dec(v_i_1942_);
lean_inc_ref(v_left_1940_);
v___x_1972_ = l_Subarray_take___redArg(v_left_1940_, v___x_1964_);
v___x_1973_ = l_Subarray_take___redArg(v_right_1941_, v___x_1968_);
lean_dec(v___x_1968_);
v___x_1974_ = l_Subarray_drop___redArg(v_left_1940_, v___x_1964_);
lean_dec(v___x_1964_);
v___x_1975_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_1976_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v___x_1974_, v___x_1975_);
v___x_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1973_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1972_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
return v___x_1978_;
}
else
{
lean_object* v___x_1979_; 
lean_dec(v___x_1968_);
lean_dec(v___x_1964_);
v___x_1979_ = lean_nat_add(v_i_1942_, v___x_1965_);
lean_dec(v_i_1942_);
v_i_1942_ = v___x_1979_;
goto _start;
}
}
}
v___jp_1946_:
{
lean_object* v_start_1947_; lean_object* v_stop_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v_start_1947_ = lean_ctor_get(v_right_1941_, 1);
v_stop_1948_ = lean_ctor_get(v_right_1941_, 2);
v___x_1949_ = lean_nat_sub(v___x_1945_, v_i_1942_);
lean_dec(v___x_1945_);
lean_inc_ref(v_left_1940_);
v___x_1950_ = l_Subarray_take___redArg(v_left_1940_, v___x_1949_);
v___x_1951_ = lean_nat_sub(v_stop_1948_, v_start_1947_);
v___x_1952_ = lean_nat_sub(v___x_1951_, v_i_1942_);
lean_dec(v_i_1942_);
lean_dec(v___x_1951_);
v___x_1953_ = l_Subarray_take___redArg(v_right_1941_, v___x_1952_);
lean_dec(v___x_1952_);
v___x_1954_ = l_Subarray_drop___redArg(v_left_1940_, v___x_1949_);
lean_dec(v___x_1949_);
v___x_1955_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_1956_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v___x_1954_, v___x_1955_);
v___x_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1953_);
lean_ctor_set(v___x_1957_, 1, v___x_1956_);
v___x_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1950_);
lean_ctor_set(v___x_1958_, 1, v___x_1957_);
return v___x_1958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3(lean_object* v_left_1981_, lean_object* v_right_1982_){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1983_ = lean_unsigned_to_nat(0u);
v___x_1984_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6(v_left_1981_, v_right_1982_, v___x_1983_);
return v___x_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2_spec__4(lean_object* v_left_1985_, lean_object* v_right_1986_, lean_object* v_pref_1987_){
_start:
{
lean_object* v_start_1988_; lean_object* v_stop_1989_; lean_object* v_i_1990_; lean_object* v___x_1996_; uint8_t v___x_1997_; 
v_start_1988_ = lean_ctor_get(v_left_1985_, 1);
v_stop_1989_ = lean_ctor_get(v_left_1985_, 2);
v_i_1990_ = lean_array_get_size(v_pref_1987_);
v___x_1996_ = lean_nat_sub(v_stop_1989_, v_start_1988_);
v___x_1997_ = lean_nat_dec_lt(v_i_1990_, v___x_1996_);
lean_dec(v___x_1996_);
if (v___x_1997_ == 0)
{
goto v___jp_1991_;
}
else
{
lean_object* v_start_1998_; lean_object* v_stop_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v_start_1998_ = lean_ctor_get(v_right_1986_, 1);
v_stop_1999_ = lean_ctor_get(v_right_1986_, 2);
v___x_2000_ = lean_nat_sub(v_stop_1999_, v_start_1998_);
v___x_2001_ = lean_nat_dec_lt(v_i_1990_, v___x_2000_);
lean_dec(v___x_2000_);
if (v___x_2001_ == 0)
{
goto v___jp_1991_;
}
else
{
lean_object* v___x_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; 
v___x_2002_ = l_Subarray_get___redArg(v_left_1985_, v_i_1990_);
v___x_2003_ = l_Subarray_get___redArg(v_right_1986_, v_i_1990_);
v___x_2004_ = lean_string_dec_eq(v___x_2002_, v___x_2003_);
lean_dec(v___x_2003_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
lean_dec(v___x_2002_);
v___x_2005_ = l_Subarray_drop___redArg(v_left_1985_, v_i_1990_);
v___x_2006_ = l_Subarray_drop___redArg(v_right_1986_, v_i_1990_);
v___x_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2005_);
lean_ctor_set(v___x_2007_, 1, v___x_2006_);
v___x_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2008_, 0, v_pref_1987_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
return v___x_2008_;
}
else
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_array_push(v_pref_1987_, v___x_2002_);
v_pref_1987_ = v___x_2009_;
goto _start;
}
}
}
v___jp_1991_:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1992_ = l_Subarray_drop___redArg(v_left_1985_, v_i_1990_);
v___x_1993_ = l_Subarray_drop___redArg(v_right_1986_, v_i_1990_);
v___x_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1992_);
lean_ctor_set(v___x_1994_, 1, v___x_1993_);
v___x_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1995_, 0, v_pref_1987_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
return v___x_1995_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2(lean_object* v_left_2011_, lean_object* v_right_2012_){
_start:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
v___x_2013_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2014_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2_spec__4(v_left_2011_, v_right_2012_, v___x_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(lean_object* v_as_x27_2015_, lean_object* v_b_2016_){
_start:
{
if (lean_obj_tag(v_as_x27_2015_) == 0)
{
return v_b_2016_;
}
else
{
lean_object* v_head_2017_; lean_object* v_snd_2018_; lean_object* v_leftIndex_2019_; 
v_head_2017_ = lean_ctor_get(v_as_x27_2015_, 0);
v_snd_2018_ = lean_ctor_get(v_head_2017_, 1);
v_leftIndex_2019_ = lean_ctor_get(v_snd_2018_, 1);
if (lean_obj_tag(v_leftIndex_2019_) == 1)
{
lean_object* v_rightIndex_2020_; 
v_rightIndex_2020_ = lean_ctor_get(v_snd_2018_, 3);
if (lean_obj_tag(v_rightIndex_2020_) == 1)
{
if (lean_obj_tag(v_b_2016_) == 0)
{
lean_object* v_tail_2021_; lean_object* v_fst_2022_; lean_object* v_leftCount_2023_; lean_object* v_rightCount_2024_; lean_object* v_val_2025_; lean_object* v_val_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v_tail_2021_ = lean_ctor_get(v_as_x27_2015_, 1);
v_fst_2022_ = lean_ctor_get(v_head_2017_, 0);
v_leftCount_2023_ = lean_ctor_get(v_snd_2018_, 0);
v_rightCount_2024_ = lean_ctor_get(v_snd_2018_, 2);
v_val_2025_ = lean_ctor_get(v_leftIndex_2019_, 0);
v_val_2026_ = lean_ctor_get(v_rightIndex_2020_, 0);
v___x_2027_ = lean_nat_add(v_leftCount_2023_, v_rightCount_2024_);
lean_inc(v_val_2026_);
lean_inc(v_val_2025_);
v___x_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2028_, 0, v_val_2025_);
lean_ctor_set(v___x_2028_, 1, v_val_2026_);
lean_inc(v_fst_2022_);
v___x_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2029_, 0, v_fst_2022_);
lean_ctor_set(v___x_2029_, 1, v___x_2028_);
v___x_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2027_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
v_as_x27_2015_ = v_tail_2021_;
v_b_2016_ = v___x_2031_;
goto _start;
}
else
{
lean_object* v_val_2033_; lean_object* v_tail_2034_; lean_object* v_fst_2035_; lean_object* v_leftCount_2036_; lean_object* v_rightCount_2037_; lean_object* v_val_2038_; lean_object* v_val_2039_; lean_object* v_fst_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2061_; 
v_val_2033_ = lean_ctor_get(v_b_2016_, 0);
lean_inc(v_val_2033_);
v_tail_2034_ = lean_ctor_get(v_as_x27_2015_, 1);
v_fst_2035_ = lean_ctor_get(v_head_2017_, 0);
v_leftCount_2036_ = lean_ctor_get(v_snd_2018_, 0);
v_rightCount_2037_ = lean_ctor_get(v_snd_2018_, 2);
v_val_2038_ = lean_ctor_get(v_leftIndex_2019_, 0);
v_val_2039_ = lean_ctor_get(v_rightIndex_2020_, 0);
v_fst_2040_ = lean_ctor_get(v_val_2033_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_val_2033_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; 
v_unused_2062_ = lean_ctor_get(v_val_2033_, 1);
lean_dec(v_unused_2062_);
v___x_2042_ = v_val_2033_;
v_isShared_2043_ = v_isSharedCheck_2061_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_fst_2040_);
lean_dec(v_val_2033_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2061_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; uint8_t v___x_2045_; 
v___x_2044_ = lean_nat_add(v_leftCount_2036_, v_rightCount_2037_);
v___x_2045_ = lean_nat_dec_lt(v___x_2044_, v_fst_2040_);
lean_dec(v_fst_2040_);
if (v___x_2045_ == 0)
{
lean_dec(v___x_2044_);
lean_del_object(v___x_2042_);
v_as_x27_2015_ = v_tail_2034_;
goto _start;
}
else
{
lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2059_; 
v_isSharedCheck_2059_ = !lean_is_exclusive(v_b_2016_);
if (v_isSharedCheck_2059_ == 0)
{
lean_object* v_unused_2060_; 
v_unused_2060_ = lean_ctor_get(v_b_2016_, 0);
lean_dec(v_unused_2060_);
v___x_2048_ = v_b_2016_;
v_isShared_2049_ = v_isSharedCheck_2059_;
goto v_resetjp_2047_;
}
else
{
lean_dec(v_b_2016_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2059_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
lean_inc(v_val_2039_);
lean_inc(v_val_2038_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 1, v_val_2039_);
lean_ctor_set(v___x_2042_, 0, v_val_2038_);
v___x_2051_ = v___x_2042_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_val_2038_);
lean_ctor_set(v_reuseFailAlloc_2058_, 1, v_val_2039_);
v___x_2051_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2055_; 
lean_inc(v_fst_2035_);
v___x_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2052_, 0, v_fst_2035_);
lean_ctor_set(v___x_2052_, 1, v___x_2051_);
v___x_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2053_, 0, v___x_2044_);
lean_ctor_set(v___x_2053_, 1, v___x_2052_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 0, v___x_2053_);
v___x_2055_ = v___x_2048_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
v_as_x27_2015_ = v_tail_2034_;
v_b_2016_ = v___x_2055_;
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
lean_object* v_tail_2063_; 
v_tail_2063_ = lean_ctor_get(v_as_x27_2015_, 1);
v_as_x27_2015_ = v_tail_2063_;
goto _start;
}
}
else
{
lean_object* v_tail_2065_; 
v_tail_2065_ = lean_ctor_get(v_as_x27_2015_, 1);
v_as_x27_2015_ = v_tail_2065_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2067_, lean_object* v_b_2068_){
_start:
{
lean_object* v_res_2069_; 
v_res_2069_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(v_as_x27_2067_, v_b_2068_);
lean_dec(v_as_x27_2067_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(lean_object* v_a_2070_, lean_object* v_b_2071_, lean_object* v_x_2072_){
_start:
{
if (lean_obj_tag(v_x_2072_) == 0)
{
lean_dec(v_b_2071_);
lean_dec_ref(v_a_2070_);
return v_x_2072_;
}
else
{
lean_object* v_key_2073_; lean_object* v_value_2074_; lean_object* v_tail_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2087_; 
v_key_2073_ = lean_ctor_get(v_x_2072_, 0);
v_value_2074_ = lean_ctor_get(v_x_2072_, 1);
v_tail_2075_ = lean_ctor_get(v_x_2072_, 2);
v_isSharedCheck_2087_ = !lean_is_exclusive(v_x_2072_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2077_ = v_x_2072_;
v_isShared_2078_ = v_isSharedCheck_2087_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_tail_2075_);
lean_inc(v_value_2074_);
lean_inc(v_key_2073_);
lean_dec(v_x_2072_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2087_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
uint8_t v___x_2079_; 
v___x_2079_ = lean_string_dec_eq(v_key_2073_, v_a_2070_);
if (v___x_2079_ == 0)
{
lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2080_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(v_a_2070_, v_b_2071_, v_tail_2075_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 2, v___x_2080_);
v___x_2082_ = v___x_2077_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_key_2073_);
lean_ctor_set(v_reuseFailAlloc_2083_, 1, v_value_2074_);
lean_ctor_set(v_reuseFailAlloc_2083_, 2, v___x_2080_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
else
{
lean_object* v___x_2085_; 
lean_dec(v_value_2074_);
lean_dec(v_key_2073_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 1, v_b_2071_);
lean_ctor_set(v___x_2077_, 0, v_a_2070_);
v___x_2085_ = v___x_2077_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2070_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v_b_2071_);
lean_ctor_set(v_reuseFailAlloc_2086_, 2, v_tail_2075_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(lean_object* v_a_2088_, lean_object* v_x_2089_){
_start:
{
if (lean_obj_tag(v_x_2089_) == 0)
{
uint8_t v___x_2090_; 
v___x_2090_ = 0;
return v___x_2090_;
}
else
{
lean_object* v_key_2091_; lean_object* v_tail_2092_; uint8_t v___x_2093_; 
v_key_2091_ = lean_ctor_get(v_x_2089_, 0);
v_tail_2092_ = lean_ctor_get(v_x_2089_, 2);
v___x_2093_ = lean_string_dec_eq(v_key_2091_, v_a_2088_);
if (v___x_2093_ == 0)
{
v_x_2089_ = v_tail_2092_;
goto _start;
}
else
{
return v___x_2093_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg___boxed(lean_object* v_a_2095_, lean_object* v_x_2096_){
_start:
{
uint8_t v_res_2097_; lean_object* v_r_2098_; 
v_res_2097_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(v_a_2095_, v_x_2096_);
lean_dec(v_x_2096_);
lean_dec_ref(v_a_2095_);
v_r_2098_ = lean_box(v_res_2097_);
return v_r_2098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29___redArg(lean_object* v_x_2099_, lean_object* v_x_2100_){
_start:
{
if (lean_obj_tag(v_x_2100_) == 0)
{
return v_x_2099_;
}
else
{
lean_object* v_key_2101_; lean_object* v_value_2102_; lean_object* v_tail_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2126_; 
v_key_2101_ = lean_ctor_get(v_x_2100_, 0);
v_value_2102_ = lean_ctor_get(v_x_2100_, 1);
v_tail_2103_ = lean_ctor_get(v_x_2100_, 2);
v_isSharedCheck_2126_ = !lean_is_exclusive(v_x_2100_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2105_ = v_x_2100_;
v_isShared_2106_ = v_isSharedCheck_2126_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_tail_2103_);
lean_inc(v_value_2102_);
lean_inc(v_key_2101_);
lean_dec(v_x_2100_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2126_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2107_; uint64_t v___x_2108_; uint64_t v___x_2109_; uint64_t v___x_2110_; uint64_t v_fold_2111_; uint64_t v___x_2112_; uint64_t v___x_2113_; uint64_t v___x_2114_; size_t v___x_2115_; size_t v___x_2116_; size_t v___x_2117_; size_t v___x_2118_; size_t v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2122_; 
v___x_2107_ = lean_array_get_size(v_x_2099_);
v___x_2108_ = lean_string_hash(v_key_2101_);
v___x_2109_ = 32ULL;
v___x_2110_ = lean_uint64_shift_right(v___x_2108_, v___x_2109_);
v_fold_2111_ = lean_uint64_xor(v___x_2108_, v___x_2110_);
v___x_2112_ = 16ULL;
v___x_2113_ = lean_uint64_shift_right(v_fold_2111_, v___x_2112_);
v___x_2114_ = lean_uint64_xor(v_fold_2111_, v___x_2113_);
v___x_2115_ = lean_uint64_to_usize(v___x_2114_);
v___x_2116_ = lean_usize_of_nat(v___x_2107_);
v___x_2117_ = ((size_t)1ULL);
v___x_2118_ = lean_usize_sub(v___x_2116_, v___x_2117_);
v___x_2119_ = lean_usize_land(v___x_2115_, v___x_2118_);
v___x_2120_ = lean_array_uget_borrowed(v_x_2099_, v___x_2119_);
lean_inc(v___x_2120_);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 2, v___x_2120_);
v___x_2122_ = v___x_2105_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_key_2101_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v_value_2102_);
lean_ctor_set(v_reuseFailAlloc_2125_, 2, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; 
v___x_2123_ = lean_array_uset(v_x_2099_, v___x_2119_, v___x_2122_);
v_x_2099_ = v___x_2123_;
v_x_2100_ = v_tail_2103_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28___redArg(lean_object* v_i_2127_, lean_object* v_source_2128_, lean_object* v_target_2129_){
_start:
{
lean_object* v___x_2130_; uint8_t v___x_2131_; 
v___x_2130_ = lean_array_get_size(v_source_2128_);
v___x_2131_ = lean_nat_dec_lt(v_i_2127_, v___x_2130_);
if (v___x_2131_ == 0)
{
lean_dec_ref(v_source_2128_);
lean_dec(v_i_2127_);
return v_target_2129_;
}
else
{
lean_object* v_es_2132_; lean_object* v___x_2133_; lean_object* v_source_2134_; lean_object* v_target_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v_es_2132_ = lean_array_fget(v_source_2128_, v_i_2127_);
v___x_2133_ = lean_box(0);
v_source_2134_ = lean_array_fset(v_source_2128_, v_i_2127_, v___x_2133_);
v_target_2135_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29___redArg(v_target_2129_, v_es_2132_);
v___x_2136_ = lean_unsigned_to_nat(1u);
v___x_2137_ = lean_nat_add(v_i_2127_, v___x_2136_);
lean_dec(v_i_2127_);
v_i_2127_ = v___x_2137_;
v_source_2128_ = v_source_2134_;
v_target_2129_ = v_target_2135_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23___redArg(lean_object* v_data_2139_){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v_nbuckets_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2140_ = lean_array_get_size(v_data_2139_);
v___x_2141_ = lean_unsigned_to_nat(2u);
v_nbuckets_2142_ = lean_nat_mul(v___x_2140_, v___x_2141_);
v___x_2143_ = lean_unsigned_to_nat(0u);
v___x_2144_ = lean_box(0);
v___x_2145_ = lean_mk_array(v_nbuckets_2142_, v___x_2144_);
v___x_2146_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28___redArg(v___x_2143_, v_data_2139_, v___x_2145_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(lean_object* v_m_2147_, lean_object* v_a_2148_, lean_object* v_b_2149_){
_start:
{
lean_object* v_size_2150_; lean_object* v_buckets_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2194_; 
v_size_2150_ = lean_ctor_get(v_m_2147_, 0);
v_buckets_2151_ = lean_ctor_get(v_m_2147_, 1);
v_isSharedCheck_2194_ = !lean_is_exclusive(v_m_2147_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2153_ = v_m_2147_;
v_isShared_2154_ = v_isSharedCheck_2194_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_buckets_2151_);
lean_inc(v_size_2150_);
lean_dec(v_m_2147_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2194_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2155_; uint64_t v___x_2156_; uint64_t v___x_2157_; uint64_t v___x_2158_; uint64_t v_fold_2159_; uint64_t v___x_2160_; uint64_t v___x_2161_; uint64_t v___x_2162_; size_t v___x_2163_; size_t v___x_2164_; size_t v___x_2165_; size_t v___x_2166_; size_t v___x_2167_; lean_object* v_bkt_2168_; uint8_t v___x_2169_; 
v___x_2155_ = lean_array_get_size(v_buckets_2151_);
v___x_2156_ = lean_string_hash(v_a_2148_);
v___x_2157_ = 32ULL;
v___x_2158_ = lean_uint64_shift_right(v___x_2156_, v___x_2157_);
v_fold_2159_ = lean_uint64_xor(v___x_2156_, v___x_2158_);
v___x_2160_ = 16ULL;
v___x_2161_ = lean_uint64_shift_right(v_fold_2159_, v___x_2160_);
v___x_2162_ = lean_uint64_xor(v_fold_2159_, v___x_2161_);
v___x_2163_ = lean_uint64_to_usize(v___x_2162_);
v___x_2164_ = lean_usize_of_nat(v___x_2155_);
v___x_2165_ = ((size_t)1ULL);
v___x_2166_ = lean_usize_sub(v___x_2164_, v___x_2165_);
v___x_2167_ = lean_usize_land(v___x_2163_, v___x_2166_);
v_bkt_2168_ = lean_array_uget_borrowed(v_buckets_2151_, v___x_2167_);
v___x_2169_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(v_a_2148_, v_bkt_2168_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; lean_object* v_size_x27_2171_; lean_object* v___x_2172_; lean_object* v_buckets_x27_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; uint8_t v___x_2179_; 
v___x_2170_ = lean_unsigned_to_nat(1u);
v_size_x27_2171_ = lean_nat_add(v_size_2150_, v___x_2170_);
lean_dec(v_size_2150_);
lean_inc(v_bkt_2168_);
v___x_2172_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2172_, 0, v_a_2148_);
lean_ctor_set(v___x_2172_, 1, v_b_2149_);
lean_ctor_set(v___x_2172_, 2, v_bkt_2168_);
v_buckets_x27_2173_ = lean_array_uset(v_buckets_2151_, v___x_2167_, v___x_2172_);
v___x_2174_ = lean_unsigned_to_nat(4u);
v___x_2175_ = lean_nat_mul(v_size_x27_2171_, v___x_2174_);
v___x_2176_ = lean_unsigned_to_nat(3u);
v___x_2177_ = lean_nat_div(v___x_2175_, v___x_2176_);
lean_dec(v___x_2175_);
v___x_2178_ = lean_array_get_size(v_buckets_x27_2173_);
v___x_2179_ = lean_nat_dec_le(v___x_2177_, v___x_2178_);
lean_dec(v___x_2177_);
if (v___x_2179_ == 0)
{
lean_object* v_val_2180_; lean_object* v___x_2182_; 
v_val_2180_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23___redArg(v_buckets_x27_2173_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 1, v_val_2180_);
lean_ctor_set(v___x_2153_, 0, v_size_x27_2171_);
v___x_2182_ = v___x_2153_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_size_x27_2171_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_val_2180_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
else
{
lean_object* v___x_2185_; 
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 1, v_buckets_x27_2173_);
lean_ctor_set(v___x_2153_, 0, v_size_x27_2171_);
v___x_2185_ = v___x_2153_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_size_x27_2171_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_buckets_x27_2173_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
else
{
lean_object* v___x_2187_; lean_object* v_buckets_x27_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
lean_inc(v_bkt_2168_);
v___x_2187_ = lean_box(0);
v_buckets_x27_2188_ = lean_array_uset(v_buckets_2151_, v___x_2167_, v___x_2187_);
v___x_2189_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(v_a_2148_, v_b_2149_, v_bkt_2168_);
v___x_2190_ = lean_array_uset(v_buckets_x27_2188_, v___x_2167_, v___x_2189_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 1, v___x_2190_);
v___x_2192_ = v___x_2153_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_size_2150_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v___x_2190_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(lean_object* v_a_2195_, lean_object* v_x_2196_){
_start:
{
if (lean_obj_tag(v_x_2196_) == 0)
{
lean_object* v___x_2197_; 
v___x_2197_ = lean_box(0);
return v___x_2197_;
}
else
{
lean_object* v_key_2198_; lean_object* v_value_2199_; lean_object* v_tail_2200_; uint8_t v___x_2201_; 
v_key_2198_ = lean_ctor_get(v_x_2196_, 0);
v_value_2199_ = lean_ctor_get(v_x_2196_, 1);
v_tail_2200_ = lean_ctor_get(v_x_2196_, 2);
v___x_2201_ = lean_string_dec_eq(v_key_2198_, v_a_2195_);
if (v___x_2201_ == 0)
{
v_x_2196_ = v_tail_2200_;
goto _start;
}
else
{
lean_object* v___x_2203_; 
lean_inc(v_value_2199_);
v___x_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2203_, 0, v_value_2199_);
return v___x_2203_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg___boxed(lean_object* v_a_2204_, lean_object* v_x_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(v_a_2204_, v_x_2205_);
lean_dec(v_x_2205_);
lean_dec_ref(v_a_2204_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(lean_object* v_m_2207_, lean_object* v_a_2208_){
_start:
{
lean_object* v_buckets_2209_; lean_object* v___x_2210_; uint64_t v___x_2211_; uint64_t v___x_2212_; uint64_t v___x_2213_; uint64_t v_fold_2214_; uint64_t v___x_2215_; uint64_t v___x_2216_; uint64_t v___x_2217_; size_t v___x_2218_; size_t v___x_2219_; size_t v___x_2220_; size_t v___x_2221_; size_t v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v_buckets_2209_ = lean_ctor_get(v_m_2207_, 1);
v___x_2210_ = lean_array_get_size(v_buckets_2209_);
v___x_2211_ = lean_string_hash(v_a_2208_);
v___x_2212_ = 32ULL;
v___x_2213_ = lean_uint64_shift_right(v___x_2211_, v___x_2212_);
v_fold_2214_ = lean_uint64_xor(v___x_2211_, v___x_2213_);
v___x_2215_ = 16ULL;
v___x_2216_ = lean_uint64_shift_right(v_fold_2214_, v___x_2215_);
v___x_2217_ = lean_uint64_xor(v_fold_2214_, v___x_2216_);
v___x_2218_ = lean_uint64_to_usize(v___x_2217_);
v___x_2219_ = lean_usize_of_nat(v___x_2210_);
v___x_2220_ = ((size_t)1ULL);
v___x_2221_ = lean_usize_sub(v___x_2219_, v___x_2220_);
v___x_2222_ = lean_usize_land(v___x_2218_, v___x_2221_);
v___x_2223_ = lean_array_uget_borrowed(v_buckets_2209_, v___x_2222_);
v___x_2224_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(v_a_2208_, v___x_2223_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg___boxed(lean_object* v_m_2225_, lean_object* v_a_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_m_2225_, v_a_2226_);
lean_dec_ref(v_a_2226_);
lean_dec_ref(v_m_2225_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(lean_object* v_histogram_2228_, lean_object* v_index_2229_, lean_object* v_val_2230_){
_start:
{
lean_object* v___x_2231_; 
v___x_2231_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_histogram_2228_, v_val_2230_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2232_ = lean_unsigned_to_nat(1u);
v___x_2233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2233_, 0, v_index_2229_);
v___x_2234_ = lean_unsigned_to_nat(0u);
v___x_2235_ = lean_box(0);
v___x_2236_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2236_, 0, v___x_2232_);
lean_ctor_set(v___x_2236_, 1, v___x_2233_);
lean_ctor_set(v___x_2236_, 2, v___x_2234_);
lean_ctor_set(v___x_2236_, 3, v___x_2235_);
v___x_2237_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2228_, v_val_2230_, v___x_2236_);
return v___x_2237_;
}
else
{
lean_object* v_val_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2259_; 
v_val_2238_ = lean_ctor_get(v___x_2231_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2231_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2240_ = v___x_2231_;
v_isShared_2241_ = v_isSharedCheck_2259_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_val_2238_);
lean_dec(v___x_2231_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2259_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v_leftCount_2242_; lean_object* v_rightCount_2243_; lean_object* v_rightIndex_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2257_; 
v_leftCount_2242_ = lean_ctor_get(v_val_2238_, 0);
v_rightCount_2243_ = lean_ctor_get(v_val_2238_, 2);
v_rightIndex_2244_ = lean_ctor_get(v_val_2238_, 3);
v_isSharedCheck_2257_ = !lean_is_exclusive(v_val_2238_);
if (v_isSharedCheck_2257_ == 0)
{
lean_object* v_unused_2258_; 
v_unused_2258_ = lean_ctor_get(v_val_2238_, 1);
lean_dec(v_unused_2258_);
v___x_2246_ = v_val_2238_;
v_isShared_2247_ = v_isSharedCheck_2257_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_rightIndex_2244_);
lean_inc(v_rightCount_2243_);
lean_inc(v_leftCount_2242_);
lean_dec(v_val_2238_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2257_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2251_; 
v___x_2248_ = lean_unsigned_to_nat(1u);
v___x_2249_ = lean_nat_add(v_leftCount_2242_, v___x_2248_);
lean_dec(v_leftCount_2242_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v_index_2229_);
v___x_2251_ = v___x_2240_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_index_2229_);
v___x_2251_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v___x_2253_; 
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 1, v___x_2251_);
lean_ctor_set(v___x_2246_, 0, v___x_2249_);
v___x_2253_ = v___x_2246_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2249_);
lean_ctor_set(v_reuseFailAlloc_2255_, 1, v___x_2251_);
lean_ctor_set(v_reuseFailAlloc_2255_, 2, v_rightCount_2243_);
lean_ctor_set(v_reuseFailAlloc_2255_, 3, v_rightIndex_2244_);
v___x_2253_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
lean_object* v___x_2254_; 
v___x_2254_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2228_, v_val_2230_, v___x_2253_);
return v___x_2254_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(lean_object* v_upperBound_2260_, lean_object* v_fst_2261_, lean_object* v___x_2262_, lean_object* v_fst_2263_, lean_object* v_a_2264_, lean_object* v_b_2265_){
_start:
{
uint8_t v___x_2266_; 
v___x_2266_ = lean_nat_dec_lt(v_a_2264_, v_upperBound_2260_);
if (v___x_2266_ == 0)
{
lean_dec(v_a_2264_);
return v_b_2265_;
}
else
{
lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2267_ = l_Subarray_get___redArg(v_fst_2263_, v_a_2264_);
lean_inc(v_a_2264_);
v___x_2268_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(v_b_2265_, v_a_2264_, v___x_2267_);
v___x_2269_ = lean_unsigned_to_nat(1u);
v___x_2270_ = lean_nat_add(v_a_2264_, v___x_2269_);
lean_dec(v_a_2264_);
v_a_2264_ = v___x_2270_;
v_b_2265_ = v___x_2268_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_upperBound_2272_, lean_object* v_fst_2273_, lean_object* v___x_2274_, lean_object* v_fst_2275_, lean_object* v_a_2276_, lean_object* v_b_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(v_upperBound_2272_, v_fst_2273_, v___x_2274_, v_fst_2275_, v_a_2276_, v_b_2277_);
lean_dec_ref(v_fst_2275_);
lean_dec(v___x_2274_);
lean_dec_ref(v_fst_2273_);
lean_dec(v_upperBound_2272_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(lean_object* v_x_2279_, lean_object* v_x_2280_){
_start:
{
if (lean_obj_tag(v_x_2280_) == 0)
{
lean_inc(v_x_2279_);
return v_x_2279_;
}
else
{
lean_object* v_key_2281_; lean_object* v_value_2282_; lean_object* v_tail_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v_key_2281_ = lean_ctor_get(v_x_2280_, 0);
v_value_2282_ = lean_ctor_get(v_x_2280_, 1);
v_tail_2283_ = lean_ctor_get(v_x_2280_, 2);
v___x_2284_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(v_x_2279_, v_tail_2283_);
lean_inc(v_value_2282_);
lean_inc(v_key_2281_);
v___x_2285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2285_, 0, v_key_2281_);
lean_ctor_set(v___x_2285_, 1, v_value_2282_);
v___x_2286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
lean_ctor_set(v___x_2286_, 1, v___x_2284_);
return v___x_2286_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5___boxed(lean_object* v_x_2287_, lean_object* v_x_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(v_x_2287_, v_x_2288_);
lean_dec(v_x_2288_);
lean_dec(v_x_2287_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(lean_object* v_as_2290_, size_t v_i_2291_, size_t v_stop_2292_, lean_object* v_b_2293_){
_start:
{
uint8_t v___x_2294_; 
v___x_2294_ = lean_usize_dec_eq(v_i_2291_, v_stop_2292_);
if (v___x_2294_ == 0)
{
size_t v___x_2295_; size_t v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; 
v___x_2295_ = ((size_t)1ULL);
v___x_2296_ = lean_usize_sub(v_i_2291_, v___x_2295_);
v___x_2297_ = lean_array_uget_borrowed(v_as_2290_, v___x_2296_);
v___x_2298_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(v_b_2293_, v___x_2297_);
lean_dec(v_b_2293_);
v_i_2291_ = v___x_2296_;
v_b_2293_ = v___x_2298_;
goto _start;
}
else
{
return v_b_2293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6___boxed(lean_object* v_as_2300_, lean_object* v_i_2301_, lean_object* v_stop_2302_, lean_object* v_b_2303_){
_start:
{
size_t v_i_boxed_2304_; size_t v_stop_boxed_2305_; lean_object* v_res_2306_; 
v_i_boxed_2304_ = lean_unbox_usize(v_i_2301_);
lean_dec(v_i_2301_);
v_stop_boxed_2305_ = lean_unbox_usize(v_stop_2302_);
lean_dec(v_stop_2302_);
v_res_2306_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(v_as_2300_, v_i_boxed_2304_, v_stop_boxed_2305_, v_b_2303_);
lean_dec_ref(v_as_2300_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(lean_object* v_histogram_2307_, lean_object* v_index_2308_, lean_object* v_val_2309_){
_start:
{
lean_object* v___x_2310_; 
v___x_2310_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_histogram_2307_, v_val_2309_);
if (lean_obj_tag(v___x_2310_) == 0)
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___x_2311_ = lean_unsigned_to_nat(0u);
v___x_2312_ = lean_box(0);
v___x_2313_ = lean_unsigned_to_nat(1u);
v___x_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2314_, 0, v_index_2308_);
v___x_2315_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2311_);
lean_ctor_set(v___x_2315_, 1, v___x_2312_);
lean_ctor_set(v___x_2315_, 2, v___x_2313_);
lean_ctor_set(v___x_2315_, 3, v___x_2314_);
v___x_2316_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2307_, v_val_2309_, v___x_2315_);
return v___x_2316_;
}
else
{
lean_object* v_val_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2338_; 
v_val_2317_ = lean_ctor_get(v___x_2310_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2319_ = v___x_2310_;
v_isShared_2320_ = v_isSharedCheck_2338_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_val_2317_);
lean_dec(v___x_2310_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2338_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v_leftCount_2321_; lean_object* v_leftIndex_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2335_; 
v_leftCount_2321_ = lean_ctor_get(v_val_2317_, 0);
v_leftIndex_2322_ = lean_ctor_get(v_val_2317_, 1);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_val_2317_);
if (v_isSharedCheck_2335_ == 0)
{
lean_object* v_unused_2336_; lean_object* v_unused_2337_; 
v_unused_2336_ = lean_ctor_get(v_val_2317_, 3);
lean_dec(v_unused_2336_);
v_unused_2337_ = lean_ctor_get(v_val_2317_, 2);
lean_dec(v_unused_2337_);
v___x_2324_ = v_val_2317_;
v_isShared_2325_ = v_isSharedCheck_2335_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_leftIndex_2322_);
lean_inc(v_leftCount_2321_);
lean_dec(v_val_2317_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2335_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2329_; 
v___x_2326_ = lean_unsigned_to_nat(1u);
v___x_2327_ = lean_nat_add(v_leftCount_2321_, v___x_2326_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 0, v_index_2308_);
v___x_2329_ = v___x_2319_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_index_2308_);
v___x_2329_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
lean_object* v___x_2331_; 
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 3, v___x_2329_);
lean_ctor_set(v___x_2324_, 2, v___x_2327_);
v___x_2331_ = v___x_2324_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_leftCount_2321_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_leftIndex_2322_);
lean_ctor_set(v_reuseFailAlloc_2333_, 2, v___x_2327_);
lean_ctor_set(v_reuseFailAlloc_2333_, 3, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2307_, v_val_2309_, v___x_2331_);
return v___x_2332_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(lean_object* v_upperBound_2339_, lean_object* v___x_2340_, lean_object* v_fst_2341_, lean_object* v___x_2342_, lean_object* v_a_2343_, lean_object* v_b_2344_){
_start:
{
uint8_t v___x_2345_; 
v___x_2345_ = lean_nat_dec_lt(v_a_2343_, v_upperBound_2339_);
if (v___x_2345_ == 0)
{
lean_dec(v_a_2343_);
return v_b_2344_;
}
else
{
lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v___x_2346_ = l_Subarray_get___redArg(v_fst_2341_, v_a_2343_);
lean_inc(v_a_2343_);
v___x_2347_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(v_b_2344_, v_a_2343_, v___x_2346_);
v___x_2348_ = lean_unsigned_to_nat(1u);
v___x_2349_ = lean_nat_add(v_a_2343_, v___x_2348_);
lean_dec(v_a_2343_);
v_a_2343_ = v___x_2349_;
v_b_2344_ = v___x_2347_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg___boxed(lean_object* v_upperBound_2351_, lean_object* v___x_2352_, lean_object* v_fst_2353_, lean_object* v___x_2354_, lean_object* v_a_2355_, lean_object* v_b_2356_){
_start:
{
lean_object* v_res_2357_; 
v_res_2357_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(v_upperBound_2351_, v___x_2352_, v_fst_2353_, v___x_2354_, v_a_2355_, v_b_2356_);
lean_dec(v___x_2354_);
lean_dec_ref(v_fst_2353_);
lean_dec(v___x_2352_);
lean_dec(v_upperBound_2351_);
return v_res_2357_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2358_ = lean_box(0);
v___x_2359_ = lean_unsigned_to_nat(16u);
v___x_2360_ = lean_mk_array(v___x_2359_, v___x_2358_);
return v___x_2360_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v_hist_2363_; 
v___x_2361_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0);
v___x_2362_ = lean_unsigned_to_nat(0u);
v_hist_2363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_2363_, 0, v___x_2362_);
lean_ctor_set(v_hist_2363_, 1, v___x_2361_);
return v_hist_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(lean_object* v_left_2364_, lean_object* v_right_2365_){
_start:
{
lean_object* v___x_2366_; lean_object* v_snd_2367_; lean_object* v_fst_2368_; lean_object* v_fst_2369_; lean_object* v_snd_2370_; lean_object* v___x_2371_; lean_object* v_snd_2372_; lean_object* v_fst_2373_; lean_object* v_fst_2374_; lean_object* v_snd_2375_; lean_object* v_start_2376_; lean_object* v_stop_2377_; lean_object* v___x_2378_; lean_object* v_hist_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v_start_2382_; lean_object* v_stop_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v_buckets_2386_; lean_object* v___x_2387_; lean_object* v___y_2389_; lean_object* v___x_2415_; lean_object* v___x_2416_; uint8_t v___x_2417_; 
v___x_2366_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2(v_left_2364_, v_right_2365_);
v_snd_2367_ = lean_ctor_get(v___x_2366_, 1);
lean_inc(v_snd_2367_);
v_fst_2368_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_fst_2368_);
lean_dec_ref(v___x_2366_);
v_fst_2369_ = lean_ctor_get(v_snd_2367_, 0);
lean_inc(v_fst_2369_);
v_snd_2370_ = lean_ctor_get(v_snd_2367_, 1);
lean_inc(v_snd_2370_);
lean_dec(v_snd_2367_);
v___x_2371_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3(v_fst_2369_, v_snd_2370_);
v_snd_2372_ = lean_ctor_get(v___x_2371_, 1);
lean_inc(v_snd_2372_);
v_fst_2373_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_fst_2373_);
lean_dec_ref(v___x_2371_);
v_fst_2374_ = lean_ctor_get(v_snd_2372_, 0);
lean_inc(v_fst_2374_);
v_snd_2375_ = lean_ctor_get(v_snd_2372_, 1);
lean_inc(v_snd_2375_);
lean_dec(v_snd_2372_);
v_start_2376_ = lean_ctor_get(v_fst_2373_, 1);
v_stop_2377_ = lean_ctor_get(v_fst_2373_, 2);
v___x_2378_ = lean_unsigned_to_nat(0u);
v_hist_2379_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1);
v___x_2380_ = lean_nat_sub(v_stop_2377_, v_start_2376_);
v___x_2381_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(v___x_2380_, v_fst_2374_, v___x_2380_, v_fst_2373_, v___x_2378_, v_hist_2379_);
v_start_2382_ = lean_ctor_get(v_fst_2374_, 1);
v_stop_2383_ = lean_ctor_get(v_fst_2374_, 2);
v___x_2384_ = lean_nat_sub(v_stop_2383_, v_start_2382_);
v___x_2385_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(v___x_2384_, v___x_2384_, v_fst_2374_, v___x_2380_, v___x_2378_, v___x_2381_);
lean_dec(v___x_2380_);
lean_dec(v___x_2384_);
v_buckets_2386_ = lean_ctor_get(v___x_2385_, 1);
lean_inc_ref(v_buckets_2386_);
lean_dec_ref(v___x_2385_);
v___x_2387_ = lean_box(0);
v___x_2415_ = lean_box(0);
v___x_2416_ = lean_array_get_size(v_buckets_2386_);
v___x_2417_ = lean_nat_dec_lt(v___x_2378_, v___x_2416_);
if (v___x_2417_ == 0)
{
lean_dec_ref(v_buckets_2386_);
v___y_2389_ = v___x_2415_;
goto v___jp_2388_;
}
else
{
size_t v___x_2418_; size_t v___x_2419_; lean_object* v___x_2420_; 
v___x_2418_ = lean_usize_of_nat(v___x_2416_);
v___x_2419_ = ((size_t)0ULL);
v___x_2420_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(v_buckets_2386_, v___x_2418_, v___x_2419_, v___x_2415_);
lean_dec_ref(v_buckets_2386_);
v___y_2389_ = v___x_2420_;
goto v___jp_2388_;
}
v___jp_2388_:
{
lean_object* v___x_2390_; 
v___x_2390_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(v___y_2389_, v___x_2387_);
lean_dec(v___y_2389_);
if (lean_obj_tag(v___x_2390_) == 1)
{
lean_object* v_val_2391_; lean_object* v_snd_2392_; lean_object* v_snd_2393_; lean_object* v_fst_2394_; lean_object* v_fst_2395_; lean_object* v_snd_2396_; lean_object* v___x_2397_; lean_object* v_fst_2398_; lean_object* v_snd_2399_; lean_object* v___x_2400_; lean_object* v_fst_2401_; lean_object* v_snd_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v_val_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_val_2391_);
lean_dec_ref(v___x_2390_);
v_snd_2392_ = lean_ctor_get(v_val_2391_, 1);
lean_inc(v_snd_2392_);
lean_dec(v_val_2391_);
v_snd_2393_ = lean_ctor_get(v_snd_2392_, 1);
lean_inc(v_snd_2393_);
v_fst_2394_ = lean_ctor_get(v_snd_2392_, 0);
lean_inc(v_fst_2394_);
lean_dec(v_snd_2392_);
v_fst_2395_ = lean_ctor_get(v_snd_2393_, 0);
lean_inc(v_fst_2395_);
v_snd_2396_ = lean_ctor_get(v_snd_2393_, 1);
lean_inc(v_snd_2396_);
lean_dec(v_snd_2393_);
v___x_2397_ = l_Subarray_split___redArg(v_fst_2373_, v_fst_2395_);
lean_dec(v_fst_2395_);
v_fst_2398_ = lean_ctor_get(v___x_2397_, 0);
lean_inc(v_fst_2398_);
v_snd_2399_ = lean_ctor_get(v___x_2397_, 1);
lean_inc(v_snd_2399_);
lean_dec_ref(v___x_2397_);
v___x_2400_ = l_Subarray_split___redArg(v_fst_2374_, v_snd_2396_);
lean_dec(v_snd_2396_);
v_fst_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_fst_2401_);
v_snd_2402_ = lean_ctor_get(v___x_2400_, 1);
lean_inc(v_snd_2402_);
lean_dec_ref(v___x_2400_);
v___x_2403_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v_fst_2398_, v_fst_2401_);
v___x_2404_ = l_Array_append___redArg(v_fst_2368_, v___x_2403_);
lean_dec_ref(v___x_2403_);
v___x_2405_ = lean_unsigned_to_nat(1u);
v___x_2406_ = lean_mk_empty_array_with_capacity(v___x_2405_);
v___x_2407_ = lean_array_push(v___x_2406_, v_fst_2394_);
v___x_2408_ = l_Array_append___redArg(v___x_2404_, v___x_2407_);
lean_dec_ref(v___x_2407_);
v___x_2409_ = l_Subarray_drop___redArg(v_snd_2399_, v___x_2405_);
v___x_2410_ = l_Subarray_drop___redArg(v_snd_2402_, v___x_2405_);
v___x_2411_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v___x_2409_, v___x_2410_);
v___x_2412_ = l_Array_append___redArg(v___x_2408_, v___x_2411_);
lean_dec_ref(v___x_2411_);
v___x_2413_ = l_Array_append___redArg(v___x_2412_, v_snd_2375_);
lean_dec(v_snd_2375_);
return v___x_2413_;
}
else
{
lean_object* v___x_2414_; 
lean_dec(v___x_2390_);
lean_dec(v_fst_2374_);
lean_dec(v_fst_2373_);
v___x_2414_ = l_Array_append___redArg(v_fst_2368_, v_snd_2375_);
lean_dec(v_snd_2375_);
return v___x_2414_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(lean_object* v___x_2421_, lean_object* v_edited_2422_, lean_object* v_b_2423_){
_start:
{
lean_object* v_fst_2424_; lean_object* v_snd_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2444_; 
v_fst_2424_ = lean_ctor_get(v_b_2423_, 0);
v_snd_2425_ = lean_ctor_get(v_b_2423_, 1);
v_isSharedCheck_2444_ = !lean_is_exclusive(v_b_2423_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2427_ = v_b_2423_;
v_isShared_2428_ = v_isSharedCheck_2444_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_snd_2425_);
lean_inc(v_fst_2424_);
lean_dec(v_b_2423_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2444_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
uint8_t v___x_2429_; 
v___x_2429_ = lean_nat_dec_lt(v_snd_2425_, v___x_2421_);
if (v___x_2429_ == 0)
{
lean_object* v___x_2431_; 
if (v_isShared_2428_ == 0)
{
v___x_2431_ = v___x_2427_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_fst_2424_);
lean_ctor_set(v_reuseFailAlloc_2432_, 1, v_snd_2425_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
else
{
uint8_t v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2437_; 
v___x_2433_ = 0;
v___x_2434_ = lean_array_fget_borrowed(v_edited_2422_, v_snd_2425_);
v___x_2435_ = lean_box(v___x_2433_);
lean_inc(v___x_2434_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 1, v___x_2434_);
lean_ctor_set(v___x_2427_, 0, v___x_2435_);
v___x_2437_ = v___x_2427_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2435_);
lean_ctor_set(v_reuseFailAlloc_2443_, 1, v___x_2434_);
v___x_2437_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2438_ = lean_array_push(v_fst_2424_, v___x_2437_);
v___x_2439_ = lean_unsigned_to_nat(1u);
v___x_2440_ = lean_nat_add(v_snd_2425_, v___x_2439_);
lean_dec(v_snd_2425_);
v___x_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2438_);
lean_ctor_set(v___x_2441_, 1, v___x_2440_);
v_b_2423_ = v___x_2441_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___boxed(lean_object* v___x_2445_, lean_object* v_edited_2446_, lean_object* v_b_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(v___x_2445_, v_edited_2446_, v_b_2447_);
lean_dec_ref(v_edited_2446_);
lean_dec(v___x_2445_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(size_t v_sz_2449_, size_t v_i_2450_, lean_object* v_bs_2451_){
_start:
{
uint8_t v___x_2452_; 
v___x_2452_ = lean_usize_dec_lt(v_i_2450_, v_sz_2449_);
if (v___x_2452_ == 0)
{
return v_bs_2451_;
}
else
{
lean_object* v_v_2453_; lean_object* v___x_2454_; lean_object* v_bs_x27_2455_; uint8_t v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; size_t v___x_2459_; size_t v___x_2460_; lean_object* v___x_2461_; 
v_v_2453_ = lean_array_uget(v_bs_2451_, v_i_2450_);
v___x_2454_ = lean_unsigned_to_nat(0u);
v_bs_x27_2455_ = lean_array_uset(v_bs_2451_, v_i_2450_, v___x_2454_);
v___x_2456_ = 1;
v___x_2457_ = lean_box(v___x_2456_);
v___x_2458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2457_);
lean_ctor_set(v___x_2458_, 1, v_v_2453_);
v___x_2459_ = ((size_t)1ULL);
v___x_2460_ = lean_usize_add(v_i_2450_, v___x_2459_);
v___x_2461_ = lean_array_uset(v_bs_x27_2455_, v_i_2450_, v___x_2458_);
v_i_2450_ = v___x_2460_;
v_bs_2451_ = v___x_2461_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7___boxed(lean_object* v_sz_2463_, lean_object* v_i_2464_, lean_object* v_bs_2465_){
_start:
{
size_t v_sz_boxed_2466_; size_t v_i_boxed_2467_; lean_object* v_res_2468_; 
v_sz_boxed_2466_ = lean_unbox_usize(v_sz_2463_);
lean_dec(v_sz_2463_);
v_i_boxed_2467_ = lean_unbox_usize(v_i_2464_);
lean_dec(v_i_2464_);
v_res_2468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_boxed_2466_, v_i_boxed_2467_, v_bs_2465_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(lean_object* v___x_2469_, lean_object* v_original_2470_, lean_object* v_b_2471_){
_start:
{
lean_object* v_fst_2472_; lean_object* v_snd_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2492_; 
v_fst_2472_ = lean_ctor_get(v_b_2471_, 0);
v_snd_2473_ = lean_ctor_get(v_b_2471_, 1);
v_isSharedCheck_2492_ = !lean_is_exclusive(v_b_2471_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2475_ = v_b_2471_;
v_isShared_2476_ = v_isSharedCheck_2492_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_snd_2473_);
lean_inc(v_fst_2472_);
lean_dec(v_b_2471_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2492_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
uint8_t v___x_2477_; 
v___x_2477_ = lean_nat_dec_lt(v_snd_2473_, v___x_2469_);
if (v___x_2477_ == 0)
{
lean_object* v___x_2479_; 
if (v_isShared_2476_ == 0)
{
v___x_2479_ = v___x_2475_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v_fst_2472_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_snd_2473_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
return v___x_2479_;
}
}
else
{
uint8_t v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2485_; 
v___x_2481_ = 1;
v___x_2482_ = lean_array_fget_borrowed(v_original_2470_, v_snd_2473_);
v___x_2483_ = lean_box(v___x_2481_);
lean_inc(v___x_2482_);
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 1, v___x_2482_);
lean_ctor_set(v___x_2475_, 0, v___x_2483_);
v___x_2485_ = v___x_2475_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v___x_2482_);
v___x_2485_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2486_ = lean_array_push(v_fst_2472_, v___x_2485_);
v___x_2487_ = lean_unsigned_to_nat(1u);
v___x_2488_ = lean_nat_add(v_snd_2473_, v___x_2487_);
lean_dec(v_snd_2473_);
v___x_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2486_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
v_b_2471_ = v___x_2489_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___boxed(lean_object* v___x_2493_, lean_object* v_original_2494_, lean_object* v_b_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(v___x_2493_, v_original_2494_, v_b_2495_);
lean_dec_ref(v_original_2494_);
lean_dec(v___x_2493_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(lean_object* v_original_2502_, lean_object* v_edited_2503_){
_start:
{
lean_object* v_i_2504_; lean_object* v___x_2505_; uint8_t v___x_2506_; 
v_i_2504_ = lean_unsigned_to_nat(0u);
v___x_2505_ = lean_array_get_size(v_original_2502_);
v___x_2506_ = lean_nat_dec_lt(v_i_2504_, v___x_2505_);
if (v___x_2506_ == 0)
{
size_t v_sz_2507_; size_t v___x_2508_; lean_object* v___x_2509_; 
lean_dec_ref(v_original_2502_);
v_sz_2507_ = lean_array_size(v_edited_2503_);
v___x_2508_ = ((size_t)0ULL);
v___x_2509_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_2507_, v___x_2508_, v_edited_2503_);
return v___x_2509_;
}
else
{
lean_object* v___x_2510_; uint8_t v___x_2511_; 
v___x_2510_ = lean_array_get_size(v_edited_2503_);
v___x_2511_ = lean_nat_dec_lt(v_i_2504_, v___x_2510_);
if (v___x_2511_ == 0)
{
size_t v_sz_2512_; size_t v___x_2513_; lean_object* v___x_2514_; 
lean_dec_ref(v_edited_2503_);
v_sz_2512_ = lean_array_size(v_original_2502_);
v___x_2513_ = ((size_t)0ULL);
v___x_2514_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_2512_, v___x_2513_, v_original_2502_);
return v___x_2514_;
}
else
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v_ds_2517_; lean_object* v___x_2518_; size_t v_sz_2519_; size_t v___x_2520_; lean_object* v___x_2521_; lean_object* v_snd_2522_; lean_object* v_fst_2523_; lean_object* v_fst_2524_; lean_object* v_snd_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2544_; 
lean_inc_ref(v_original_2502_);
v___x_2515_ = l_Array_toSubarray___redArg(v_original_2502_, v_i_2504_, v___x_2505_);
lean_inc_ref(v_edited_2503_);
v___x_2516_ = l_Array_toSubarray___redArg(v_edited_2503_, v_i_2504_, v___x_2510_);
v_ds_2517_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v___x_2515_, v___x_2516_);
v___x_2518_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__1));
v_sz_2519_ = lean_array_size(v_ds_2517_);
v___x_2520_ = ((size_t)0ULL);
v___x_2521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v_edited_2503_, v___x_2510_, v_original_2502_, v___x_2505_, v_ds_2517_, v_sz_2519_, v___x_2520_, v___x_2518_);
lean_dec_ref(v_ds_2517_);
v_snd_2522_ = lean_ctor_get(v___x_2521_, 1);
lean_inc(v_snd_2522_);
v_fst_2523_ = lean_ctor_get(v___x_2521_, 0);
lean_inc(v_fst_2523_);
lean_dec_ref(v___x_2521_);
v_fst_2524_ = lean_ctor_get(v_snd_2522_, 0);
v_snd_2525_ = lean_ctor_get(v_snd_2522_, 1);
v_isSharedCheck_2544_ = !lean_is_exclusive(v_snd_2522_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2527_ = v_snd_2522_;
v_isShared_2528_ = v_isSharedCheck_2544_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_snd_2525_);
lean_inc(v_fst_2524_);
lean_dec(v_snd_2522_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2544_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 1, v_fst_2524_);
lean_ctor_set(v___x_2527_, 0, v_fst_2523_);
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_fst_2523_);
lean_ctor_set(v_reuseFailAlloc_2543_, 1, v_fst_2524_);
v___x_2530_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
lean_object* v___x_2531_; lean_object* v_fst_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2541_; 
v___x_2531_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(v___x_2505_, v_original_2502_, v___x_2530_);
lean_dec_ref(v_original_2502_);
v_fst_2532_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2541_ == 0)
{
lean_object* v_unused_2542_; 
v_unused_2542_ = lean_ctor_get(v___x_2531_, 1);
lean_dec(v_unused_2542_);
v___x_2534_ = v___x_2531_;
v_isShared_2535_ = v_isSharedCheck_2541_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_fst_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2541_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 1, v_snd_2525_);
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_fst_2532_);
lean_ctor_set(v_reuseFailAlloc_2540_, 1, v_snd_2525_);
v___x_2537_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2538_; lean_object* v_fst_2539_; 
v___x_2538_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(v___x_2510_, v_edited_2503_, v___x_2537_);
lean_dec_ref(v_edited_2503_);
v_fst_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_fst_2539_);
lean_dec_ref(v___x_2538_);
return v_fst_2539_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(lean_object* v___x_2545_, uint8_t v_inSubst_2546_, lean_object* v___x_2547_, lean_object* v_____r_2548_, lean_object* v_wssIdx_2549_){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v___x_2550_ = lean_box(v_inSubst_2546_);
v___x_2551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2545_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
v___x_2552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2552_, 0, v_wssIdx_2549_);
lean_ctor_set(v___x_2552_, 1, v___x_2551_);
v___x_2553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2547_);
lean_ctor_set(v___x_2553_, 1, v___x_2552_);
v___x_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2554_, 0, v___x_2553_);
return v___x_2554_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1___boxed(lean_object* v___x_2555_, lean_object* v_inSubst_2556_, lean_object* v___x_2557_, lean_object* v_____r_2558_, lean_object* v_wssIdx_2559_){
_start:
{
uint8_t v_inSubst_boxed_2560_; lean_object* v_res_2561_; 
v_inSubst_boxed_2560_ = lean_unbox(v_inSubst_2556_);
v_res_2561_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2555_, v_inSubst_boxed_2560_, v___x_2557_, v_____r_2558_, v_wssIdx_2559_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(lean_object* v_fst_2562_, uint8_t v___x_2563_, lean_object* v_fst_2564_, lean_object* v___x_2565_, lean_object* v_00___2566_){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2567_ = lean_box(v___x_2563_);
v___x_2568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2568_, 0, v_fst_2562_);
lean_ctor_set(v___x_2568_, 1, v___x_2567_);
v___x_2569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2569_, 0, v_fst_2564_);
lean_ctor_set(v___x_2569_, 1, v___x_2568_);
v___x_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2570_, 0, v___x_2565_);
lean_ctor_set(v___x_2570_, 1, v___x_2569_);
v___x_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2570_);
return v___x_2571_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0___boxed(lean_object* v_fst_2572_, lean_object* v___x_2573_, lean_object* v_fst_2574_, lean_object* v___x_2575_, lean_object* v_00___2576_){
_start:
{
uint8_t v___x_9190__boxed_2577_; lean_object* v_res_2578_; 
v___x_9190__boxed_2577_ = lean_unbox(v___x_2573_);
v_res_2578_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2572_, v___x_9190__boxed_2577_, v_fst_2574_, v___x_2575_, v_00___2576_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(uint8_t v_inSubst_2579_, lean_object* v_snd_2580_, lean_object* v_fst_2581_, lean_object* v_____r_2582_, lean_object* v_withWs_2583_, lean_object* v_wssIdx_2584_){
_start:
{
lean_object* v_wss_x27Idx_2586_; uint8_t v___x_2592_; 
v___x_2592_ = lean_unbox(v_snd_2580_);
if (v___x_2592_ == 0)
{
v_wss_x27Idx_2586_ = v_fst_2581_;
goto v___jp_2585_;
}
else
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = lean_unsigned_to_nat(1u);
v___x_2594_ = lean_nat_add(v_fst_2581_, v___x_2593_);
lean_dec(v_fst_2581_);
v_wss_x27Idx_2586_ = v___x_2594_;
goto v___jp_2585_;
}
v___jp_2585_:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2587_ = lean_box(v_inSubst_2579_);
v___x_2588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2588_, 0, v_wss_x27Idx_2586_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
v___x_2589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2589_, 0, v_wssIdx_2584_);
lean_ctor_set(v___x_2589_, 1, v___x_2588_);
v___x_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2590_, 0, v_withWs_2583_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
v___x_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
return v___x_2591_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2___boxed(lean_object* v_inSubst_2595_, lean_object* v_snd_2596_, lean_object* v_fst_2597_, lean_object* v_____r_2598_, lean_object* v_withWs_2599_, lean_object* v_wssIdx_2600_){
_start:
{
uint8_t v_inSubst_boxed_2601_; lean_object* v_res_2602_; 
v_inSubst_boxed_2601_ = lean_unbox(v_inSubst_2595_);
v_res_2602_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_boxed_2601_, v_snd_2596_, v_fst_2597_, v_____r_2598_, v_withWs_2599_, v_wssIdx_2600_);
lean_dec(v_snd_2596_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(lean_object* v_upperBound_2603_, lean_object* v_diff_2604_, lean_object* v_snd_2605_, lean_object* v_snd_2606_, lean_object* v_a_2607_, lean_object* v_b_2608_){
_start:
{
lean_object* v_a_2610_; lean_object* v___y_2615_; uint8_t v___x_2618_; 
v___x_2618_ = lean_nat_dec_lt(v_a_2607_, v_upperBound_2603_);
if (v___x_2618_ == 0)
{
lean_dec(v_a_2607_);
return v_b_2608_;
}
else
{
lean_object* v___x_2619_; lean_object* v_snd_2620_; lean_object* v_snd_2621_; lean_object* v_fst_2622_; lean_object* v_fst_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2763_; 
v___x_2619_ = lean_array_fget_borrowed(v_diff_2604_, v_a_2607_);
v_snd_2620_ = lean_ctor_get(v_b_2608_, 1);
lean_inc(v_snd_2620_);
v_snd_2621_ = lean_ctor_get(v_snd_2620_, 1);
lean_inc(v_snd_2621_);
v_fst_2622_ = lean_ctor_get(v___x_2619_, 0);
v_fst_2623_ = lean_ctor_get(v_b_2608_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v_b_2608_);
if (v_isSharedCheck_2763_ == 0)
{
lean_object* v_unused_2764_; 
v_unused_2764_ = lean_ctor_get(v_b_2608_, 1);
lean_dec(v_unused_2764_);
v___x_2625_ = v_b_2608_;
v_isShared_2626_ = v_isSharedCheck_2763_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_fst_2623_);
lean_dec(v_b_2608_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2763_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v_fst_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2761_; 
v_fst_2627_ = lean_ctor_get(v_snd_2620_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v_snd_2620_);
if (v_isSharedCheck_2761_ == 0)
{
lean_object* v_unused_2762_; 
v_unused_2762_ = lean_ctor_get(v_snd_2620_, 1);
lean_dec(v_unused_2762_);
v___x_2629_ = v_snd_2620_;
v_isShared_2630_ = v_isSharedCheck_2761_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_fst_2627_);
lean_dec(v_snd_2620_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2761_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v_fst_2631_; lean_object* v_snd_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2760_; 
v_fst_2631_ = lean_ctor_get(v_snd_2621_, 0);
v_snd_2632_ = lean_ctor_get(v_snd_2621_, 1);
v_isSharedCheck_2760_ = !lean_is_exclusive(v_snd_2621_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2634_ = v_snd_2621_;
v_isShared_2635_ = v_isSharedCheck_2760_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_snd_2632_);
lean_inc(v_fst_2631_);
lean_dec(v_snd_2621_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2760_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2636_; lean_object* v___y_2638_; lean_object* v___y_2653_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; uint8_t v___x_2664_; 
lean_inc(v___x_2619_);
v___x_2636_ = lean_array_push(v_fst_2623_, v___x_2619_);
v___x_2661_ = lean_unsigned_to_nat(1u);
v___x_2662_ = lean_nat_add(v_a_2607_, v___x_2661_);
v___x_2663_ = lean_array_get_size(v_diff_2604_);
v___x_2664_ = lean_nat_dec_lt(v___x_2662_, v___x_2663_);
if (v___x_2664_ == 0)
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
lean_dec(v___x_2662_);
lean_del_object(v___x_2634_);
lean_del_object(v___x_2629_);
lean_del_object(v___x_2625_);
v___x_2665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2665_, 0, v_fst_2631_);
lean_ctor_set(v___x_2665_, 1, v_snd_2632_);
v___x_2666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2666_, 0, v_fst_2627_);
lean_ctor_set(v___x_2666_, 1, v___x_2665_);
v___x_2667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2636_);
lean_ctor_set(v___x_2667_, 1, v___x_2666_);
v_a_2610_ = v___x_2667_;
goto v___jp_2609_;
}
else
{
lean_object* v___x_2668_; lean_object* v_fst_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2758_; 
v___x_2668_ = lean_array_fget(v_diff_2604_, v___x_2662_);
lean_dec(v___x_2662_);
v_fst_2669_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2758_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2758_ == 0)
{
lean_object* v_unused_2759_; 
v_unused_2759_ = lean_ctor_get(v___x_2668_, 1);
lean_dec(v_unused_2759_);
v___x_2671_ = v___x_2668_;
v_isShared_2672_ = v_isSharedCheck_2758_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_fst_2669_);
lean_dec(v___x_2668_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2758_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
uint8_t v_inSubst_2673_; lean_object* v___y_2675_; lean_object* v___x_2684_; uint8_t v___x_2685_; 
v_inSubst_2673_ = 0;
v___x_2684_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2685_ = lean_unbox(v_fst_2622_);
switch(v___x_2685_)
{
case 0:
{
uint8_t v___x_2686_; 
lean_del_object(v___x_2634_);
lean_del_object(v___x_2629_);
lean_del_object(v___x_2625_);
v___x_2686_ = lean_unbox(v_fst_2669_);
switch(v___x_2686_)
{
case 0:
{
lean_object* v___x_2687_; lean_object* v___x_2689_; 
v___x_2687_ = lean_array_get_borrowed(v___x_2684_, v_snd_2605_, v_fst_2631_);
lean_inc(v___x_2687_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 1, v___x_2687_);
v___x_2689_ = v___x_2671_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_fst_2669_);
lean_ctor_set(v_reuseFailAlloc_2695_, 1, v___x_2687_);
v___x_2689_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2690_ = lean_array_push(v___x_2636_, v___x_2689_);
v___x_2691_ = lean_nat_add(v_fst_2631_, v___x_2661_);
lean_dec(v_fst_2631_);
v___x_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2691_);
lean_ctor_set(v___x_2692_, 1, v_snd_2632_);
v___x_2693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2693_, 0, v_fst_2627_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2690_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
v_a_2610_ = v___x_2694_;
goto v___jp_2609_;
}
}
case 1:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; 
lean_del_object(v___x_2671_);
lean_dec(v_fst_2669_);
lean_dec(v_snd_2632_);
v___x_2696_ = lean_box(0);
v___x_2697_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2631_, v___x_2618_, v_fst_2627_, v___x_2636_, v___x_2696_);
v___y_2615_ = v___x_2697_;
goto v___jp_2614_;
}
default: 
{
lean_object* v___x_2698_; uint8_t v___x_2699_; 
lean_dec(v_fst_2669_);
v___x_2698_ = lean_array_get_borrowed(v___x_2684_, v_snd_2605_, v_fst_2631_);
v___x_2699_ = lean_unbox(v_snd_2632_);
if (v___x_2699_ == 0)
{
lean_object* v___x_2701_; 
lean_inc(v___x_2698_);
lean_inc(v_fst_2622_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 1, v___x_2698_);
lean_ctor_set(v___x_2671_, 0, v_fst_2622_);
v___x_2701_ = v___x_2671_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2704_; 
v_reuseFailAlloc_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_fst_2622_);
lean_ctor_set(v_reuseFailAlloc_2704_, 1, v___x_2698_);
v___x_2701_ = v_reuseFailAlloc_2704_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2702_ = lean_mk_empty_array_with_capacity(v___x_2661_);
v___x_2703_ = lean_array_push(v___x_2702_, v___x_2701_);
v___y_2675_ = v___x_2703_;
goto v___jp_2674_;
}
}
else
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
lean_del_object(v___x_2671_);
v___x_2705_ = lean_array_get_borrowed(v___x_2684_, v_snd_2606_, v_fst_2627_);
lean_inc(v___x_2698_);
lean_inc(v___x_2705_);
v___x_2706_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2705_, v___x_2698_);
v___y_2675_ = v___x_2706_;
goto v___jp_2674_;
}
}
}
}
case 1:
{
uint8_t v___x_2707_; 
lean_del_object(v___x_2634_);
lean_del_object(v___x_2629_);
lean_del_object(v___x_2625_);
v___x_2707_ = lean_unbox(v_fst_2669_);
switch(v___x_2707_)
{
case 0:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
lean_del_object(v___x_2671_);
lean_dec(v_fst_2669_);
lean_dec(v_snd_2632_);
v___x_2708_ = lean_box(0);
v___x_2709_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2631_, v___x_2618_, v_fst_2627_, v___x_2636_, v___x_2708_);
v___y_2615_ = v___x_2709_;
goto v___jp_2614_;
}
case 1:
{
lean_object* v___x_2710_; lean_object* v___x_2712_; 
v___x_2710_ = lean_array_get_borrowed(v___x_2684_, v_snd_2606_, v_fst_2627_);
lean_inc(v___x_2710_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 1, v___x_2710_);
v___x_2712_ = v___x_2671_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_fst_2669_);
lean_ctor_set(v_reuseFailAlloc_2718_, 1, v___x_2710_);
v___x_2712_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2713_ = lean_array_push(v___x_2636_, v___x_2712_);
v___x_2714_ = lean_nat_add(v_fst_2627_, v___x_2661_);
lean_dec(v_fst_2627_);
v___x_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2715_, 0, v_fst_2631_);
lean_ctor_set(v___x_2715_, 1, v_snd_2632_);
v___x_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2714_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
v___x_2717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2713_);
lean_ctor_set(v___x_2717_, 1, v___x_2716_);
v_a_2610_ = v___x_2717_;
goto v___jp_2609_;
}
}
default: 
{
uint8_t v___x_2722_; 
lean_dec(v_fst_2669_);
v___x_2722_ = lean_unbox(v_snd_2632_);
if (v___x_2722_ == 0)
{
lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; uint8_t v___x_2727_; 
v___x_2723_ = lean_array_get_borrowed(v___x_2684_, v_snd_2606_, v_fst_2627_);
v___x_2724_ = lean_unsigned_to_nat(0u);
v___x_2725_ = lean_string_utf8_byte_size(v___x_2723_);
lean_inc(v___x_2723_);
v___x_2726_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2723_);
lean_ctor_set(v___x_2726_, 1, v___x_2724_);
lean_ctor_set(v___x_2726_, 2, v___x_2725_);
v___x_2727_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_2726_);
lean_dec_ref(v___x_2726_);
if (v___x_2727_ == 0)
{
lean_object* v___x_2729_; 
lean_inc(v___x_2723_);
lean_inc(v_fst_2622_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 1, v___x_2723_);
lean_ctor_set(v___x_2671_, 0, v_fst_2622_);
v___x_2729_ = v___x_2671_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_fst_2622_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v___x_2723_);
v___x_2729_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2730_ = lean_array_push(v___x_2636_, v___x_2729_);
v___x_2731_ = lean_nat_add(v_fst_2627_, v___x_2661_);
lean_dec(v_fst_2627_);
v___x_2732_ = lean_box(0);
v___x_2733_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2673_, v_snd_2632_, v_fst_2631_, v___x_2732_, v___x_2730_, v___x_2731_);
lean_dec(v_snd_2632_);
v___y_2615_ = v___x_2733_;
goto v___jp_2614_;
}
}
else
{
lean_del_object(v___x_2671_);
goto v___jp_2719_;
}
}
else
{
lean_del_object(v___x_2671_);
goto v___jp_2719_;
}
v___jp_2719_:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2720_ = lean_box(0);
v___x_2721_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2673_, v_snd_2632_, v_fst_2631_, v___x_2720_, v___x_2636_, v_fst_2627_);
lean_dec(v_snd_2632_);
v___y_2615_ = v___x_2721_;
goto v___jp_2614_;
}
}
}
}
default: 
{
uint8_t v___x_2735_; 
v___x_2735_ = lean_unbox(v_fst_2669_);
if (v___x_2735_ == 1)
{
lean_object* v___x_2736_; lean_object* v___x_2737_; uint8_t v___x_2738_; 
v___x_2736_ = lean_array_get_borrowed(v___x_2684_, v_snd_2606_, v_fst_2627_);
v___x_2737_ = lean_array_get_size(v_snd_2605_);
v___x_2738_ = lean_nat_dec_lt(v_fst_2631_, v___x_2737_);
if (v___x_2738_ == 0)
{
lean_object* v___x_2740_; 
lean_inc(v___x_2736_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 1, v___x_2736_);
v___x_2740_ = v___x_2671_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_fst_2669_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v___x_2736_);
v___x_2740_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2741_ = lean_mk_empty_array_with_capacity(v___x_2661_);
v___x_2742_ = lean_array_push(v___x_2741_, v___x_2740_);
v___y_2638_ = v___x_2742_;
goto v___jp_2637_;
}
}
else
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
lean_del_object(v___x_2671_);
lean_dec(v_fst_2669_);
v___x_2744_ = lean_array_fget_borrowed(v_snd_2605_, v_fst_2631_);
lean_inc(v___x_2744_);
lean_inc(v___x_2736_);
v___x_2745_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2736_, v___x_2744_);
v___y_2638_ = v___x_2745_;
goto v___jp_2637_;
}
}
else
{
lean_object* v___x_2746_; lean_object* v___x_2747_; uint8_t v___x_2748_; 
lean_dec(v_fst_2669_);
lean_del_object(v___x_2634_);
lean_del_object(v___x_2629_);
lean_del_object(v___x_2625_);
v___x_2746_ = lean_array_get_borrowed(v___x_2684_, v_snd_2605_, v_fst_2631_);
v___x_2747_ = lean_array_get_size(v_snd_2606_);
v___x_2748_ = lean_nat_dec_lt(v_fst_2627_, v___x_2747_);
if (v___x_2748_ == 0)
{
uint8_t v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2752_; 
v___x_2749_ = 0;
v___x_2750_ = lean_box(v___x_2749_);
lean_inc(v___x_2746_);
if (v_isShared_2672_ == 0)
{
lean_ctor_set(v___x_2671_, 1, v___x_2746_);
lean_ctor_set(v___x_2671_, 0, v___x_2750_);
v___x_2752_ = v___x_2671_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2750_);
lean_ctor_set(v_reuseFailAlloc_2755_, 1, v___x_2746_);
v___x_2752_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = lean_mk_empty_array_with_capacity(v___x_2661_);
v___x_2754_ = lean_array_push(v___x_2753_, v___x_2752_);
v___y_2653_ = v___x_2754_;
goto v___jp_2652_;
}
}
else
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
lean_del_object(v___x_2671_);
v___x_2756_ = lean_array_fget_borrowed(v_snd_2606_, v_fst_2627_);
lean_inc(v___x_2746_);
lean_inc(v___x_2756_);
v___x_2757_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2756_, v___x_2746_);
v___y_2653_ = v___x_2757_;
goto v___jp_2652_;
}
}
}
}
v___jp_2674_:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v___x_2676_ = l_Array_append___redArg(v___x_2636_, v___y_2675_);
lean_dec_ref(v___y_2675_);
v___x_2677_ = lean_nat_add(v_fst_2631_, v___x_2661_);
lean_dec(v_fst_2631_);
v___x_2678_ = lean_unbox(v_snd_2632_);
lean_dec(v_snd_2632_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2679_ = lean_box(0);
v___x_2680_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2677_, v_inSubst_2673_, v___x_2676_, v___x_2679_, v_fst_2627_);
v___y_2615_ = v___x_2680_;
goto v___jp_2614_;
}
else
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2681_ = lean_nat_add(v_fst_2627_, v___x_2661_);
lean_dec(v_fst_2627_);
v___x_2682_ = lean_box(0);
v___x_2683_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2677_, v_inSubst_2673_, v___x_2676_, v___x_2682_, v___x_2681_);
v___y_2615_ = v___x_2683_;
goto v___jp_2614_;
}
}
}
}
v___jp_2637_:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2644_; 
v___x_2639_ = l_Array_append___redArg(v___x_2636_, v___y_2638_);
lean_dec_ref(v___y_2638_);
v___x_2640_ = lean_unsigned_to_nat(1u);
v___x_2641_ = lean_nat_add(v_fst_2627_, v___x_2640_);
lean_dec(v_fst_2627_);
v___x_2642_ = lean_nat_add(v_fst_2631_, v___x_2640_);
lean_dec(v_fst_2631_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 0, v___x_2642_);
v___x_2644_ = v___x_2634_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2642_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v_snd_2632_);
v___x_2644_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
lean_object* v___x_2646_; 
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 1, v___x_2644_);
lean_ctor_set(v___x_2629_, 0, v___x_2641_);
v___x_2646_ = v___x_2629_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2641_);
lean_ctor_set(v_reuseFailAlloc_2650_, 1, v___x_2644_);
v___x_2646_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
lean_object* v___x_2648_; 
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 1, v___x_2646_);
lean_ctor_set(v___x_2625_, 0, v___x_2639_);
v___x_2648_ = v___x_2625_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v___x_2639_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v___x_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
v_a_2610_ = v___x_2648_;
goto v___jp_2609_;
}
}
}
}
v___jp_2652_:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2654_ = l_Array_append___redArg(v___x_2636_, v___y_2653_);
lean_dec_ref(v___y_2653_);
v___x_2655_ = lean_unsigned_to_nat(1u);
v___x_2656_ = lean_nat_add(v_fst_2627_, v___x_2655_);
lean_dec(v_fst_2627_);
v___x_2657_ = lean_nat_add(v_fst_2631_, v___x_2655_);
lean_dec(v_fst_2631_);
v___x_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2657_);
lean_ctor_set(v___x_2658_, 1, v_snd_2632_);
v___x_2659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2656_);
lean_ctor_set(v___x_2659_, 1, v___x_2658_);
v___x_2660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2660_, 0, v___x_2654_);
lean_ctor_set(v___x_2660_, 1, v___x_2659_);
v_a_2610_ = v___x_2660_;
goto v___jp_2609_;
}
}
}
}
}
v___jp_2609_:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2611_ = lean_unsigned_to_nat(1u);
v___x_2612_ = lean_nat_add(v_a_2607_, v___x_2611_);
lean_dec(v_a_2607_);
v_a_2607_ = v___x_2612_;
v_b_2608_ = v_a_2610_;
goto _start;
}
v___jp_2614_:
{
if (lean_obj_tag(v___y_2615_) == 0)
{
lean_object* v_a_2616_; 
lean_dec(v_a_2607_);
v_a_2616_ = lean_ctor_get(v___y_2615_, 0);
lean_inc(v_a_2616_);
lean_dec_ref(v___y_2615_);
return v_a_2616_;
}
else
{
lean_object* v_a_2617_; 
v_a_2617_ = lean_ctor_get(v___y_2615_, 0);
lean_inc(v_a_2617_);
lean_dec_ref(v___y_2615_);
v_a_2610_ = v_a_2617_;
goto v___jp_2609_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___boxed(lean_object* v_upperBound_2765_, lean_object* v_diff_2766_, lean_object* v_snd_2767_, lean_object* v_snd_2768_, lean_object* v_a_2769_, lean_object* v_b_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2765_, v_diff_2766_, v_snd_2767_, v_snd_2768_, v_a_2769_, v_b_2770_);
lean_dec_ref(v_snd_2768_);
lean_dec_ref(v_snd_2767_);
lean_dec_ref(v_diff_2766_);
lean_dec(v_upperBound_2765_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(lean_object* v_s_2782_, lean_object* v_s_x27_2783_){
_start:
{
lean_object* v___x_2784_; lean_object* v_fst_2785_; lean_object* v_snd_2786_; lean_object* v___x_2787_; lean_object* v_fst_2788_; lean_object* v_snd_2789_; lean_object* v_diff_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v_fst_2795_; lean_object* v___x_2796_; size_t v_sz_2797_; size_t v___x_2798_; lean_object* v___x_2799_; 
v___x_2784_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_2782_);
v_fst_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_fst_2785_);
v_snd_2786_ = lean_ctor_get(v___x_2784_, 1);
lean_inc(v_snd_2786_);
lean_dec_ref(v___x_2784_);
v___x_2787_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_x27_2783_);
v_fst_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_fst_2788_);
v_snd_2789_ = lean_ctor_get(v___x_2787_, 1);
lean_inc(v_snd_2789_);
lean_dec_ref(v___x_2787_);
v_diff_2790_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(v_fst_2785_, v_fst_2788_);
v___x_2791_ = lean_unsigned_to_nat(0u);
v___x_2792_ = lean_array_get_size(v_diff_2790_);
v___x_2793_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__2));
v___x_2794_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v___x_2792_, v_diff_2790_, v_snd_2789_, v_snd_2786_, v___x_2791_, v___x_2793_);
lean_dec(v_snd_2786_);
lean_dec(v_snd_2789_);
lean_dec_ref(v_diff_2790_);
v_fst_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_fst_2795_);
lean_dec_ref(v___x_2794_);
v___x_2796_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_fst_2795_);
lean_dec(v_fst_2795_);
v_sz_2797_ = lean_array_size(v___x_2796_);
v___x_2798_ = ((size_t)0ULL);
v___x_2799_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_2797_, v___x_2798_, v___x_2796_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___boxed(lean_object* v_s_2800_, lean_object* v_s_x27_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_2800_, v_s_x27_2801_);
lean_dec_ref(v_s_x27_2801_);
lean_dec_ref(v_s_2800_);
return v_res_2802_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(lean_object* v_upperBound_2803_, lean_object* v_diff_2804_, lean_object* v_snd_2805_, lean_object* v_snd_2806_, lean_object* v_inst_2807_, lean_object* v_R_2808_, lean_object* v_a_2809_, lean_object* v_b_2810_, lean_object* v_c_2811_){
_start:
{
lean_object* v___x_2812_; 
v___x_2812_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2803_, v_diff_2804_, v_snd_2805_, v_snd_2806_, v_a_2809_, v_b_2810_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___boxed(lean_object* v_upperBound_2813_, lean_object* v_diff_2814_, lean_object* v_snd_2815_, lean_object* v_snd_2816_, lean_object* v_inst_2817_, lean_object* v_R_2818_, lean_object* v_a_2819_, lean_object* v_b_2820_, lean_object* v_c_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(v_upperBound_2813_, v_diff_2814_, v_snd_2815_, v_snd_2816_, v_inst_2817_, v_R_2818_, v_a_2819_, v_b_2820_, v_c_2821_);
lean_dec_ref(v_snd_2816_);
lean_dec_ref(v_snd_2815_);
lean_dec_ref(v_diff_2814_);
lean_dec(v_upperBound_2813_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4(lean_object* v_as_2823_, lean_object* v_as_x27_2824_, lean_object* v_b_2825_, lean_object* v_a_2826_){
_start:
{
lean_object* v___x_2827_; 
v___x_2827_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(v_as_x27_2824_, v_b_2825_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___boxed(lean_object* v_as_2828_, lean_object* v_as_x27_2829_, lean_object* v_b_2830_, lean_object* v_a_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4(v_as_2828_, v_as_x27_2829_, v_b_2830_, v_a_2831_);
lean_dec(v_as_x27_2829_);
lean_dec(v_as_2828_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7(lean_object* v_lsize_2833_, lean_object* v_rsize_2834_, lean_object* v_histogram_2835_, lean_object* v_index_2836_, lean_object* v_val_2837_){
_start:
{
lean_object* v___x_2838_; 
v___x_2838_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(v_histogram_2835_, v_index_2836_, v_val_2837_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___boxed(lean_object* v_lsize_2839_, lean_object* v_rsize_2840_, lean_object* v_histogram_2841_, lean_object* v_index_2842_, lean_object* v_val_2843_){
_start:
{
lean_object* v_res_2844_; 
v_res_2844_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7(v_lsize_2839_, v_rsize_2840_, v_histogram_2841_, v_index_2842_, v_val_2843_);
lean_dec(v_rsize_2840_);
lean_dec(v_lsize_2839_);
return v_res_2844_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8(lean_object* v_upperBound_2845_, lean_object* v___x_2846_, lean_object* v_fst_2847_, lean_object* v___x_2848_, lean_object* v_inst_2849_, lean_object* v_R_2850_, lean_object* v_a_2851_, lean_object* v_b_2852_, lean_object* v_c_2853_){
_start:
{
lean_object* v___x_2854_; 
v___x_2854_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(v_upperBound_2845_, v___x_2846_, v_fst_2847_, v___x_2848_, v_a_2851_, v_b_2852_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___boxed(lean_object* v_upperBound_2855_, lean_object* v___x_2856_, lean_object* v_fst_2857_, lean_object* v___x_2858_, lean_object* v_inst_2859_, lean_object* v_R_2860_, lean_object* v_a_2861_, lean_object* v_b_2862_, lean_object* v_c_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8(v_upperBound_2855_, v___x_2856_, v_fst_2857_, v___x_2858_, v_inst_2859_, v_R_2860_, v_a_2861_, v_b_2862_, v_c_2863_);
lean_dec(v___x_2858_);
lean_dec_ref(v_fst_2857_);
lean_dec(v___x_2856_);
lean_dec(v_upperBound_2855_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9(lean_object* v_lsize_2865_, lean_object* v_rsize_2866_, lean_object* v_histogram_2867_, lean_object* v_index_2868_, lean_object* v_val_2869_){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(v_histogram_2867_, v_index_2868_, v_val_2869_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___boxed(lean_object* v_lsize_2871_, lean_object* v_rsize_2872_, lean_object* v_histogram_2873_, lean_object* v_index_2874_, lean_object* v_val_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9(v_lsize_2871_, v_rsize_2872_, v_histogram_2873_, v_index_2874_, v_val_2875_);
lean_dec(v_rsize_2872_);
lean_dec(v_lsize_2871_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10(lean_object* v_upperBound_2877_, lean_object* v_fst_2878_, lean_object* v___x_2879_, lean_object* v_fst_2880_, lean_object* v_inst_2881_, lean_object* v_R_2882_, lean_object* v_a_2883_, lean_object* v_b_2884_, lean_object* v_c_2885_){
_start:
{
lean_object* v___x_2886_; 
v___x_2886_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(v_upperBound_2877_, v_fst_2878_, v___x_2879_, v_fst_2880_, v_a_2883_, v_b_2884_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___boxed(lean_object* v_upperBound_2887_, lean_object* v_fst_2888_, lean_object* v___x_2889_, lean_object* v_fst_2890_, lean_object* v_inst_2891_, lean_object* v_R_2892_, lean_object* v_a_2893_, lean_object* v_b_2894_, lean_object* v_c_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10(v_upperBound_2887_, v_fst_2888_, v___x_2889_, v_fst_2890_, v_inst_2891_, v_R_2892_, v_a_2893_, v_b_2894_, v_c_2895_);
lean_dec_ref(v_fst_2890_);
lean_dec(v___x_2889_);
lean_dec_ref(v_fst_2888_);
lean_dec(v_upperBound_2887_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11(lean_object* v_00_u03b2_2897_, lean_object* v_m_2898_, lean_object* v_a_2899_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_m_2898_, v_a_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___boxed(lean_object* v_00_u03b2_2901_, lean_object* v_m_2902_, lean_object* v_a_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11(v_00_u03b2_2901_, v_m_2902_, v_a_2903_);
lean_dec_ref(v_a_2903_);
lean_dec_ref(v_m_2902_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12(lean_object* v_00_u03b2_2905_, lean_object* v_m_2906_, lean_object* v_a_2907_, lean_object* v_b_2908_){
_start:
{
lean_object* v___x_2909_; 
v___x_2909_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_m_2906_, v_a_2907_, v_b_2908_);
return v___x_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14(lean_object* v_inst_2910_, lean_object* v_R_2911_, lean_object* v_a_2912_, lean_object* v_b_2913_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v_a_2912_, v_b_2913_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20(lean_object* v_00_u03b2_2915_, lean_object* v_a_2916_, lean_object* v_x_2917_){
_start:
{
lean_object* v___x_2918_; 
v___x_2918_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(v_a_2916_, v_x_2917_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___boxed(lean_object* v_00_u03b2_2919_, lean_object* v_a_2920_, lean_object* v_x_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20(v_00_u03b2_2919_, v_a_2920_, v_x_2921_);
lean_dec(v_x_2921_);
lean_dec_ref(v_a_2920_);
return v_res_2922_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22(lean_object* v_00_u03b2_2923_, lean_object* v_a_2924_, lean_object* v_x_2925_){
_start:
{
uint8_t v___x_2926_; 
v___x_2926_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(v_a_2924_, v_x_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___boxed(lean_object* v_00_u03b2_2927_, lean_object* v_a_2928_, lean_object* v_x_2929_){
_start:
{
uint8_t v_res_2930_; lean_object* v_r_2931_; 
v_res_2930_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22(v_00_u03b2_2927_, v_a_2928_, v_x_2929_);
lean_dec(v_x_2929_);
lean_dec_ref(v_a_2928_);
v_r_2931_ = lean_box(v_res_2930_);
return v_r_2931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23(lean_object* v_00_u03b2_2932_, lean_object* v_data_2933_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23___redArg(v_data_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24(lean_object* v_00_u03b2_2935_, lean_object* v_a_2936_, lean_object* v_b_2937_, lean_object* v_x_2938_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(v_a_2936_, v_b_2937_, v_x_2938_);
return v___x_2939_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28(lean_object* v_00_u03b2_2940_, lean_object* v_i_2941_, lean_object* v_source_2942_, lean_object* v_target_2943_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28___redArg(v_i_2941_, v_source_2942_, v_target_2943_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_2945_, lean_object* v_x_2946_, lean_object* v_x_2947_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29___redArg(v_x_2946_, v_x_2947_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(lean_object* v_s_2949_){
_start:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = lean_string_data(v_s_2949_);
v___x_2951_ = lean_array_mk(v___x_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(lean_object* v_s_2952_, lean_object* v_s_x27_2953_){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2954_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_2952_);
v___x_2955_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_2953_);
v___x_2956_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_2954_, v___x_2955_);
v___x_2957_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_2956_);
lean_dec_ref(v___x_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(lean_object* v_s_2958_, lean_object* v_s_x27_2959_){
_start:
{
uint8_t v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; uint8_t v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2960_ = 1;
v___x_2961_ = lean_box(v___x_2960_);
v___x_2962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
lean_ctor_set(v___x_2962_, 1, v_s_2958_);
v___x_2963_ = 0;
v___x_2964_ = lean_box(v___x_2963_);
v___x_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
lean_ctor_set(v___x_2965_, 1, v_s_x27_2959_);
v___x_2966_ = lean_unsigned_to_nat(2u);
v___x_2967_ = lean_mk_empty_array_with_capacity(v___x_2966_);
v___x_2968_ = lean_array_push(v___x_2967_, v___x_2962_);
v___x_2969_ = lean_array_push(v___x_2968_, v___x_2965_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(lean_object* v_as_2970_, size_t v_i_2971_, size_t v_stop_2972_, lean_object* v_b_2973_){
_start:
{
lean_object* v___y_2975_; uint8_t v___x_2979_; 
v___x_2979_ = lean_usize_dec_eq(v_i_2971_, v_stop_2972_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; lean_object* v_fst_2981_; uint8_t v___x_2982_; uint8_t v___x_2983_; uint8_t v___x_2984_; 
v___x_2980_ = lean_array_uget_borrowed(v_as_2970_, v_i_2971_);
v_fst_2981_ = lean_ctor_get(v___x_2980_, 0);
v___x_2982_ = 2;
v___x_2983_ = lean_unbox(v_fst_2981_);
v___x_2984_ = l_Lean_Diff_instBEqAction_beq(v___x_2983_, v___x_2982_);
if (v___x_2984_ == 0)
{
lean_object* v___x_2985_; 
lean_inc(v___x_2980_);
v___x_2985_ = lean_array_push(v_b_2973_, v___x_2980_);
v___y_2975_ = v___x_2985_;
goto v___jp_2974_;
}
else
{
v___y_2975_ = v_b_2973_;
goto v___jp_2974_;
}
}
else
{
return v_b_2973_;
}
v___jp_2974_:
{
size_t v___x_2976_; size_t v___x_2977_; 
v___x_2976_ = ((size_t)1ULL);
v___x_2977_ = lean_usize_add(v_i_2971_, v___x_2976_);
v_i_2971_ = v___x_2977_;
v_b_2973_ = v___y_2975_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0___boxed(lean_object* v_as_2986_, lean_object* v_i_2987_, lean_object* v_stop_2988_, lean_object* v_b_2989_){
_start:
{
size_t v_i_boxed_2990_; size_t v_stop_boxed_2991_; lean_object* v_res_2992_; 
v_i_boxed_2990_ = lean_unbox_usize(v_i_2987_);
lean_dec(v_i_2987_);
v_stop_boxed_2991_ = lean_unbox_usize(v_stop_2988_);
lean_dec(v_stop_2988_);
v_res_2992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_as_2986_, v_i_boxed_2990_, v_stop_boxed_2991_, v_b_2989_);
lean_dec_ref(v_as_2986_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff(lean_object* v_s_2993_, lean_object* v_s_x27_2994_, uint8_t v_granularity_2995_){
_start:
{
lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; uint8_t v___y_3000_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; 
switch(v_granularity_2995_)
{
case 0:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___y_3042_; uint8_t v___x_3048_; 
v___x_3039_ = lean_string_length(v_s_2993_);
v___x_3040_ = lean_string_length(v_s_x27_2994_);
v___x_3048_ = lean_nat_dec_le(v___x_3039_, v___x_3040_);
if (v___x_3048_ == 0)
{
v___y_3042_ = v___x_3040_;
goto v___jp_3041_;
}
else
{
v___y_3042_ = v___x_3039_;
goto v___jp_3041_;
}
v___jp_3041_:
{
lean_object* v___x_3043_; lean_object* v_maxCharDiffDistance_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; uint8_t v___x_3047_; 
v___x_3043_ = lean_unsigned_to_nat(5u);
v_maxCharDiffDistance_3044_ = lean_nat_div(v___y_3042_, v___x_3043_);
v___x_3045_ = lean_unsigned_to_nat(1u);
v___x_3046_ = lean_nat_shiftr(v___y_3042_, v___x_3045_);
lean_dec(v___y_3042_);
v___x_3047_ = lean_nat_dec_le(v___x_3039_, v___x_3040_);
if (v___x_3047_ == 0)
{
v___y_3019_ = v_maxCharDiffDistance_3044_;
v___y_3020_ = v___x_3046_;
v___y_3021_ = v___x_3045_;
v___y_3022_ = v___x_3039_;
goto v___jp_3018_;
}
else
{
v___y_3019_ = v_maxCharDiffDistance_3044_;
v___y_3020_ = v___x_3046_;
v___y_3021_ = v___x_3045_;
v___y_3022_ = v___x_3040_;
goto v___jp_3018_;
}
}
}
case 1:
{
lean_object* v___x_3049_; 
v___x_3049_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(v_s_2993_, v_s_x27_2994_);
return v___x_3049_;
}
case 2:
{
lean_object* v___x_3050_; 
v___x_3050_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_2993_, v_s_x27_2994_);
lean_dec_ref(v_s_x27_2994_);
lean_dec_ref(v_s_2993_);
return v___x_3050_;
}
case 3:
{
lean_object* v___x_3051_; 
v___x_3051_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_2993_, v_s_x27_2994_);
return v___x_3051_;
}
default: 
{
uint8_t v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
lean_dec_ref(v_s_2993_);
v___x_3052_ = 0;
v___x_3053_ = lean_box(v___x_3052_);
v___x_3054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3053_);
lean_ctor_set(v___x_3054_, 1, v_s_x27_2994_);
v___x_3055_ = lean_unsigned_to_nat(1u);
v___x_3056_ = lean_mk_empty_array_with_capacity(v___x_3055_);
v___x_3057_ = lean_array_push(v___x_3056_, v___x_3054_);
return v___x_3057_;
}
}
v___jp_2996_:
{
if (v___y_3000_ == 0)
{
uint8_t v___x_3001_; 
lean_dec_ref(v___y_2999_);
v___x_3001_ = lean_nat_dec_le(v___y_2998_, v___y_2997_);
lean_dec(v___y_2997_);
lean_dec(v___y_2998_);
if (v___x_3001_ == 0)
{
lean_object* v___x_3002_; 
v___x_3002_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_2993_, v_s_x27_2994_);
return v___x_3002_;
}
else
{
lean_object* v___x_3003_; 
v___x_3003_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_2993_, v_s_x27_2994_);
lean_dec_ref(v_s_x27_2994_);
lean_dec_ref(v_s_2993_);
return v___x_3003_;
}
}
else
{
size_t v_sz_3004_; size_t v___x_3005_; lean_object* v___x_3006_; 
lean_dec(v___y_2998_);
lean_dec(v___y_2997_);
lean_dec_ref(v_s_x27_2994_);
lean_dec_ref(v_s_2993_);
v_sz_3004_ = lean_array_size(v___y_2999_);
v___x_3005_ = ((size_t)0ULL);
v___x_3006_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_3004_, v___x_3005_, v___y_2999_);
return v___x_3006_;
}
}
v___jp_3007_:
{
lean_object* v_approxEditDistance_3012_; lean_object* v_charArrDiff_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; uint8_t v___x_3016_; 
v_approxEditDistance_3012_ = lean_array_get_size(v___y_3011_);
lean_dec_ref(v___y_3011_);
v_charArrDiff_3013_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v___y_3010_);
lean_dec_ref(v___y_3010_);
v___x_3014_ = lean_array_get_size(v_charArrDiff_3013_);
v___x_3015_ = lean_unsigned_to_nat(3u);
v___x_3016_ = lean_nat_dec_le(v___x_3014_, v___x_3015_);
if (v___x_3016_ == 0)
{
uint8_t v___x_3017_; 
v___x_3017_ = lean_nat_dec_le(v_approxEditDistance_3012_, v___y_3009_);
lean_dec(v___y_3009_);
v___y_2997_ = v___y_3008_;
v___y_2998_ = v_approxEditDistance_3012_;
v___y_2999_ = v_charArrDiff_3013_;
v___y_3000_ = v___x_3017_;
goto v___jp_2996_;
}
else
{
lean_dec(v___y_3009_);
v___y_2997_ = v___y_3008_;
v___y_2998_ = v_approxEditDistance_3012_;
v___y_2999_ = v_charArrDiff_3013_;
v___y_3000_ = v___x_3016_;
goto v___jp_2996_;
}
}
v___jp_3018_:
{
lean_object* v___x_3023_; lean_object* v_maxWordDiffDistance_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v_charDiffRaw_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; uint8_t v___x_3031_; 
v___x_3023_ = lean_nat_shiftr(v___y_3022_, v___y_3021_);
lean_dec(v___y_3022_);
v_maxWordDiffDistance_3024_ = lean_nat_add(v___y_3020_, v___x_3023_);
lean_dec(v___x_3023_);
lean_dec(v___y_3020_);
lean_inc_ref(v_s_2993_);
v___x_3025_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_2993_);
lean_inc_ref(v_s_x27_2994_);
v___x_3026_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_2994_);
v_charDiffRaw_3027_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3025_, v___x_3026_);
v___x_3028_ = lean_unsigned_to_nat(0u);
v___x_3029_ = lean_array_get_size(v_charDiffRaw_3027_);
v___x_3030_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0));
v___x_3031_ = lean_nat_dec_lt(v___x_3028_, v___x_3029_);
if (v___x_3031_ == 0)
{
v___y_3008_ = v_maxWordDiffDistance_3024_;
v___y_3009_ = v___y_3019_;
v___y_3010_ = v_charDiffRaw_3027_;
v___y_3011_ = v___x_3030_;
goto v___jp_3007_;
}
else
{
uint8_t v___x_3032_; 
v___x_3032_ = lean_nat_dec_le(v___x_3029_, v___x_3029_);
if (v___x_3032_ == 0)
{
if (v___x_3031_ == 0)
{
v___y_3008_ = v_maxWordDiffDistance_3024_;
v___y_3009_ = v___y_3019_;
v___y_3010_ = v_charDiffRaw_3027_;
v___y_3011_ = v___x_3030_;
goto v___jp_3007_;
}
else
{
size_t v___x_3033_; size_t v___x_3034_; lean_object* v___x_3035_; 
v___x_3033_ = ((size_t)0ULL);
v___x_3034_ = lean_usize_of_nat(v___x_3029_);
v___x_3035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3027_, v___x_3033_, v___x_3034_, v___x_3030_);
v___y_3008_ = v_maxWordDiffDistance_3024_;
v___y_3009_ = v___y_3019_;
v___y_3010_ = v_charDiffRaw_3027_;
v___y_3011_ = v___x_3035_;
goto v___jp_3007_;
}
}
else
{
size_t v___x_3036_; size_t v___x_3037_; lean_object* v___x_3038_; 
v___x_3036_ = ((size_t)0ULL);
v___x_3037_ = lean_usize_of_nat(v___x_3029_);
v___x_3038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3027_, v___x_3036_, v___x_3037_, v___x_3030_);
v___y_3008_ = v_maxWordDiffDistance_3024_;
v___y_3009_ = v___y_3019_;
v___y_3010_ = v_charDiffRaw_3027_;
v___y_3011_ = v___x_3038_;
goto v___jp_3007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff___boxed(lean_object* v_s_3058_, lean_object* v_s_x27_3059_, lean_object* v_granularity_3060_){
_start:
{
uint8_t v_granularity_boxed_3061_; lean_object* v_res_3062_; 
v_granularity_boxed_3061_ = lean_unbox(v_granularity_3060_);
v_res_3062_ = l_Lean_Meta_Hint_readableDiff(v_s_3058_, v_s_x27_3059_, v_granularity_boxed_3061_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(lean_object* v_as_3063_, size_t v_i_3064_, size_t v_stop_3065_, lean_object* v_b_3066_){
_start:
{
uint8_t v___x_3067_; 
v___x_3067_ = lean_usize_dec_eq(v_i_3064_, v_stop_3065_);
if (v___x_3067_ == 0)
{
lean_object* v___x_3068_; lean_object* v_snd_3069_; lean_object* v___x_3070_; size_t v___x_3071_; size_t v___x_3072_; 
v___x_3068_ = lean_array_uget_borrowed(v_as_3063_, v_i_3064_);
v_snd_3069_ = lean_ctor_get(v___x_3068_, 1);
v___x_3070_ = lean_string_append(v_b_3066_, v_snd_3069_);
v___x_3071_ = ((size_t)1ULL);
v___x_3072_ = lean_usize_add(v_i_3064_, v___x_3071_);
v_i_3064_ = v___x_3072_;
v_b_3066_ = v___x_3070_;
goto _start;
}
else
{
return v_b_3066_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0___boxed(lean_object* v_as_3074_, lean_object* v_i_3075_, lean_object* v_stop_3076_, lean_object* v_b_3077_){
_start:
{
size_t v_i_boxed_3078_; size_t v_stop_boxed_3079_; lean_object* v_res_3080_; 
v_i_boxed_3078_ = lean_unbox_usize(v_i_3075_);
lean_dec(v_i_3075_);
v_stop_boxed_3079_ = lean_unbox_usize(v_stop_3076_);
lean_dec(v_stop_3076_);
v_res_3080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v_as_3074_, v_i_boxed_3078_, v_stop_boxed_3079_, v_b_3077_);
lean_dec_ref(v_as_3074_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(lean_object* v_t_3081_, lean_object* v___y_3082_){
_start:
{
lean_object* v___x_3084_; lean_object* v_infoState_3085_; uint8_t v_enabled_3086_; 
v___x_3084_ = lean_st_ref_get(v___y_3082_);
v_infoState_3085_ = lean_ctor_get(v___x_3084_, 7);
lean_inc_ref(v_infoState_3085_);
lean_dec(v___x_3084_);
v_enabled_3086_ = lean_ctor_get_uint8(v_infoState_3085_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3085_);
if (v_enabled_3086_ == 0)
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
lean_dec_ref(v_t_3081_);
v___x_3087_ = lean_box(0);
v___x_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
return v___x_3088_;
}
else
{
lean_object* v___x_3089_; lean_object* v_infoState_3090_; lean_object* v_env_3091_; lean_object* v_nextMacroScope_3092_; lean_object* v_ngen_3093_; lean_object* v_auxDeclNGen_3094_; lean_object* v_traceState_3095_; lean_object* v_cache_3096_; lean_object* v_messages_3097_; lean_object* v_snapshotTasks_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3120_; 
v___x_3089_ = lean_st_ref_take(v___y_3082_);
v_infoState_3090_ = lean_ctor_get(v___x_3089_, 7);
v_env_3091_ = lean_ctor_get(v___x_3089_, 0);
v_nextMacroScope_3092_ = lean_ctor_get(v___x_3089_, 1);
v_ngen_3093_ = lean_ctor_get(v___x_3089_, 2);
v_auxDeclNGen_3094_ = lean_ctor_get(v___x_3089_, 3);
v_traceState_3095_ = lean_ctor_get(v___x_3089_, 4);
v_cache_3096_ = lean_ctor_get(v___x_3089_, 5);
v_messages_3097_ = lean_ctor_get(v___x_3089_, 6);
v_snapshotTasks_3098_ = lean_ctor_get(v___x_3089_, 8);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3100_ = v___x_3089_;
v_isShared_3101_ = v_isSharedCheck_3120_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_snapshotTasks_3098_);
lean_inc(v_infoState_3090_);
lean_inc(v_messages_3097_);
lean_inc(v_cache_3096_);
lean_inc(v_traceState_3095_);
lean_inc(v_auxDeclNGen_3094_);
lean_inc(v_ngen_3093_);
lean_inc(v_nextMacroScope_3092_);
lean_inc(v_env_3091_);
lean_dec(v___x_3089_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3120_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
uint8_t v_enabled_3102_; lean_object* v_assignment_3103_; lean_object* v_lazyAssignment_3104_; lean_object* v_trees_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3119_; 
v_enabled_3102_ = lean_ctor_get_uint8(v_infoState_3090_, sizeof(void*)*3);
v_assignment_3103_ = lean_ctor_get(v_infoState_3090_, 0);
v_lazyAssignment_3104_ = lean_ctor_get(v_infoState_3090_, 1);
v_trees_3105_ = lean_ctor_get(v_infoState_3090_, 2);
v_isSharedCheck_3119_ = !lean_is_exclusive(v_infoState_3090_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3107_ = v_infoState_3090_;
v_isShared_3108_ = v_isSharedCheck_3119_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_trees_3105_);
lean_inc(v_lazyAssignment_3104_);
lean_inc(v_assignment_3103_);
lean_dec(v_infoState_3090_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3119_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3109_; lean_object* v___x_3111_; 
v___x_3109_ = l_Lean_PersistentArray_push___redArg(v_trees_3105_, v_t_3081_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 2, v___x_3109_);
v___x_3111_ = v___x_3107_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_assignment_3103_);
lean_ctor_set(v_reuseFailAlloc_3118_, 1, v_lazyAssignment_3104_);
lean_ctor_set(v_reuseFailAlloc_3118_, 2, v___x_3109_);
lean_ctor_set_uint8(v_reuseFailAlloc_3118_, sizeof(void*)*3, v_enabled_3102_);
v___x_3111_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
lean_object* v___x_3113_; 
if (v_isShared_3101_ == 0)
{
lean_ctor_set(v___x_3100_, 7, v___x_3111_);
v___x_3113_ = v___x_3100_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_env_3091_);
lean_ctor_set(v_reuseFailAlloc_3117_, 1, v_nextMacroScope_3092_);
lean_ctor_set(v_reuseFailAlloc_3117_, 2, v_ngen_3093_);
lean_ctor_set(v_reuseFailAlloc_3117_, 3, v_auxDeclNGen_3094_);
lean_ctor_set(v_reuseFailAlloc_3117_, 4, v_traceState_3095_);
lean_ctor_set(v_reuseFailAlloc_3117_, 5, v_cache_3096_);
lean_ctor_set(v_reuseFailAlloc_3117_, 6, v_messages_3097_);
lean_ctor_set(v_reuseFailAlloc_3117_, 7, v___x_3111_);
lean_ctor_set(v_reuseFailAlloc_3117_, 8, v_snapshotTasks_3098_);
v___x_3113_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3114_ = lean_st_ref_set(v___y_3082_, v___x_3113_);
v___x_3115_ = lean_box(0);
v___x_3116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3115_);
return v___x_3116_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg___boxed(lean_object* v_t_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v_res_3124_; 
v_res_3124_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3121_, v___y_3122_);
lean_dec(v___y_3122_);
return v_res_3124_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3125_ = lean_unsigned_to_nat(32u);
v___x_3126_ = lean_mk_empty_array_with_capacity(v___x_3125_);
v___x_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3127_, 0, v___x_3126_);
return v___x_3127_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1(void){
_start:
{
size_t v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; 
v___x_3128_ = ((size_t)5ULL);
v___x_3129_ = lean_unsigned_to_nat(0u);
v___x_3130_ = lean_unsigned_to_nat(32u);
v___x_3131_ = lean_mk_empty_array_with_capacity(v___x_3130_);
v___x_3132_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0);
v___x_3133_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
lean_ctor_set(v___x_3133_, 1, v___x_3131_);
lean_ctor_set(v___x_3133_, 2, v___x_3129_);
lean_ctor_set(v___x_3133_, 3, v___x_3129_);
lean_ctor_set_usize(v___x_3133_, 4, v___x_3128_);
return v___x_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(lean_object* v_t_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v___x_3138_; lean_object* v_infoState_3139_; uint8_t v_enabled_3140_; 
v___x_3138_ = lean_st_ref_get(v___y_3136_);
v_infoState_3139_ = lean_ctor_get(v___x_3138_, 7);
lean_inc_ref(v_infoState_3139_);
lean_dec(v___x_3138_);
v_enabled_3140_ = lean_ctor_get_uint8(v_infoState_3139_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3139_);
if (v_enabled_3140_ == 0)
{
lean_object* v___x_3141_; lean_object* v___x_3142_; 
lean_dec_ref(v_t_3134_);
v___x_3141_ = lean_box(0);
v___x_3142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3141_);
return v___x_3142_;
}
else
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3143_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1);
v___x_3144_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3144_, 0, v_t_3134_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
v___x_3145_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v___x_3144_, v___y_3136_);
return v___x_3145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___boxed(lean_object* v_t_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v_t_3146_, v___y_3147_, v___y_3148_);
lean_dec(v___y_3148_);
lean_dec_ref(v___y_3147_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0(lean_object* v___x_3151_, lean_object* v___y_3152_){
_start:
{
lean_object* v___x_3153_; 
v___x_3153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3153_, 0, v___x_3151_);
lean_ctor_set(v___x_3153_, 1, v___y_3152_);
return v___x_3153_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3155_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__0));
v___x_3156_ = l_Lean_stringToMessageData(v___x_3155_);
return v___x_3156_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3158_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__2));
v___x_3159_ = l_Lean_stringToMessageData(v___x_3158_);
return v___x_3159_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29(void){
_start:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3208_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__28));
v___x_3209_ = l_Lean_Json_mkObj(v___x_3208_);
return v___x_3209_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30(void){
_start:
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3210_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29);
v___x_3211_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__19));
v___x_3212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
lean_ctor_set(v___x_3212_, 1, v___x_3210_);
return v___x_3212_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31(void){
_start:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3213_ = lean_box(0);
v___x_3214_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30);
v___x_3215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3214_);
lean_ctor_set(v___x_3215_, 1, v___x_3213_);
return v___x_3215_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33(void){
_start:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3218_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__32));
v___x_3219_ = l_Lean_MessageData_ofFormat(v___x_3218_);
return v___x_3219_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35(void){
_start:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3221_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__34));
v___x_3222_ = l_Lean_stringToMessageData(v___x_3221_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(lean_object* v_suggestions_3224_, uint8_t v_forceList_3225_, lean_object* v_codeActionPrefix_x3f_3226_, lean_object* v_ref_3227_, lean_object* v_as_3228_, size_t v_sz_3229_, size_t v_i_3230_, lean_object* v_b_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v_a_3236_; lean_object* v___y_3241_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3252_; lean_object* v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; uint8_t v___x_3280_; 
v___x_3280_ = lean_usize_dec_lt(v_i_3230_, v_sz_3229_);
if (v___x_3280_ == 0)
{
lean_object* v___x_3281_; 
lean_dec(v_ref_3227_);
lean_dec(v_codeActionPrefix_x3f_3226_);
v___x_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3281_, 0, v_b_3231_);
return v___x_3281_;
}
else
{
lean_object* v_a_3282_; lean_object* v_span_x3f_3283_; lean_object* v___x_3284_; lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; uint8_t v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; uint8_t v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; uint8_t v___y_3372_; lean_object* v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; uint8_t v___y_3379_; lean_object* v___y_3380_; uint8_t v___y_3381_; lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v_postInfo_x3f_3389_; lean_object* v___y_3390_; uint8_t v___y_3391_; uint8_t v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v___y_3399_; uint8_t v___y_3400_; uint8_t v___y_3401_; lean_object* v_edits_3402_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v_stop_3414_; uint8_t v___y_3415_; uint8_t v___y_3416_; lean_object* v_edits_3417_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; uint8_t v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; uint8_t v___y_3434_; lean_object* v_edits_3435_; lean_object* v___y_3436_; lean_object* v___x_3460_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; uint8_t v___y_3467_; uint8_t v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; uint8_t v___y_3512_; lean_object* v___y_3513_; uint8_t v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3525_; 
v_a_3282_ = lean_array_uget_borrowed(v_as_3228_, v_i_3230_);
v_span_x3f_3283_ = lean_ctor_get(v_a_3282_, 1);
v___x_3284_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_3460_ = l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_;
if (lean_obj_tag(v_span_x3f_3283_) == 0)
{
lean_inc(v_ref_3227_);
v___y_3525_ = v_ref_3227_;
goto v___jp_3524_;
}
else
{
lean_object* v_val_3546_; 
v_val_3546_ = lean_ctor_get(v_span_x3f_3283_, 0);
lean_inc(v_val_3546_);
v___y_3525_ = v_val_3546_;
goto v___jp_3524_;
}
v___jp_3285_:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___f_3306_; 
lean_inc_ref(v___y_3289_);
v___x_3292_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson(v___y_3289_);
v___x_3293_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__9));
v___x_3294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
lean_ctor_set(v___x_3294_, 1, v___x_3292_);
v___x_3295_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3296_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3296_, 0, v___y_3287_);
v___x_3297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3295_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
v___x_3298_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3299_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3286_);
v___x_3300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3298_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
v___x_3301_ = lean_box(0);
v___x_3302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3300_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
v___x_3303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3297_);
lean_ctor_set(v___x_3303_, 1, v___x_3302_);
v___x_3304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3294_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
v___x_3305_ = l_Lean_Json_mkObj(v___x_3304_);
lean_dec_ref(v___x_3304_);
v___f_3306_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3306_, 0, v___x_3305_);
if (v___y_3290_ == 0)
{
lean_object* v___x_3307_; 
v___x_3307_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString(v___y_3289_);
v___y_3260_ = v___f_3306_;
v___y_3261_ = v___y_3288_;
v___y_3262_ = v___y_3291_;
v___y_3263_ = v___x_3307_;
goto v___jp_3259_;
}
else
{
lean_object* v___x_3308_; lean_object* v___x_3309_; uint8_t v___x_3310_; 
v___x_3308_ = lean_unsigned_to_nat(0u);
v___x_3309_ = lean_array_get_size(v___y_3289_);
v___x_3310_ = lean_nat_dec_lt(v___x_3308_, v___x_3309_);
if (v___x_3310_ == 0)
{
lean_dec_ref(v___y_3289_);
v___y_3260_ = v___f_3306_;
v___y_3261_ = v___y_3288_;
v___y_3262_ = v___y_3291_;
v___y_3263_ = v___x_3284_;
goto v___jp_3259_;
}
else
{
uint8_t v___x_3311_; 
v___x_3311_ = lean_nat_dec_le(v___x_3309_, v___x_3309_);
if (v___x_3311_ == 0)
{
if (v___x_3310_ == 0)
{
lean_dec_ref(v___y_3289_);
v___y_3260_ = v___f_3306_;
v___y_3261_ = v___y_3288_;
v___y_3262_ = v___y_3291_;
v___y_3263_ = v___x_3284_;
goto v___jp_3259_;
}
else
{
size_t v___x_3312_; size_t v___x_3313_; lean_object* v___x_3314_; 
v___x_3312_ = ((size_t)0ULL);
v___x_3313_ = lean_usize_of_nat(v___x_3309_);
v___x_3314_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3289_, v___x_3312_, v___x_3313_, v___x_3284_);
lean_dec_ref(v___y_3289_);
v___y_3260_ = v___f_3306_;
v___y_3261_ = v___y_3288_;
v___y_3262_ = v___y_3291_;
v___y_3263_ = v___x_3314_;
goto v___jp_3259_;
}
}
else
{
size_t v___x_3315_; size_t v___x_3316_; lean_object* v___x_3317_; 
v___x_3315_ = ((size_t)0ULL);
v___x_3316_ = lean_usize_of_nat(v___x_3309_);
v___x_3317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3289_, v___x_3315_, v___x_3316_, v___x_3284_);
lean_dec_ref(v___y_3289_);
v___y_3260_ = v___f_3306_;
v___y_3261_ = v___y_3288_;
v___y_3262_ = v___y_3291_;
v___y_3263_ = v___x_3317_;
goto v___jp_3259_;
}
}
}
}
v___jp_3318_:
{
if (lean_obj_tag(v___y_3320_) == 0)
{
lean_object* v___x_3327_; uint64_t v_javascriptHash_3328_; lean_object* v_suggestion_3329_; lean_object* v_messageData_x3f_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___f_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
lean_dec_ref(v___y_3324_);
v___x_3327_ = l_Lean_Meta_Hint_textInsertionWidget;
v_javascriptHash_3328_ = lean_ctor_get_uint64(v___x_3327_, sizeof(void*)*1);
v_suggestion_3329_ = lean_ctor_get(v___y_3322_, 0);
lean_inc_ref(v_suggestion_3329_);
v_messageData_x3f_3330_ = lean_ctor_get(v___y_3322_, 4);
lean_inc(v_messageData_x3f_3330_);
lean_dec_ref(v___y_3322_);
v___x_3331_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18));
v___x_3332_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3333_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3319_);
v___x_3334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3332_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
v___x_3335_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3336_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3336_, 0, v___y_3321_);
v___x_3337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___x_3335_);
lean_ctor_set(v___x_3337_, 1, v___x_3336_);
v___x_3338_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31);
v___x_3339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3337_);
lean_ctor_set(v___x_3339_, 1, v___x_3338_);
v___x_3340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3334_);
lean_ctor_set(v___x_3340_, 1, v___x_3339_);
v___x_3341_ = l_Lean_Json_mkObj(v___x_3340_);
lean_dec_ref(v___x_3340_);
v___f_3342_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3342_, 0, v___x_3341_);
v___x_3343_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3343_, 0, v___x_3331_);
lean_ctor_set(v___x_3343_, 1, v___f_3342_);
lean_ctor_set_uint64(v___x_3343_, sizeof(void*)*2, v_javascriptHash_3328_);
v___x_3344_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33);
v___x_3345_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3343_);
lean_ctor_set(v___x_3345_, 1, v___x_3344_);
v___x_3346_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
lean_ctor_set(v___x_3347_, 1, v___x_3345_);
v___x_3348_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35);
v___x_3349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3347_);
lean_ctor_set(v___x_3349_, 1, v___x_3348_);
v___x_3350_ = l_Lean_stringToMessageData(v___y_3326_);
v___x_3351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3349_);
lean_ctor_set(v___x_3351_, 1, v___x_3350_);
if (lean_obj_tag(v_messageData_x3f_3330_) == 0)
{
if (lean_obj_tag(v_suggestion_3329_) == 0)
{
lean_object* v_a_3352_; lean_object* v___x_3353_; 
v_a_3352_ = lean_ctor_get(v_suggestion_3329_, 1);
lean_inc(v_a_3352_);
lean_dec_ref(v_suggestion_3329_);
v___x_3353_ = l_Lean_MessageData_ofSyntax(v_a_3352_);
v___y_3245_ = v___y_3323_;
v___y_3246_ = v___x_3351_;
v___y_3247_ = v___x_3353_;
goto v___jp_3244_;
}
else
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3362_; 
v_a_3354_ = lean_ctor_get(v_suggestion_3329_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v_suggestion_3329_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3356_ = v_suggestion_3329_;
v_isShared_3357_ = v_isSharedCheck_3362_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v_suggestion_3329_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3362_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3359_; 
if (v_isShared_3357_ == 0)
{
lean_ctor_set_tag(v___x_3356_, 3);
v___x_3359_ = v___x_3356_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_a_3354_);
v___x_3359_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
lean_object* v___x_3360_; 
v___x_3360_ = l_Lean_MessageData_ofFormat(v___x_3359_);
v___y_3245_ = v___y_3323_;
v___y_3246_ = v___x_3351_;
v___y_3247_ = v___x_3360_;
goto v___jp_3244_;
}
}
}
}
else
{
lean_object* v_val_3363_; 
lean_dec_ref(v_suggestion_3329_);
v_val_3363_ = lean_ctor_get(v_messageData_x3f_3330_, 0);
lean_inc(v_val_3363_);
lean_dec_ref(v_messageData_x3f_3330_);
v___y_3245_ = v___y_3323_;
v___y_3246_ = v___x_3351_;
v___y_3247_ = v_val_3363_;
goto v___jp_3244_;
}
}
else
{
lean_dec_ref(v___y_3320_);
lean_dec_ref(v___y_3322_);
v___y_3286_ = v___y_3319_;
v___y_3287_ = v___y_3321_;
v___y_3288_ = v___y_3323_;
v___y_3289_ = v___y_3324_;
v___y_3290_ = v___y_3325_;
v___y_3291_ = v___y_3326_;
goto v___jp_3285_;
}
}
v___jp_3364_:
{
if (v___y_3372_ == 0)
{
lean_object* v_messageData_x3f_3373_; 
v_messageData_x3f_3373_ = lean_ctor_get(v___y_3368_, 4);
if (lean_obj_tag(v_messageData_x3f_3373_) == 0)
{
lean_dec_ref(v___y_3368_);
lean_dec(v___y_3366_);
v___y_3286_ = v___y_3365_;
v___y_3287_ = v___y_3367_;
v___y_3288_ = v___y_3369_;
v___y_3289_ = v___y_3370_;
v___y_3290_ = v___y_3372_;
v___y_3291_ = v___y_3371_;
goto v___jp_3285_;
}
else
{
v___y_3319_ = v___y_3365_;
v___y_3320_ = v___y_3366_;
v___y_3321_ = v___y_3367_;
v___y_3322_ = v___y_3368_;
v___y_3323_ = v___y_3369_;
v___y_3324_ = v___y_3370_;
v___y_3325_ = v___y_3372_;
v___y_3326_ = v___y_3371_;
goto v___jp_3318_;
}
}
else
{
v___y_3319_ = v___y_3365_;
v___y_3320_ = v___y_3366_;
v___y_3321_ = v___y_3367_;
v___y_3322_ = v___y_3368_;
v___y_3323_ = v___y_3369_;
v___y_3324_ = v___y_3370_;
v___y_3325_ = v___y_3372_;
v___y_3326_ = v___y_3371_;
goto v___jp_3318_;
}
}
v___jp_3374_:
{
if (v___y_3379_ == 4)
{
v___y_3365_ = v___y_3375_;
v___y_3366_ = v___y_3376_;
v___y_3367_ = v___y_3377_;
v___y_3368_ = v___y_3378_;
v___y_3369_ = v___y_3383_;
v___y_3370_ = v___y_3380_;
v___y_3371_ = v___y_3382_;
v___y_3372_ = v___x_3280_;
goto v___jp_3364_;
}
else
{
v___y_3365_ = v___y_3375_;
v___y_3366_ = v___y_3376_;
v___y_3367_ = v___y_3377_;
v___y_3368_ = v___y_3378_;
v___y_3369_ = v___y_3383_;
v___y_3370_ = v___y_3380_;
v___y_3371_ = v___y_3382_;
v___y_3372_ = v___y_3381_;
goto v___jp_3364_;
}
}
v___jp_3384_:
{
if (lean_obj_tag(v_postInfo_x3f_3389_) == 0)
{
v___y_3375_ = v___y_3385_;
v___y_3376_ = v___y_3386_;
v___y_3377_ = v___y_3387_;
v___y_3378_ = v___y_3388_;
v___y_3379_ = v___y_3391_;
v___y_3380_ = v___y_3390_;
v___y_3381_ = v___y_3392_;
v___y_3382_ = v___y_3393_;
v___y_3383_ = v___x_3284_;
goto v___jp_3374_;
}
else
{
lean_object* v_val_3394_; 
v_val_3394_ = lean_ctor_get(v_postInfo_x3f_3389_, 0);
lean_inc(v_val_3394_);
lean_dec_ref(v_postInfo_x3f_3389_);
v___y_3375_ = v___y_3385_;
v___y_3376_ = v___y_3386_;
v___y_3377_ = v___y_3387_;
v___y_3378_ = v___y_3388_;
v___y_3379_ = v___y_3391_;
v___y_3380_ = v___y_3390_;
v___y_3381_ = v___y_3392_;
v___y_3382_ = v___y_3393_;
v___y_3383_ = v_val_3394_;
goto v___jp_3374_;
}
}
v___jp_3395_:
{
lean_object* v_preInfo_x3f_3403_; 
v_preInfo_x3f_3403_ = lean_ctor_get(v___y_3399_, 1);
if (lean_obj_tag(v_preInfo_x3f_3403_) == 0)
{
lean_object* v_postInfo_x3f_3404_; 
v_postInfo_x3f_3404_ = lean_ctor_get(v___y_3399_, 2);
lean_inc(v_postInfo_x3f_3404_);
v___y_3385_ = v___y_3396_;
v___y_3386_ = v___y_3397_;
v___y_3387_ = v___y_3398_;
v___y_3388_ = v___y_3399_;
v_postInfo_x3f_3389_ = v_postInfo_x3f_3404_;
v___y_3390_ = v_edits_3402_;
v___y_3391_ = v___y_3400_;
v___y_3392_ = v___y_3401_;
v___y_3393_ = v___x_3284_;
goto v___jp_3384_;
}
else
{
lean_object* v_postInfo_x3f_3405_; lean_object* v_val_3406_; 
v_postInfo_x3f_3405_ = lean_ctor_get(v___y_3399_, 2);
lean_inc(v_postInfo_x3f_3405_);
v_val_3406_ = lean_ctor_get(v_preInfo_x3f_3403_, 0);
lean_inc(v_val_3406_);
v___y_3385_ = v___y_3396_;
v___y_3386_ = v___y_3397_;
v___y_3387_ = v___y_3398_;
v___y_3388_ = v___y_3399_;
v_postInfo_x3f_3389_ = v_postInfo_x3f_3405_;
v___y_3390_ = v_edits_3402_;
v___y_3391_ = v___y_3400_;
v___y_3392_ = v___y_3401_;
v___y_3393_ = v_val_3406_;
goto v___jp_3384_;
}
}
v___jp_3407_:
{
uint8_t v___x_3418_; 
v___x_3418_ = lean_nat_dec_lt(v___y_3409_, v_stop_3414_);
if (v___x_3418_ == 0)
{
lean_dec(v_stop_3414_);
lean_dec(v___y_3409_);
v___y_3396_ = v___y_3408_;
v___y_3397_ = v___y_3410_;
v___y_3398_ = v___y_3411_;
v___y_3399_ = v___y_3412_;
v___y_3400_ = v___y_3415_;
v___y_3401_ = v___y_3416_;
v_edits_3402_ = v_edits_3417_;
goto v___jp_3395_;
}
else
{
lean_object* v_source_3419_; uint8_t v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v_source_3419_ = lean_ctor_get(v___y_3413_, 0);
v___x_3420_ = 2;
v___x_3421_ = lean_string_utf8_extract(v_source_3419_, v___y_3409_, v_stop_3414_);
lean_dec(v_stop_3414_);
lean_dec(v___y_3409_);
v___x_3422_ = lean_box(v___x_3420_);
v___x_3423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3422_);
lean_ctor_set(v___x_3423_, 1, v___x_3421_);
v___x_3424_ = lean_array_push(v_edits_3417_, v___x_3423_);
v___y_3396_ = v___y_3408_;
v___y_3397_ = v___y_3410_;
v___y_3398_ = v___y_3411_;
v___y_3399_ = v___y_3412_;
v___y_3400_ = v___y_3415_;
v___y_3401_ = v___y_3416_;
v_edits_3402_ = v___x_3424_;
goto v___jp_3395_;
}
}
v___jp_3425_:
{
if (lean_obj_tag(v___y_3428_) == 0)
{
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec(v___y_3426_);
v___y_3396_ = v___y_3427_;
v___y_3397_ = v___y_3428_;
v___y_3398_ = v___y_3429_;
v___y_3399_ = v___y_3430_;
v___y_3400_ = v___y_3431_;
v___y_3401_ = v___y_3434_;
v_edits_3402_ = v_edits_3435_;
goto v___jp_3395_;
}
else
{
lean_object* v_val_3437_; lean_object* v___x_3438_; 
v_val_3437_ = lean_ctor_get(v___y_3428_, 0);
v___x_3438_ = l_Lean_Syntax_getRange_x3f(v_val_3437_, v___y_3434_);
if (lean_obj_tag(v___x_3438_) == 1)
{
lean_object* v_val_3439_; uint8_t v___x_3440_; 
v_val_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_val_3439_);
lean_dec_ref(v___x_3438_);
v___x_3440_ = l_Lean_Syntax_Range_includes(v_val_3439_, v___y_3433_, v___y_3434_, v___y_3434_);
lean_dec_ref(v___y_3433_);
if (v___x_3440_ == 0)
{
lean_dec(v_val_3439_);
lean_dec(v___y_3432_);
lean_dec(v___y_3426_);
v___y_3396_ = v___y_3427_;
v___y_3397_ = v___y_3428_;
v___y_3398_ = v___y_3429_;
v___y_3399_ = v___y_3430_;
v___y_3400_ = v___y_3431_;
v___y_3401_ = v___y_3434_;
v_edits_3402_ = v_edits_3435_;
goto v___jp_3395_;
}
else
{
lean_object* v_fileMap_3441_; lean_object* v_start_3442_; lean_object* v_stop_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3459_; 
v_fileMap_3441_ = lean_ctor_get(v___y_3436_, 1);
v_start_3442_ = lean_ctor_get(v_val_3439_, 0);
v_stop_3443_ = lean_ctor_get(v_val_3439_, 1);
v_isSharedCheck_3459_ = !lean_is_exclusive(v_val_3439_);
if (v_isSharedCheck_3459_ == 0)
{
v___x_3445_ = v_val_3439_;
v_isShared_3446_ = v_isSharedCheck_3459_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_stop_3443_);
lean_inc(v_start_3442_);
lean_dec(v_val_3439_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3459_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
uint8_t v___x_3447_; 
v___x_3447_ = lean_nat_dec_lt(v_start_3442_, v___y_3432_);
if (v___x_3447_ == 0)
{
lean_del_object(v___x_3445_);
lean_dec(v_start_3442_);
lean_dec(v___y_3432_);
v___y_3408_ = v___y_3427_;
v___y_3409_ = v___y_3426_;
v___y_3410_ = v___y_3428_;
v___y_3411_ = v___y_3429_;
v___y_3412_ = v___y_3430_;
v___y_3413_ = v_fileMap_3441_;
v_stop_3414_ = v_stop_3443_;
v___y_3415_ = v___y_3431_;
v___y_3416_ = v___y_3434_;
v_edits_3417_ = v_edits_3435_;
goto v___jp_3407_;
}
else
{
lean_object* v_source_3448_; uint8_t v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3453_; 
v_source_3448_ = lean_ctor_get(v_fileMap_3441_, 0);
v___x_3449_ = 2;
v___x_3450_ = lean_string_utf8_extract(v_source_3448_, v_start_3442_, v___y_3432_);
lean_dec(v___y_3432_);
lean_dec(v_start_3442_);
v___x_3451_ = lean_box(v___x_3449_);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 1, v___x_3450_);
lean_ctor_set(v___x_3445_, 0, v___x_3451_);
v___x_3453_ = v___x_3445_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3458_; 
v_reuseFailAlloc_3458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3458_, 0, v___x_3451_);
lean_ctor_set(v_reuseFailAlloc_3458_, 1, v___x_3450_);
v___x_3453_ = v_reuseFailAlloc_3458_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3454_ = lean_unsigned_to_nat(1u);
v___x_3455_ = lean_mk_empty_array_with_capacity(v___x_3454_);
v___x_3456_ = lean_array_push(v___x_3455_, v___x_3453_);
v___x_3457_ = l_Array_append___redArg(v___x_3456_, v_edits_3435_);
lean_dec_ref(v_edits_3435_);
v___y_3408_ = v___y_3427_;
v___y_3409_ = v___y_3426_;
v___y_3410_ = v___y_3428_;
v___y_3411_ = v___y_3429_;
v___y_3412_ = v___y_3430_;
v___y_3413_ = v_fileMap_3441_;
v_stop_3414_ = v_stop_3443_;
v___y_3415_ = v___y_3431_;
v___y_3416_ = v___y_3434_;
v_edits_3417_ = v___x_3457_;
goto v___jp_3407_;
}
}
}
}
}
else
{
lean_dec(v___x_3438_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec(v___y_3426_);
v___y_3396_ = v___y_3427_;
v___y_3397_ = v___y_3428_;
v___y_3398_ = v___y_3429_;
v___y_3399_ = v___y_3430_;
v___y_3400_ = v___y_3431_;
v___y_3401_ = v___y_3434_;
v_edits_3402_ = v_edits_3435_;
goto v___jp_3395_;
}
}
}
v___jp_3461_:
{
lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
lean_inc_ref(v___y_3466_);
v___x_3472_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3472_, 0, v___y_3465_);
lean_ctor_set(v___x_3472_, 1, v___y_3471_);
lean_ctor_set(v___x_3472_, 2, v___y_3466_);
v___x_3473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3473_, 0, v___x_3460_);
lean_ctor_set(v___x_3473_, 1, v___x_3472_);
v___x_3474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___y_3470_);
lean_ctor_set(v___x_3474_, 1, v___x_3473_);
v___x_3475_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_3475_, 0, v___x_3474_);
v___x_3476_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v___x_3475_, v___y_3232_, v___y_3233_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v_messageData_x3f_3477_; 
lean_dec_ref(v___x_3476_);
v_messageData_x3f_3477_ = lean_ctor_get(v___y_3466_, 4);
if (lean_obj_tag(v_messageData_x3f_3477_) == 1)
{
lean_object* v_start_3478_; lean_object* v_stop_3479_; lean_object* v_val_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; uint8_t v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; 
v_start_3478_ = lean_ctor_get(v___y_3469_, 0);
lean_inc(v_start_3478_);
v_stop_3479_ = lean_ctor_get(v___y_3469_, 1);
lean_inc(v_stop_3479_);
v_val_3480_ = lean_ctor_get(v_messageData_x3f_3477_, 0);
v___x_3481_ = lean_box(0);
lean_inc(v_val_3480_);
v___x_3482_ = l_Lean_MessageData_format(v_val_3480_, v___x_3481_);
v___x_3483_ = 0;
v___x_3484_ = l_Std_Format_defWidth;
v___x_3485_ = lean_unsigned_to_nat(0u);
v___x_3486_ = l_Std_Format_pretty(v___x_3482_, v___x_3484_, v___x_3485_, v___x_3485_);
v___x_3487_ = lean_box(v___x_3483_);
v___x_3488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
lean_ctor_set(v___x_3488_, 1, v___x_3486_);
v___x_3489_ = lean_unsigned_to_nat(1u);
v___x_3490_ = lean_mk_empty_array_with_capacity(v___x_3489_);
v___x_3491_ = lean_array_push(v___x_3490_, v___x_3488_);
v___y_3426_ = v_stop_3479_;
v___y_3427_ = v___y_3462_;
v___y_3428_ = v___y_3463_;
v___y_3429_ = v___y_3464_;
v___y_3430_ = v___y_3466_;
v___y_3431_ = v___y_3467_;
v___y_3432_ = v_start_3478_;
v___y_3433_ = v___y_3469_;
v___y_3434_ = v___y_3468_;
v_edits_3435_ = v___x_3491_;
v___y_3436_ = v___y_3232_;
goto v___jp_3425_;
}
else
{
lean_object* v_fileMap_3492_; lean_object* v_start_3493_; lean_object* v_stop_3494_; lean_object* v_source_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v_fileMap_3492_ = lean_ctor_get(v___y_3232_, 1);
v_start_3493_ = lean_ctor_get(v___y_3469_, 0);
lean_inc(v_start_3493_);
v_stop_3494_ = lean_ctor_get(v___y_3469_, 1);
lean_inc(v_stop_3494_);
v_source_3495_ = lean_ctor_get(v_fileMap_3492_, 0);
v___x_3496_ = lean_string_utf8_extract(v_source_3495_, v_start_3493_, v_stop_3494_);
lean_inc_ref(v___y_3464_);
v___x_3497_ = l_Lean_Meta_Hint_readableDiff(v___x_3496_, v___y_3464_, v___y_3467_);
v___y_3426_ = v_stop_3494_;
v___y_3427_ = v___y_3462_;
v___y_3428_ = v___y_3463_;
v___y_3429_ = v___y_3464_;
v___y_3430_ = v___y_3466_;
v___y_3431_ = v___y_3467_;
v___y_3432_ = v_start_3493_;
v___y_3433_ = v___y_3469_;
v___y_3434_ = v___y_3468_;
v_edits_3435_ = v___x_3497_;
v___y_3436_ = v___y_3232_;
goto v___jp_3425_;
}
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
lean_dec_ref(v___y_3469_);
lean_dec_ref(v___y_3466_);
lean_dec_ref(v___y_3464_);
lean_dec(v___y_3463_);
lean_dec_ref(v___y_3462_);
lean_dec_ref(v_b_3231_);
lean_dec(v_ref_3227_);
lean_dec(v_codeActionPrefix_x3f_3226_);
v_a_3498_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3476_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3476_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
v___jp_3506_:
{
lean_object* v_toCodeActionTitle_x3f_3516_; lean_object* v___x_3517_; 
v_toCodeActionTitle_x3f_3516_ = lean_ctor_get(v___y_3511_, 5);
v___x_3517_ = l_Lean_Syntax_ofRange(v___y_3515_, v___x_3280_);
if (lean_obj_tag(v_toCodeActionTitle_x3f_3516_) == 0)
{
if (lean_obj_tag(v_codeActionPrefix_x3f_3226_) == 0)
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3518_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__36));
v___x_3519_ = lean_string_append(v___x_3518_, v___y_3510_);
v___y_3462_ = v___y_3507_;
v___y_3463_ = v___y_3508_;
v___y_3464_ = v___y_3510_;
v___y_3465_ = v___y_3509_;
v___y_3466_ = v___y_3511_;
v___y_3467_ = v___y_3512_;
v___y_3468_ = v___y_3514_;
v___y_3469_ = v___y_3513_;
v___y_3470_ = v___x_3517_;
v___y_3471_ = v___x_3519_;
goto v___jp_3461_;
}
else
{
lean_object* v_val_3520_; lean_object* v___x_3521_; 
v_val_3520_ = lean_ctor_get(v_codeActionPrefix_x3f_3226_, 0);
lean_inc(v_val_3520_);
v___x_3521_ = lean_string_append(v_val_3520_, v___y_3510_);
v___y_3462_ = v___y_3507_;
v___y_3463_ = v___y_3508_;
v___y_3464_ = v___y_3510_;
v___y_3465_ = v___y_3509_;
v___y_3466_ = v___y_3511_;
v___y_3467_ = v___y_3512_;
v___y_3468_ = v___y_3514_;
v___y_3469_ = v___y_3513_;
v___y_3470_ = v___x_3517_;
v___y_3471_ = v___x_3521_;
goto v___jp_3461_;
}
}
else
{
lean_object* v_val_3522_; lean_object* v___x_3523_; 
v_val_3522_ = lean_ctor_get(v_toCodeActionTitle_x3f_3516_, 0);
lean_inc(v_val_3522_);
lean_inc_ref(v___y_3510_);
v___x_3523_ = lean_apply_1(v_val_3522_, v___y_3510_);
v___y_3462_ = v___y_3507_;
v___y_3463_ = v___y_3508_;
v___y_3464_ = v___y_3510_;
v___y_3465_ = v___y_3509_;
v___y_3466_ = v___y_3511_;
v___y_3467_ = v___y_3512_;
v___y_3468_ = v___y_3514_;
v___y_3469_ = v___y_3513_;
v___y_3470_ = v___x_3517_;
v___y_3471_ = v___x_3523_;
goto v___jp_3461_;
}
}
v___jp_3524_:
{
uint8_t v___x_3526_; lean_object* v___x_3527_; 
v___x_3526_ = 0;
v___x_3527_ = l_Lean_Syntax_getRange_x3f(v___y_3525_, v___x_3526_);
lean_dec(v___y_3525_);
if (lean_obj_tag(v___x_3527_) == 1)
{
lean_object* v_val_3528_; lean_object* v_toTryThisSuggestion_3529_; lean_object* v_previewSpan_x3f_3530_; uint8_t v_diffGranularity_3531_; lean_object* v___x_3532_; 
v_val_3528_ = lean_ctor_get(v___x_3527_, 0);
lean_inc_n(v_val_3528_, 2);
lean_dec_ref(v___x_3527_);
v_toTryThisSuggestion_3529_ = lean_ctor_get(v_a_3282_, 0);
v_previewSpan_x3f_3530_ = lean_ctor_get(v_a_3282_, 2);
v_diffGranularity_3531_ = lean_ctor_get_uint8(v_a_3282_, sizeof(void*)*3);
lean_inc_ref(v_toTryThisSuggestion_3529_);
v___x_3532_ = l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(v_toTryThisSuggestion_3529_, v_val_3528_, v___y_3232_, v___y_3233_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_a_3533_; lean_object* v_range_3534_; lean_object* v_newText_3535_; lean_object* v___x_3536_; 
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_a_3533_);
lean_dec_ref(v___x_3532_);
v_range_3534_ = lean_ctor_get(v_a_3533_, 0);
lean_inc_ref(v_range_3534_);
v_newText_3535_ = lean_ctor_get(v_a_3533_, 1);
lean_inc_ref(v_newText_3535_);
v___x_3536_ = l_Lean_Syntax_getRange_x3f(v_ref_3227_, v___x_3526_);
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_inc(v_val_3528_);
lean_inc_ref(v_toTryThisSuggestion_3529_);
lean_inc(v_previewSpan_x3f_3530_);
v___y_3507_ = v_range_3534_;
v___y_3508_ = v_previewSpan_x3f_3530_;
v___y_3509_ = v_a_3533_;
v___y_3510_ = v_newText_3535_;
v___y_3511_ = v_toTryThisSuggestion_3529_;
v___y_3512_ = v_diffGranularity_3531_;
v___y_3513_ = v_val_3528_;
v___y_3514_ = v___x_3526_;
v___y_3515_ = v_val_3528_;
goto v___jp_3506_;
}
else
{
lean_object* v_val_3537_; 
v_val_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_val_3537_);
lean_dec_ref(v___x_3536_);
lean_inc_ref(v_toTryThisSuggestion_3529_);
lean_inc(v_previewSpan_x3f_3530_);
v___y_3507_ = v_range_3534_;
v___y_3508_ = v_previewSpan_x3f_3530_;
v___y_3509_ = v_a_3533_;
v___y_3510_ = v_newText_3535_;
v___y_3511_ = v_toTryThisSuggestion_3529_;
v___y_3512_ = v_diffGranularity_3531_;
v___y_3513_ = v_val_3528_;
v___y_3514_ = v___x_3526_;
v___y_3515_ = v_val_3537_;
goto v___jp_3506_;
}
}
else
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
lean_dec(v_val_3528_);
lean_dec_ref(v_b_3231_);
lean_dec(v_ref_3227_);
lean_dec(v_codeActionPrefix_x3f_3226_);
v_a_3538_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3540_ = v___x_3532_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3532_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3538_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
else
{
lean_dec(v___x_3527_);
v_a_3236_ = v_b_3231_;
goto v___jp_3235_;
}
}
}
v___jp_3235_:
{
size_t v___x_3237_; size_t v___x_3238_; 
v___x_3237_ = ((size_t)1ULL);
v___x_3238_ = lean_usize_add(v_i_3230_, v___x_3237_);
v_i_3230_ = v___x_3238_;
v_b_3231_ = v_a_3236_;
goto _start;
}
v___jp_3240_:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; 
v___x_3242_ = l_Lean_MessageData_nestD(v___y_3241_);
v___x_3243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3243_, 0, v_b_3231_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v_a_3236_ = v___x_3243_;
goto v___jp_3235_;
}
v___jp_3244_:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3248_, 0, v___y_3246_);
lean_ctor_set(v___x_3248_, 1, v___y_3247_);
v___x_3249_ = l_Lean_stringToMessageData(v___y_3245_);
v___x_3250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3250_, 0, v___x_3248_);
lean_ctor_set(v___x_3250_, 1, v___x_3249_);
v___y_3241_ = v___x_3250_;
goto v___jp_3240_;
}
v___jp_3251_:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3253_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3254_ = lean_unsigned_to_nat(2u);
v___x_3255_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3);
v___x_3256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3256_, 0, v___x_3255_);
lean_ctor_set(v___x_3256_, 1, v___y_3252_);
v___x_3257_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3254_);
lean_ctor_set(v___x_3257_, 1, v___x_3256_);
v___x_3258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3253_);
lean_ctor_set(v___x_3258_, 1, v___x_3257_);
v___y_3241_ = v___x_3258_;
goto v___jp_3240_;
}
v___jp_3259_:
{
lean_object* v___x_3264_; uint64_t v_javascriptHash_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; uint8_t v___x_3277_; 
v___x_3264_ = l_Lean_Meta_Hint_tryThisDiffWidget;
v_javascriptHash_3265_ = lean_ctor_get_uint64(v___x_3264_, sizeof(void*)*1);
v___x_3266_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8));
v___x_3267_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3267_, 0, v___x_3266_);
lean_ctor_set(v___x_3267_, 1, v___y_3260_);
lean_ctor_set_uint64(v___x_3267_, sizeof(void*)*2, v_javascriptHash_3265_);
v___x_3268_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3268_, 0, v___y_3263_);
v___x_3269_ = l_Lean_MessageData_ofFormat(v___x_3268_);
v___x_3270_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3267_);
lean_ctor_set(v___x_3270_, 1, v___x_3269_);
v___x_3271_ = l_Lean_stringToMessageData(v___y_3262_);
v___x_3272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3271_);
lean_ctor_set(v___x_3272_, 1, v___x_3270_);
v___x_3273_ = l_Lean_stringToMessageData(v___y_3261_);
v___x_3274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3272_);
lean_ctor_set(v___x_3274_, 1, v___x_3273_);
v___x_3275_ = lean_array_get_size(v_suggestions_3224_);
v___x_3276_ = lean_unsigned_to_nat(1u);
v___x_3277_ = lean_nat_dec_eq(v___x_3275_, v___x_3276_);
if (v___x_3277_ == 0)
{
v___y_3252_ = v___x_3274_;
goto v___jp_3251_;
}
else
{
if (v_forceList_3225_ == 0)
{
if (v___x_3277_ == 0)
{
v___y_3252_ = v___x_3274_;
goto v___jp_3251_;
}
else
{
lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3278_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
lean_ctor_set(v___x_3279_, 1, v___x_3274_);
v___y_3241_ = v___x_3279_;
goto v___jp_3240_;
}
}
else
{
v___y_3252_ = v___x_3274_;
goto v___jp_3251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___boxed(lean_object* v_suggestions_3547_, lean_object* v_forceList_3548_, lean_object* v_codeActionPrefix_x3f_3549_, lean_object* v_ref_3550_, lean_object* v_as_3551_, lean_object* v_sz_3552_, lean_object* v_i_3553_, lean_object* v_b_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
uint8_t v_forceList_boxed_3558_; size_t v_sz_boxed_3559_; size_t v_i_boxed_3560_; lean_object* v_res_3561_; 
v_forceList_boxed_3558_ = lean_unbox(v_forceList_3548_);
v_sz_boxed_3559_ = lean_unbox_usize(v_sz_3552_);
lean_dec(v_sz_3552_);
v_i_boxed_3560_ = lean_unbox_usize(v_i_3553_);
lean_dec(v_i_3553_);
v_res_3561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3547_, v_forceList_boxed_3558_, v_codeActionPrefix_x3f_3549_, v_ref_3550_, v_as_3551_, v_sz_boxed_3559_, v_i_boxed_3560_, v_b_3554_, v___y_3555_, v___y_3556_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec_ref(v_as_3551_);
lean_dec_ref(v_suggestions_3547_);
return v_res_3561_;
}
}
static lean_object* _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0(void){
_start:
{
lean_object* v___x_3562_; lean_object* v_msg_3563_; 
v___x_3562_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v_msg_3563_ = l_Lean_stringToMessageData(v___x_3562_);
return v_msg_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage(lean_object* v_suggestions_3564_, lean_object* v_ref_3565_, lean_object* v_codeActionPrefix_x3f_3566_, uint8_t v_forceList_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_){
_start:
{
lean_object* v_msg_3571_; size_t v_sz_3572_; size_t v___x_3573_; lean_object* v___x_3574_; 
v_msg_3571_ = lean_obj_once(&l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0, &l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0_once, _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0);
v_sz_3572_ = lean_array_size(v_suggestions_3564_);
v___x_3573_ = ((size_t)0ULL);
v___x_3574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3564_, v_forceList_3567_, v_codeActionPrefix_x3f_3566_, v_ref_3565_, v_suggestions_3564_, v_sz_3572_, v___x_3573_, v_msg_3571_, v_a_3568_, v_a_3569_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage___boxed(lean_object* v_suggestions_3575_, lean_object* v_ref_3576_, lean_object* v_codeActionPrefix_x3f_3577_, lean_object* v_forceList_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_){
_start:
{
uint8_t v_forceList_boxed_3582_; lean_object* v_res_3583_; 
v_forceList_boxed_3582_ = lean_unbox(v_forceList_3578_);
v_res_3583_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3575_, v_ref_3576_, v_codeActionPrefix_x3f_3577_, v_forceList_boxed_3582_, v_a_3579_, v_a_3580_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
lean_dec_ref(v_suggestions_3575_);
return v_res_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(lean_object* v_t_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_){
_start:
{
lean_object* v___x_3588_; 
v___x_3588_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3584_, v___y_3586_);
return v___x_3588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___boxed(lean_object* v_t_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(v_t_3589_, v___y_3590_, v___y_3591_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
return v_res_3593_;
}
}
static lean_object* _init_l_Lean_MessageData_hint___closed__3(void){
_start:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3598_ = ((lean_object*)(l_Lean_MessageData_hint___closed__2));
v___x_3599_ = l_Lean_stringToMessageData(v___x_3598_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint(lean_object* v_hint_3600_, lean_object* v_suggestions_3601_, lean_object* v_ref_x3f_3602_, lean_object* v_codeActionPrefix_x3f_3603_, uint8_t v_forceList_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_){
_start:
{
lean_object* v___y_3609_; 
if (lean_obj_tag(v_ref_x3f_3602_) == 0)
{
lean_object* v_ref_3624_; 
v_ref_3624_ = lean_ctor_get(v_a_3605_, 5);
lean_inc(v_ref_3624_);
v___y_3609_ = v_ref_3624_;
goto v___jp_3608_;
}
else
{
lean_object* v_val_3625_; 
v_val_3625_ = lean_ctor_get(v_ref_x3f_3602_, 0);
lean_inc(v_val_3625_);
lean_dec_ref(v_ref_x3f_3602_);
v___y_3609_ = v_val_3625_;
goto v___jp_3608_;
}
v___jp_3608_:
{
lean_object* v___x_3610_; 
v___x_3610_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3601_, v___y_3609_, v_codeActionPrefix_x3f_3603_, v_forceList_3604_, v_a_3605_, v_a_3606_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3623_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3613_ = v___x_3610_;
v_isShared_3614_ = v_isSharedCheck_3623_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3610_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3623_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3621_; 
v___x_3615_ = ((lean_object*)(l_Lean_MessageData_hint___closed__1));
v___x_3616_ = lean_obj_once(&l_Lean_MessageData_hint___closed__3, &l_Lean_MessageData_hint___closed__3_once, _init_l_Lean_MessageData_hint___closed__3);
v___x_3617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3616_);
lean_ctor_set(v___x_3617_, 1, v_hint_3600_);
v___x_3618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3618_, 0, v___x_3617_);
lean_ctor_set(v___x_3618_, 1, v_a_3611_);
v___x_3619_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3615_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 0, v___x_3619_);
v___x_3621_ = v___x_3613_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3619_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
else
{
lean_dec_ref(v_hint_3600_);
return v___x_3610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint___boxed(lean_object* v_hint_3626_, lean_object* v_suggestions_3627_, lean_object* v_ref_x3f_3628_, lean_object* v_codeActionPrefix_x3f_3629_, lean_object* v_forceList_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_){
_start:
{
uint8_t v_forceList_boxed_3634_; lean_object* v_res_3635_; 
v_forceList_boxed_3634_ = lean_unbox(v_forceList_3630_);
v_res_3635_ = l_Lean_MessageData_hint(v_hint_3626_, v_suggestions_3627_, v_ref_x3f_3628_, v_codeActionPrefix_x3f_3629_, v_forceList_boxed_3634_, v_a_3631_, v_a_3632_);
lean_dec(v_a_3632_);
lean_dec_ref(v_a_3631_);
lean_dec_ref(v_suggestions_3627_);
return v_res_3635_;
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
l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed__const__1 = _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed__const__1();
lean_mark_persistent(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed__const__1);
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
