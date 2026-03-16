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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(uint32_t, lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(uint32_t, lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(uint32_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0 = (const lean_object*)&l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0_value;
static const lean_ctor_object l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__1 = (const lean_object*)&l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__1_value;
static const lean_ctor_object l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0_value),((lean_object*)&l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__1_value)}};
static const lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__2 = (const lean_object*)&l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(lean_object*, lean_object*, lean_object*);
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
lean_inc(v_head_780_);
v_snd_781_ = lean_ctor_get(v_head_780_, 1);
lean_inc(v_snd_781_);
v_leftIndex_782_ = lean_ctor_get(v_snd_781_, 1);
lean_inc(v_leftIndex_782_);
if (lean_obj_tag(v_leftIndex_782_) == 1)
{
lean_object* v_rightIndex_783_; 
v_rightIndex_783_ = lean_ctor_get(v_snd_781_, 3);
lean_inc(v_rightIndex_783_);
if (lean_obj_tag(v_rightIndex_783_) == 1)
{
if (lean_obj_tag(v_b_779_) == 0)
{
lean_object* v_tail_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_814_; 
v_tail_784_ = lean_ctor_get(v_as_x27_778_, 1);
v_isSharedCheck_814_ = !lean_is_exclusive(v_as_x27_778_);
if (v_isSharedCheck_814_ == 0)
{
lean_object* v_unused_815_; 
v_unused_815_ = lean_ctor_get(v_as_x27_778_, 0);
lean_dec(v_unused_815_);
v___x_786_ = v_as_x27_778_;
v_isShared_787_ = v_isSharedCheck_814_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_tail_784_);
lean_dec(v_as_x27_778_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_814_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v_fst_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_812_; 
v_fst_788_ = lean_ctor_get(v_head_780_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v_head_780_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; 
v_unused_813_ = lean_ctor_get(v_head_780_, 1);
lean_dec(v_unused_813_);
v___x_790_ = v_head_780_;
v_isShared_791_ = v_isSharedCheck_812_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_fst_788_);
lean_dec(v_head_780_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_812_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v_leftCount_792_; lean_object* v_rightCount_793_; lean_object* v_val_794_; lean_object* v_val_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_811_; 
v_leftCount_792_ = lean_ctor_get(v_snd_781_, 0);
lean_inc(v_leftCount_792_);
v_rightCount_793_ = lean_ctor_get(v_snd_781_, 2);
lean_inc(v_rightCount_793_);
lean_dec(v_snd_781_);
v_val_794_ = lean_ctor_get(v_leftIndex_782_, 0);
lean_inc(v_val_794_);
lean_dec_ref(v_leftIndex_782_);
v_val_795_ = lean_ctor_get(v_rightIndex_783_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v_rightIndex_783_);
if (v_isSharedCheck_811_ == 0)
{
v___x_797_ = v_rightIndex_783_;
v_isShared_798_ = v_isSharedCheck_811_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_val_795_);
lean_dec(v_rightIndex_783_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_811_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_799_; lean_object* v___x_801_; 
v___x_799_ = lean_nat_add(v_leftCount_792_, v_rightCount_793_);
lean_dec(v_rightCount_793_);
lean_dec(v_leftCount_792_);
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 1, v_val_795_);
lean_ctor_set(v___x_790_, 0, v_val_794_);
v___x_801_ = v___x_790_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_val_794_);
lean_ctor_set(v_reuseFailAlloc_810_, 1, v_val_795_);
v___x_801_ = v_reuseFailAlloc_810_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_803_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set_tag(v___x_786_, 0);
lean_ctor_set(v___x_786_, 1, v___x_801_);
lean_ctor_set(v___x_786_, 0, v_fst_788_);
v___x_803_ = v___x_786_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v_fst_788_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v___x_801_);
v___x_803_ = v_reuseFailAlloc_809_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_804_; lean_object* v___x_806_; 
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_799_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_804_);
v___x_806_ = v___x_797_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_804_);
v___x_806_ = v_reuseFailAlloc_808_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
v_as_x27_778_ = v_tail_784_;
v_b_779_ = v___x_806_;
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
lean_object* v_val_816_; lean_object* v_tail_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_858_; 
v_val_816_ = lean_ctor_get(v_b_779_, 0);
lean_inc(v_val_816_);
v_tail_817_ = lean_ctor_get(v_as_x27_778_, 1);
v_isSharedCheck_858_ = !lean_is_exclusive(v_as_x27_778_);
if (v_isSharedCheck_858_ == 0)
{
lean_object* v_unused_859_; 
v_unused_859_ = lean_ctor_get(v_as_x27_778_, 0);
lean_dec(v_unused_859_);
v___x_819_ = v_as_x27_778_;
v_isShared_820_ = v_isSharedCheck_858_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_tail_817_);
lean_dec(v_as_x27_778_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_858_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v_fst_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_856_; 
v_fst_821_ = lean_ctor_get(v_head_780_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v_head_780_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; 
v_unused_857_ = lean_ctor_get(v_head_780_, 1);
lean_dec(v_unused_857_);
v___x_823_ = v_head_780_;
v_isShared_824_ = v_isSharedCheck_856_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_fst_821_);
lean_dec(v_head_780_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_856_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v_leftCount_825_; lean_object* v_rightCount_826_; lean_object* v_val_827_; lean_object* v_val_828_; lean_object* v_fst_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_854_; 
v_leftCount_825_ = lean_ctor_get(v_snd_781_, 0);
lean_inc(v_leftCount_825_);
v_rightCount_826_ = lean_ctor_get(v_snd_781_, 2);
lean_inc(v_rightCount_826_);
lean_dec(v_snd_781_);
v_val_827_ = lean_ctor_get(v_leftIndex_782_, 0);
lean_inc(v_val_827_);
lean_dec_ref(v_leftIndex_782_);
v_val_828_ = lean_ctor_get(v_rightIndex_783_, 0);
lean_inc(v_val_828_);
lean_dec_ref(v_rightIndex_783_);
v_fst_829_ = lean_ctor_get(v_val_816_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v_val_816_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; 
v_unused_855_ = lean_ctor_get(v_val_816_, 1);
lean_dec(v_unused_855_);
v___x_831_ = v_val_816_;
v_isShared_832_ = v_isSharedCheck_854_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_fst_829_);
lean_dec(v_val_816_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_854_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_833_ = lean_nat_add(v_leftCount_825_, v_rightCount_826_);
lean_dec(v_rightCount_826_);
lean_dec(v_leftCount_825_);
v___x_834_ = lean_nat_dec_lt(v___x_833_, v_fst_829_);
lean_dec(v_fst_829_);
if (v___x_834_ == 0)
{
lean_dec(v___x_833_);
lean_del_object(v___x_831_);
lean_dec(v_val_828_);
lean_dec(v_val_827_);
lean_del_object(v___x_823_);
lean_dec(v_fst_821_);
lean_del_object(v___x_819_);
v_as_x27_778_ = v_tail_817_;
goto _start;
}
else
{
lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_852_; 
v_isSharedCheck_852_ = !lean_is_exclusive(v_b_779_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; 
v_unused_853_ = lean_ctor_get(v_b_779_, 0);
lean_dec(v_unused_853_);
v___x_837_ = v_b_779_;
v_isShared_838_ = v_isSharedCheck_852_;
goto v_resetjp_836_;
}
else
{
lean_dec(v_b_779_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_852_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 1, v_val_828_);
lean_ctor_set(v___x_831_, 0, v_val_827_);
v___x_840_ = v___x_831_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v_val_827_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v_val_828_);
v___x_840_ = v_reuseFailAlloc_851_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
lean_object* v___x_842_; 
if (v_isShared_824_ == 0)
{
lean_ctor_set(v___x_823_, 1, v___x_840_);
v___x_842_ = v___x_823_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v_fst_821_);
lean_ctor_set(v_reuseFailAlloc_850_, 1, v___x_840_);
v___x_842_ = v_reuseFailAlloc_850_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_844_; 
if (v_isShared_820_ == 0)
{
lean_ctor_set_tag(v___x_819_, 0);
lean_ctor_set(v___x_819_, 1, v___x_842_);
lean_ctor_set(v___x_819_, 0, v___x_833_);
v___x_844_ = v___x_819_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_833_);
lean_ctor_set(v_reuseFailAlloc_849_, 1, v___x_842_);
v___x_844_ = v_reuseFailAlloc_849_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_846_; 
if (v_isShared_838_ == 0)
{
lean_ctor_set(v___x_837_, 0, v___x_844_);
v___x_846_ = v___x_837_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_848_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
v_as_x27_778_ = v_tail_817_;
v_b_779_ = v___x_846_;
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
else
{
lean_object* v_tail_860_; 
lean_dec(v_rightIndex_783_);
lean_dec_ref(v_leftIndex_782_);
lean_dec(v_snd_781_);
lean_dec(v_head_780_);
v_tail_860_ = lean_ctor_get(v_as_x27_778_, 1);
lean_inc(v_tail_860_);
lean_dec_ref(v_as_x27_778_);
v_as_x27_778_ = v_tail_860_;
goto _start;
}
}
else
{
lean_object* v_tail_862_; 
lean_dec(v_leftIndex_782_);
lean_dec(v_snd_781_);
lean_dec(v_head_780_);
v_tail_862_ = lean_ctor_get(v_as_x27_778_, 1);
lean_inc(v_tail_862_);
lean_dec_ref(v_as_x27_778_);
v_as_x27_778_ = v_tail_862_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3_spec__4(lean_object* v_left_864_, lean_object* v_right_865_, lean_object* v_pref_866_){
_start:
{
lean_object* v_start_867_; lean_object* v_stop_868_; lean_object* v_i_869_; lean_object* v___x_875_; uint8_t v___x_876_; 
v_start_867_ = lean_ctor_get(v_left_864_, 1);
v_stop_868_ = lean_ctor_get(v_left_864_, 2);
v_i_869_ = lean_array_get_size(v_pref_866_);
v___x_875_ = lean_nat_sub(v_stop_868_, v_start_867_);
v___x_876_ = lean_nat_dec_lt(v_i_869_, v___x_875_);
lean_dec(v___x_875_);
if (v___x_876_ == 0)
{
goto v___jp_870_;
}
else
{
lean_object* v_start_877_; lean_object* v_stop_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v_start_877_ = lean_ctor_get(v_right_865_, 1);
v_stop_878_ = lean_ctor_get(v_right_865_, 2);
v___x_879_ = lean_nat_sub(v_stop_878_, v_start_877_);
v___x_880_ = lean_nat_dec_lt(v_i_869_, v___x_879_);
lean_dec(v___x_879_);
if (v___x_880_ == 0)
{
goto v___jp_870_;
}
else
{
lean_object* v___x_881_; lean_object* v___x_882_; uint32_t v___x_883_; uint32_t v___x_884_; uint8_t v___x_885_; 
v___x_881_ = l_Subarray_get___redArg(v_left_864_, v_i_869_);
v___x_882_ = l_Subarray_get___redArg(v_right_865_, v_i_869_);
v___x_883_ = lean_unbox_uint32(v___x_881_);
v___x_884_ = lean_unbox_uint32(v___x_882_);
lean_dec(v___x_882_);
v___x_885_ = lean_uint32_dec_eq(v___x_883_, v___x_884_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
lean_dec(v___x_881_);
v___x_886_ = l_Subarray_drop___redArg(v_left_864_, v_i_869_);
v___x_887_ = l_Subarray_drop___redArg(v_right_865_, v_i_869_);
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_886_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v_pref_866_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
return v___x_889_;
}
else
{
lean_object* v___x_890_; 
v___x_890_ = lean_array_push(v_pref_866_, v___x_881_);
v_pref_866_ = v___x_890_;
goto _start;
}
}
}
v___jp_870_:
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_871_ = l_Subarray_drop___redArg(v_left_864_, v_i_869_);
v___x_872_ = l_Subarray_drop___redArg(v_right_865_, v_i_869_);
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_871_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
v___x_874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_874_, 0, v_pref_866_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
return v___x_874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3(lean_object* v_left_892_, lean_object* v_right_893_){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_895_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3_spec__4(v_left_892_, v_right_893_, v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(lean_object* v_a_896_, lean_object* v_b_897_){
_start:
{
lean_object* v_array_898_; lean_object* v_start_899_; lean_object* v_stop_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_913_; 
v_array_898_ = lean_ctor_get(v_a_896_, 0);
v_start_899_ = lean_ctor_get(v_a_896_, 1);
v_stop_900_ = lean_ctor_get(v_a_896_, 2);
v_isSharedCheck_913_ = !lean_is_exclusive(v_a_896_);
if (v_isSharedCheck_913_ == 0)
{
v___x_902_ = v_a_896_;
v_isShared_903_ = v_isSharedCheck_913_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_stop_900_);
lean_inc(v_start_899_);
lean_inc(v_array_898_);
lean_dec(v_a_896_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_913_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
uint8_t v___x_904_; 
v___x_904_ = lean_nat_dec_lt(v_start_899_, v_stop_900_);
if (v___x_904_ == 0)
{
lean_del_object(v___x_902_);
lean_dec(v_stop_900_);
lean_dec(v_start_899_);
lean_dec_ref(v_array_898_);
return v_b_897_;
}
else
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_908_; 
v___x_905_ = lean_unsigned_to_nat(1u);
v___x_906_ = lean_nat_add(v_start_899_, v___x_905_);
lean_inc_ref(v_array_898_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 1, v___x_906_);
v___x_908_ = v___x_902_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_array_898_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_stop_900_);
v___x_908_ = v_reuseFailAlloc_912_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = lean_array_fget(v_array_898_, v_start_899_);
lean_dec(v_start_899_);
lean_dec_ref(v_array_898_);
v___x_910_ = lean_array_push(v_b_897_, v___x_909_);
v_a_896_ = v___x_908_;
v_b_897_ = v___x_910_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6(lean_object* v_left_914_, lean_object* v_right_915_, lean_object* v_i_916_){
_start:
{
lean_object* v_start_917_; lean_object* v_stop_918_; lean_object* v___x_919_; uint8_t v___x_933_; 
v_start_917_ = lean_ctor_get(v_left_914_, 1);
v_stop_918_ = lean_ctor_get(v_left_914_, 2);
v___x_919_ = lean_nat_sub(v_stop_918_, v_start_917_);
v___x_933_ = lean_nat_dec_lt(v_i_916_, v___x_919_);
if (v___x_933_ == 0)
{
goto v___jp_920_;
}
else
{
lean_object* v_start_934_; lean_object* v_stop_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v_start_934_ = lean_ctor_get(v_right_915_, 1);
v_stop_935_ = lean_ctor_get(v_right_915_, 2);
v___x_936_ = lean_nat_sub(v_stop_935_, v_start_934_);
v___x_937_ = lean_nat_dec_lt(v_i_916_, v___x_936_);
if (v___x_937_ == 0)
{
lean_dec(v___x_936_);
goto v___jp_920_;
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; uint32_t v___x_945_; uint32_t v___x_946_; uint8_t v___x_947_; 
v___x_938_ = lean_nat_sub(v___x_919_, v_i_916_);
lean_dec(v___x_919_);
v___x_939_ = lean_unsigned_to_nat(1u);
v___x_940_ = lean_nat_sub(v___x_938_, v___x_939_);
v___x_941_ = l_Subarray_get___redArg(v_left_914_, v___x_940_);
lean_dec(v___x_940_);
v___x_942_ = lean_nat_sub(v___x_936_, v_i_916_);
lean_dec(v___x_936_);
v___x_943_ = lean_nat_sub(v___x_942_, v___x_939_);
v___x_944_ = l_Subarray_get___redArg(v_right_915_, v___x_943_);
lean_dec(v___x_943_);
v___x_945_ = lean_unbox_uint32(v___x_941_);
lean_dec(v___x_941_);
v___x_946_ = lean_unbox_uint32(v___x_944_);
lean_dec(v___x_944_);
v___x_947_ = lean_uint32_dec_eq(v___x_945_, v___x_946_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
lean_dec(v_i_916_);
lean_inc_ref(v_left_914_);
v___x_948_ = l_Subarray_take___redArg(v_left_914_, v___x_938_);
v___x_949_ = l_Subarray_take___redArg(v_right_915_, v___x_942_);
lean_dec(v___x_942_);
v___x_950_ = l_Subarray_drop___redArg(v_left_914_, v___x_938_);
lean_dec(v___x_938_);
v___x_951_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_952_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(v___x_950_, v___x_951_);
v___x_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_953_, 0, v___x_949_);
lean_ctor_set(v___x_953_, 1, v___x_952_);
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_948_);
lean_ctor_set(v___x_954_, 1, v___x_953_);
return v___x_954_;
}
else
{
lean_object* v___x_955_; 
lean_dec(v___x_942_);
lean_dec(v___x_938_);
v___x_955_ = lean_nat_add(v_i_916_, v___x_939_);
lean_dec(v_i_916_);
v_i_916_ = v___x_955_;
goto _start;
}
}
}
v___jp_920_:
{
lean_object* v_start_921_; lean_object* v_stop_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v_start_921_ = lean_ctor_get(v_right_915_, 1);
v_stop_922_ = lean_ctor_get(v_right_915_, 2);
v___x_923_ = lean_nat_sub(v___x_919_, v_i_916_);
lean_dec(v___x_919_);
lean_inc_ref(v_left_914_);
v___x_924_ = l_Subarray_take___redArg(v_left_914_, v___x_923_);
v___x_925_ = lean_nat_sub(v_stop_922_, v_start_921_);
v___x_926_ = lean_nat_sub(v___x_925_, v_i_916_);
lean_dec(v_i_916_);
lean_dec(v___x_925_);
v___x_927_ = l_Subarray_take___redArg(v_right_915_, v___x_926_);
lean_dec(v___x_926_);
v___x_928_ = l_Subarray_drop___redArg(v_left_914_, v___x_923_);
lean_dec(v___x_923_);
v___x_929_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_930_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(v___x_928_, v___x_929_);
v___x_931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_927_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_924_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
return v___x_932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4(lean_object* v_left_957_, lean_object* v_right_958_){
_start:
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = lean_unsigned_to_nat(0u);
v___x_960_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6(v_left_957_, v_right_958_, v___x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(lean_object* v_x_961_, lean_object* v_x_962_){
_start:
{
if (lean_obj_tag(v_x_962_) == 0)
{
lean_inc(v_x_961_);
return v_x_961_;
}
else
{
lean_object* v_key_963_; lean_object* v_value_964_; lean_object* v_tail_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_key_963_ = lean_ctor_get(v_x_962_, 0);
v_value_964_ = lean_ctor_get(v_x_962_, 1);
v_tail_965_ = lean_ctor_get(v_x_962_, 2);
v___x_966_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(v_x_961_, v_tail_965_);
lean_inc(v_value_964_);
lean_inc(v_key_963_);
v___x_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_967_, 0, v_key_963_);
lean_ctor_set(v___x_967_, 1, v_value_964_);
v___x_968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v___x_966_);
return v___x_968_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6___boxed(lean_object* v_x_969_, lean_object* v_x_970_){
_start:
{
lean_object* v_res_971_; 
v_res_971_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(v_x_969_, v_x_970_);
lean_dec(v_x_970_);
lean_dec(v_x_969_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7(lean_object* v_as_972_, size_t v_i_973_, size_t v_stop_974_, lean_object* v_b_975_){
_start:
{
uint8_t v___x_976_; 
v___x_976_ = lean_usize_dec_eq(v_i_973_, v_stop_974_);
if (v___x_976_ == 0)
{
size_t v___x_977_; size_t v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_977_ = ((size_t)1ULL);
v___x_978_ = lean_usize_sub(v_i_973_, v___x_977_);
v___x_979_ = lean_array_uget_borrowed(v_as_972_, v___x_978_);
v___x_980_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__6(v_b_975_, v___x_979_);
lean_dec(v_b_975_);
v_i_973_ = v___x_978_;
v_b_975_ = v___x_980_;
goto _start;
}
else
{
return v_b_975_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7___boxed(lean_object* v_as_982_, lean_object* v_i_983_, lean_object* v_stop_984_, lean_object* v_b_985_){
_start:
{
size_t v_i_boxed_986_; size_t v_stop_boxed_987_; lean_object* v_res_988_; 
v_i_boxed_986_ = lean_unbox_usize(v_i_983_);
lean_dec(v_i_983_);
v_stop_boxed_987_ = lean_unbox_usize(v_stop_984_);
lean_dec(v_stop_984_);
v_res_988_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7(v_as_982_, v_i_boxed_986_, v_stop_boxed_987_, v_b_985_);
lean_dec_ref(v_as_982_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(lean_object* v_histogram_989_, lean_object* v_index_990_, uint32_t v_val_991_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(v_histogram_989_, v_val_991_);
if (lean_obj_tag(v___x_992_) == 0)
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_993_ = lean_unsigned_to_nat(1u);
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v_index_990_);
v___x_995_ = lean_unsigned_to_nat(0u);
v___x_996_ = lean_box(0);
v___x_997_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_997_, 0, v___x_993_);
lean_ctor_set(v___x_997_, 1, v___x_994_);
lean_ctor_set(v___x_997_, 2, v___x_995_);
lean_ctor_set(v___x_997_, 3, v___x_996_);
v___x_998_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_histogram_989_, v_val_991_, v___x_997_);
return v___x_998_;
}
else
{
lean_object* v_val_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1020_; 
v_val_999_ = lean_ctor_get(v___x_992_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_992_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1001_ = v___x_992_;
v_isShared_1002_ = v_isSharedCheck_1020_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_val_999_);
lean_dec(v___x_992_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1020_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v_leftCount_1003_; lean_object* v_rightCount_1004_; lean_object* v_rightIndex_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1018_; 
v_leftCount_1003_ = lean_ctor_get(v_val_999_, 0);
v_rightCount_1004_ = lean_ctor_get(v_val_999_, 2);
v_rightIndex_1005_ = lean_ctor_get(v_val_999_, 3);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_val_999_);
if (v_isSharedCheck_1018_ == 0)
{
lean_object* v_unused_1019_; 
v_unused_1019_ = lean_ctor_get(v_val_999_, 1);
lean_dec(v_unused_1019_);
v___x_1007_ = v_val_999_;
v_isShared_1008_ = v_isSharedCheck_1018_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_rightIndex_1005_);
lean_inc(v_rightCount_1004_);
lean_inc(v_leftCount_1003_);
lean_dec(v_val_999_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1018_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1009_ = lean_unsigned_to_nat(1u);
v___x_1010_ = lean_nat_add(v_leftCount_1003_, v___x_1009_);
lean_dec(v_leftCount_1003_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v_index_990_);
v___x_1012_ = v___x_1001_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_index_990_);
v___x_1012_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1014_; 
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 1, v___x_1012_);
lean_ctor_set(v___x_1007_, 0, v___x_1010_);
v___x_1014_ = v___x_1007_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1016_, 2, v_rightCount_1004_);
lean_ctor_set(v_reuseFailAlloc_1016_, 3, v_rightIndex_1005_);
v___x_1014_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1015_; 
v___x_1015_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_histogram_989_, v_val_991_, v___x_1014_);
return v___x_1015_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg___boxed(lean_object* v_histogram_1021_, lean_object* v_index_1022_, lean_object* v_val_1023_){
_start:
{
uint32_t v_val_boxed_1024_; lean_object* v_res_1025_; 
v_val_boxed_1024_ = lean_unbox_uint32(v_val_1023_);
lean_dec(v_val_1023_);
v_res_1025_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(v_histogram_1021_, v_index_1022_, v_val_boxed_1024_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg(lean_object* v_upperBound_1026_, lean_object* v_fst_1027_, lean_object* v___x_1028_, lean_object* v_fst_1029_, lean_object* v_a_1030_, lean_object* v_b_1031_){
_start:
{
uint8_t v___x_1032_; 
v___x_1032_ = lean_nat_dec_lt(v_a_1030_, v_upperBound_1026_);
if (v___x_1032_ == 0)
{
lean_dec(v_a_1030_);
return v_b_1031_;
}
else
{
lean_object* v___x_1033_; uint32_t v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1033_ = l_Subarray_get___redArg(v_fst_1029_, v_a_1030_);
v___x_1034_ = lean_unbox_uint32(v___x_1033_);
lean_dec(v___x_1033_);
lean_inc(v_a_1030_);
v___x_1035_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(v_b_1031_, v_a_1030_, v___x_1034_);
v___x_1036_ = lean_unsigned_to_nat(1u);
v___x_1037_ = lean_nat_add(v_a_1030_, v___x_1036_);
lean_dec(v_a_1030_);
v_a_1030_ = v___x_1037_;
v_b_1031_ = v___x_1035_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg___boxed(lean_object* v_upperBound_1039_, lean_object* v_fst_1040_, lean_object* v___x_1041_, lean_object* v_fst_1042_, lean_object* v_a_1043_, lean_object* v_b_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg(v_upperBound_1039_, v_fst_1040_, v___x_1041_, v_fst_1042_, v_a_1043_, v_b_1044_);
lean_dec_ref(v_fst_1042_);
lean_dec(v___x_1041_);
lean_dec_ref(v_fst_1040_);
lean_dec(v_upperBound_1039_);
return v_res_1045_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = lean_box(0);
v___x_1047_ = lean_unsigned_to_nat(16u);
v___x_1048_ = lean_mk_array(v___x_1047_, v___x_1046_);
return v___x_1048_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v_hist_1051_; 
v___x_1049_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__0);
v___x_1050_ = lean_unsigned_to_nat(0u);
v_hist_1051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_1051_, 0, v___x_1050_);
lean_ctor_set(v_hist_1051_, 1, v___x_1049_);
return v_hist_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(lean_object* v_left_1052_, lean_object* v_right_1053_){
_start:
{
lean_object* v___x_1054_; lean_object* v_snd_1055_; lean_object* v_fst_1056_; lean_object* v_fst_1057_; lean_object* v_snd_1058_; lean_object* v___x_1059_; lean_object* v_snd_1060_; lean_object* v_fst_1061_; lean_object* v_fst_1062_; lean_object* v_snd_1063_; lean_object* v_start_1064_; lean_object* v_stop_1065_; lean_object* v___x_1066_; lean_object* v_hist_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v_start_1070_; lean_object* v_stop_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v_buckets_1074_; lean_object* v___x_1075_; lean_object* v___y_1077_; lean_object* v___x_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1054_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__3(v_left_1052_, v_right_1053_);
v_snd_1055_ = lean_ctor_get(v___x_1054_, 1);
lean_inc(v_snd_1055_);
v_fst_1056_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_fst_1056_);
lean_dec_ref(v___x_1054_);
v_fst_1057_ = lean_ctor_get(v_snd_1055_, 0);
lean_inc(v_fst_1057_);
v_snd_1058_ = lean_ctor_get(v_snd_1055_, 1);
lean_inc(v_snd_1058_);
lean_dec(v_snd_1055_);
v___x_1059_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4(v_fst_1057_, v_snd_1058_);
v_snd_1060_ = lean_ctor_get(v___x_1059_, 1);
lean_inc(v_snd_1060_);
v_fst_1061_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_fst_1061_);
lean_dec_ref(v___x_1059_);
v_fst_1062_ = lean_ctor_get(v_snd_1060_, 0);
lean_inc(v_fst_1062_);
v_snd_1063_ = lean_ctor_get(v_snd_1060_, 1);
lean_inc(v_snd_1063_);
lean_dec(v_snd_1060_);
v_start_1064_ = lean_ctor_get(v_fst_1061_, 1);
v_stop_1065_ = lean_ctor_get(v_fst_1061_, 2);
v___x_1066_ = lean_unsigned_to_nat(0u);
v_hist_1067_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___closed__1);
v___x_1068_ = lean_nat_sub(v_stop_1065_, v_start_1064_);
v___x_1069_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg(v___x_1068_, v_fst_1062_, v___x_1068_, v_fst_1061_, v___x_1066_, v_hist_1067_);
v_start_1070_ = lean_ctor_get(v_fst_1062_, 1);
v_stop_1071_ = lean_ctor_get(v_fst_1062_, 2);
v___x_1072_ = lean_nat_sub(v_stop_1071_, v_start_1070_);
v___x_1073_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(v___x_1072_, v___x_1072_, v_fst_1062_, v___x_1068_, v___x_1066_, v___x_1069_);
lean_dec(v___x_1068_);
lean_dec(v___x_1072_);
v_buckets_1074_ = lean_ctor_get(v___x_1073_, 1);
lean_inc_ref(v_buckets_1074_);
lean_dec_ref(v___x_1073_);
v___x_1075_ = lean_box(0);
v___x_1103_ = lean_box(0);
v___x_1104_ = lean_array_get_size(v_buckets_1074_);
v___x_1105_ = lean_nat_dec_lt(v___x_1066_, v___x_1104_);
if (v___x_1105_ == 0)
{
lean_dec_ref(v_buckets_1074_);
v___y_1077_ = v___x_1103_;
goto v___jp_1076_;
}
else
{
size_t v___x_1106_; size_t v___x_1107_; lean_object* v___x_1108_; 
v___x_1106_ = lean_usize_of_nat(v___x_1104_);
v___x_1107_ = ((size_t)0ULL);
v___x_1108_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__7(v_buckets_1074_, v___x_1106_, v___x_1107_, v___x_1103_);
lean_dec_ref(v_buckets_1074_);
v___y_1077_ = v___x_1108_;
goto v___jp_1076_;
}
v___jp_1076_:
{
lean_object* v___x_1078_; 
v___x_1078_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg(v___y_1077_, v___x_1075_);
if (lean_obj_tag(v___x_1078_) == 1)
{
lean_object* v_val_1079_; lean_object* v_snd_1080_; lean_object* v_snd_1081_; lean_object* v_fst_1082_; lean_object* v_fst_1083_; lean_object* v_snd_1084_; lean_object* v___x_1085_; lean_object* v_fst_1086_; lean_object* v_snd_1087_; lean_object* v___x_1088_; lean_object* v_fst_1089_; lean_object* v_snd_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v_val_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_val_1079_);
lean_dec_ref(v___x_1078_);
v_snd_1080_ = lean_ctor_get(v_val_1079_, 1);
lean_inc(v_snd_1080_);
lean_dec(v_val_1079_);
v_snd_1081_ = lean_ctor_get(v_snd_1080_, 1);
lean_inc(v_snd_1081_);
v_fst_1082_ = lean_ctor_get(v_snd_1080_, 0);
lean_inc(v_fst_1082_);
lean_dec(v_snd_1080_);
v_fst_1083_ = lean_ctor_get(v_snd_1081_, 0);
lean_inc(v_fst_1083_);
v_snd_1084_ = lean_ctor_get(v_snd_1081_, 1);
lean_inc(v_snd_1084_);
lean_dec(v_snd_1081_);
v___x_1085_ = l_Subarray_split___redArg(v_fst_1061_, v_fst_1083_);
lean_dec(v_fst_1083_);
v_fst_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_fst_1086_);
v_snd_1087_ = lean_ctor_get(v___x_1085_, 1);
lean_inc(v_snd_1087_);
lean_dec_ref(v___x_1085_);
v___x_1088_ = l_Subarray_split___redArg(v_fst_1062_, v_snd_1084_);
lean_dec(v_snd_1084_);
v_fst_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_fst_1089_);
v_snd_1090_ = lean_ctor_get(v___x_1088_, 1);
lean_inc(v_snd_1090_);
lean_dec_ref(v___x_1088_);
v___x_1091_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v_fst_1086_, v_fst_1089_);
v___x_1092_ = l_Array_append___redArg(v_fst_1056_, v___x_1091_);
lean_dec_ref(v___x_1091_);
v___x_1093_ = lean_unsigned_to_nat(1u);
v___x_1094_ = lean_mk_empty_array_with_capacity(v___x_1093_);
v___x_1095_ = lean_array_push(v___x_1094_, v_fst_1082_);
v___x_1096_ = l_Array_append___redArg(v___x_1092_, v___x_1095_);
lean_dec_ref(v___x_1095_);
v___x_1097_ = l_Subarray_drop___redArg(v_snd_1087_, v___x_1093_);
v___x_1098_ = l_Subarray_drop___redArg(v_snd_1090_, v___x_1093_);
v___x_1099_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v___x_1097_, v___x_1098_);
v___x_1100_ = l_Array_append___redArg(v___x_1096_, v___x_1099_);
lean_dec_ref(v___x_1099_);
v___x_1101_ = l_Array_append___redArg(v___x_1100_, v_snd_1063_);
lean_dec(v_snd_1063_);
return v___x_1101_;
}
else
{
lean_object* v___x_1102_; 
lean_dec(v___x_1078_);
lean_dec(v_fst_1062_);
lean_dec(v_fst_1061_);
v___x_1102_ = l_Array_append___redArg(v_fst_1056_, v_snd_1063_);
lean_dec(v_snd_1063_);
return v___x_1102_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(size_t v_sz_1109_, size_t v_i_1110_, lean_object* v_bs_1111_){
_start:
{
uint8_t v___x_1112_; 
v___x_1112_ = lean_usize_dec_lt(v_i_1110_, v_sz_1109_);
if (v___x_1112_ == 0)
{
return v_bs_1111_;
}
else
{
lean_object* v_v_1113_; lean_object* v___x_1114_; lean_object* v_bs_x27_1115_; uint8_t v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; size_t v___x_1119_; size_t v___x_1120_; lean_object* v___x_1121_; 
v_v_1113_ = lean_array_uget(v_bs_1111_, v_i_1110_);
v___x_1114_ = lean_unsigned_to_nat(0u);
v_bs_x27_1115_ = lean_array_uset(v_bs_1111_, v_i_1110_, v___x_1114_);
v___x_1116_ = 1;
v___x_1117_ = lean_box(v___x_1116_);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
lean_ctor_set(v___x_1118_, 1, v_v_1113_);
v___x_1119_ = ((size_t)1ULL);
v___x_1120_ = lean_usize_add(v_i_1110_, v___x_1119_);
v___x_1121_ = lean_array_uset(v_bs_x27_1115_, v_i_1110_, v___x_1118_);
v_i_1110_ = v___x_1120_;
v_bs_1111_ = v___x_1121_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8___boxed(lean_object* v_sz_1123_, lean_object* v_i_1124_, lean_object* v_bs_1125_){
_start:
{
size_t v_sz_boxed_1126_; size_t v_i_boxed_1127_; lean_object* v_res_1128_; 
v_sz_boxed_1126_ = lean_unbox_usize(v_sz_1123_);
lean_dec(v_sz_1123_);
v_i_boxed_1127_ = lean_unbox_usize(v_i_1124_);
lean_dec(v_i_1124_);
v_res_1128_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(v_sz_boxed_1126_, v_i_boxed_1127_, v_bs_1125_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(uint32_t v_inst_1129_, lean_object* v_edited_1130_, lean_object* v___x_1131_, uint32_t v_a_1132_, lean_object* v_b_1133_){
_start:
{
lean_object* v_fst_1134_; lean_object* v_snd_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1162_; 
v_fst_1134_ = lean_ctor_get(v_b_1133_, 0);
v_snd_1135_ = lean_ctor_get(v_b_1133_, 1);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_b_1133_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1137_ = v_b_1133_;
v_isShared_1138_ = v_isSharedCheck_1162_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_snd_1135_);
lean_inc(v_fst_1134_);
lean_dec(v_b_1133_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1162_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
uint8_t v___y_1140_; uint8_t v___x_1156_; 
v___x_1156_ = lean_nat_dec_lt(v_snd_1135_, v___x_1131_);
if (v___x_1156_ == 0)
{
v___y_1140_ = v___x_1156_;
goto v___jp_1139_;
}
else
{
lean_object* v___x_1157_; lean_object* v___x_1158_; uint32_t v___x_1159_; uint8_t v___x_1160_; 
v___x_1157_ = lean_box_uint32(v_inst_1129_);
v___x_1158_ = lean_array_get_borrowed(v___x_1157_, v_edited_1130_, v_snd_1135_);
v___x_1159_ = lean_unbox_uint32(v___x_1158_);
v___x_1160_ = lean_uint32_dec_eq(v___x_1159_, v_a_1132_);
if (v___x_1160_ == 0)
{
v___y_1140_ = v___x_1156_;
goto v___jp_1139_;
}
else
{
lean_object* v___x_1161_; 
lean_del_object(v___x_1137_);
v___x_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1161_, 0, v_fst_1134_);
lean_ctor_set(v___x_1161_, 1, v_snd_1135_);
return v___x_1161_;
}
}
v___jp_1139_:
{
if (v___y_1140_ == 0)
{
lean_object* v___x_1142_; 
if (v_isShared_1138_ == 0)
{
v___x_1142_ = v___x_1137_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_fst_1134_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_snd_1135_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
else
{
uint8_t v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1149_; 
v___x_1144_ = 0;
v___x_1145_ = lean_box_uint32(v_inst_1129_);
v___x_1146_ = lean_array_get_borrowed(v___x_1145_, v_edited_1130_, v_snd_1135_);
v___x_1147_ = lean_box(v___x_1144_);
lean_inc(v___x_1146_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 1, v___x_1146_);
lean_ctor_set(v___x_1137_, 0, v___x_1147_);
v___x_1149_ = v___x_1137_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1147_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v___x_1146_);
v___x_1149_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1150_ = lean_array_push(v_fst_1134_, v___x_1149_);
v___x_1151_ = lean_unsigned_to_nat(1u);
v___x_1152_ = lean_nat_add(v_snd_1135_, v___x_1151_);
lean_dec(v_snd_1135_);
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1150_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v_b_1133_ = v___x_1153_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed(lean_object* v_inst_1163_, lean_object* v_edited_1164_, lean_object* v___x_1165_, lean_object* v_a_1166_, lean_object* v_b_1167_){
_start:
{
uint32_t v_inst_5252__boxed_1168_; uint32_t v_a_boxed_1169_; lean_object* v_res_1170_; 
v_inst_5252__boxed_1168_ = lean_unbox_uint32(v_inst_1163_);
lean_dec(v_inst_1163_);
v_a_boxed_1169_ = lean_unbox_uint32(v_a_1166_);
lean_dec(v_a_1166_);
v_res_1170_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v_inst_5252__boxed_1168_, v_edited_1164_, v___x_1165_, v_a_boxed_1169_, v_b_1167_);
lean_dec(v___x_1165_);
lean_dec_ref(v_edited_1164_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(uint32_t v_inst_1171_, lean_object* v_original_1172_, lean_object* v___x_1173_, uint32_t v_a_1174_, lean_object* v_b_1175_){
_start:
{
lean_object* v_fst_1176_; lean_object* v_snd_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1204_; 
v_fst_1176_ = lean_ctor_get(v_b_1175_, 0);
v_snd_1177_ = lean_ctor_get(v_b_1175_, 1);
v_isSharedCheck_1204_ = !lean_is_exclusive(v_b_1175_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1179_ = v_b_1175_;
v_isShared_1180_ = v_isSharedCheck_1204_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_snd_1177_);
lean_inc(v_fst_1176_);
lean_dec(v_b_1175_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1204_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
uint8_t v___y_1182_; uint8_t v___x_1198_; 
v___x_1198_ = lean_nat_dec_lt(v_snd_1177_, v___x_1173_);
if (v___x_1198_ == 0)
{
v___y_1182_ = v___x_1198_;
goto v___jp_1181_;
}
else
{
lean_object* v___x_1199_; lean_object* v___x_1200_; uint32_t v___x_1201_; uint8_t v___x_1202_; 
v___x_1199_ = lean_box_uint32(v_inst_1171_);
v___x_1200_ = lean_array_get_borrowed(v___x_1199_, v_original_1172_, v_snd_1177_);
v___x_1201_ = lean_unbox_uint32(v___x_1200_);
v___x_1202_ = lean_uint32_dec_eq(v___x_1201_, v_a_1174_);
if (v___x_1202_ == 0)
{
v___y_1182_ = v___x_1198_;
goto v___jp_1181_;
}
else
{
lean_object* v___x_1203_; 
lean_del_object(v___x_1179_);
v___x_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1203_, 0, v_fst_1176_);
lean_ctor_set(v___x_1203_, 1, v_snd_1177_);
return v___x_1203_;
}
}
v___jp_1181_:
{
if (v___y_1182_ == 0)
{
lean_object* v___x_1184_; 
if (v_isShared_1180_ == 0)
{
v___x_1184_ = v___x_1179_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_fst_1176_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_snd_1177_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
else
{
uint8_t v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1191_; 
v___x_1186_ = 1;
v___x_1187_ = lean_box_uint32(v_inst_1171_);
v___x_1188_ = lean_array_get_borrowed(v___x_1187_, v_original_1172_, v_snd_1177_);
v___x_1189_ = lean_box(v___x_1186_);
lean_inc(v___x_1188_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 1, v___x_1188_);
lean_ctor_set(v___x_1179_, 0, v___x_1189_);
v___x_1191_ = v___x_1179_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v___x_1189_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v___x_1188_);
v___x_1191_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1192_ = lean_array_push(v_fst_1176_, v___x_1191_);
v___x_1193_ = lean_unsigned_to_nat(1u);
v___x_1194_ = lean_nat_add(v_snd_1177_, v___x_1193_);
lean_dec(v_snd_1177_);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1192_);
lean_ctor_set(v___x_1195_, 1, v___x_1194_);
v_b_1175_ = v___x_1195_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___boxed(lean_object* v_inst_1205_, lean_object* v_original_1206_, lean_object* v___x_1207_, lean_object* v_a_1208_, lean_object* v_b_1209_){
_start:
{
uint32_t v_inst_5312__boxed_1210_; uint32_t v_a_boxed_1211_; lean_object* v_res_1212_; 
v_inst_5312__boxed_1210_ = lean_unbox_uint32(v_inst_1205_);
lean_dec(v_inst_1205_);
v_a_boxed_1211_ = lean_unbox_uint32(v_a_1208_);
lean_dec(v_a_1208_);
v_res_1212_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(v_inst_5312__boxed_1210_, v_original_1206_, v___x_1207_, v_a_boxed_1211_, v_b_1209_);
lean_dec(v___x_1207_);
lean_dec_ref(v_original_1206_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(uint32_t v_inst_1213_, lean_object* v_original_1214_, lean_object* v___x_1215_, lean_object* v_edited_1216_, lean_object* v___x_1217_, lean_object* v_as_1218_, size_t v_sz_1219_, size_t v_i_1220_, lean_object* v_b_1221_){
_start:
{
uint8_t v___x_1222_; 
v___x_1222_ = lean_usize_dec_lt(v_i_1220_, v_sz_1219_);
if (v___x_1222_ == 0)
{
return v_b_1221_;
}
else
{
lean_object* v_snd_1223_; lean_object* v_fst_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1273_; 
v_snd_1223_ = lean_ctor_get(v_b_1221_, 1);
v_fst_1224_ = lean_ctor_get(v_b_1221_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_b_1221_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1226_ = v_b_1221_;
v_isShared_1227_ = v_isSharedCheck_1273_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_snd_1223_);
lean_inc(v_fst_1224_);
lean_dec(v_b_1221_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1273_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v_fst_1228_; lean_object* v_snd_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1272_; 
v_fst_1228_ = lean_ctor_get(v_snd_1223_, 0);
v_snd_1229_ = lean_ctor_get(v_snd_1223_, 1);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_snd_1223_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1231_ = v_snd_1223_;
v_isShared_1232_ = v_isSharedCheck_1272_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_snd_1229_);
lean_inc(v_fst_1228_);
lean_dec(v_snd_1223_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1272_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v_a_1233_; lean_object* v___x_1235_; 
v_a_1233_ = lean_array_uget_borrowed(v_as_1218_, v_i_1220_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v_fst_1228_);
lean_ctor_set(v___x_1231_, 0, v_fst_1224_);
v___x_1235_ = v___x_1231_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_fst_1224_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_fst_1228_);
v___x_1235_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
uint32_t v___x_1236_; lean_object* v___x_1237_; lean_object* v_fst_1238_; lean_object* v_snd_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1270_; 
v___x_1236_ = lean_unbox_uint32(v_a_1233_);
v___x_1237_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(v_inst_1213_, v_original_1214_, v___x_1215_, v___x_1236_, v___x_1235_);
v_fst_1238_ = lean_ctor_get(v___x_1237_, 0);
v_snd_1239_ = lean_ctor_get(v___x_1237_, 1);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1241_ = v___x_1237_;
v_isShared_1242_ = v_isSharedCheck_1270_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_snd_1239_);
lean_inc(v_fst_1238_);
lean_dec(v___x_1237_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1270_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
lean_ctor_set(v___x_1241_, 1, v_snd_1229_);
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_fst_1238_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_snd_1229_);
v___x_1244_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
uint32_t v___x_1245_; lean_object* v___x_1246_; lean_object* v_fst_1247_; lean_object* v_snd_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1268_; 
v___x_1245_ = lean_unbox_uint32(v_a_1233_);
v___x_1246_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v_inst_1213_, v_edited_1216_, v___x_1217_, v___x_1245_, v___x_1244_);
v_fst_1247_ = lean_ctor_get(v___x_1246_, 0);
v_snd_1248_ = lean_ctor_get(v___x_1246_, 1);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1250_ = v___x_1246_;
v_isShared_1251_ = v_isSharedCheck_1268_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_snd_1248_);
lean_inc(v_fst_1247_);
lean_dec(v___x_1246_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1268_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
uint8_t v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1252_ = 2;
v___x_1253_ = lean_box(v___x_1252_);
lean_inc(v_a_1233_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 1, v_a_1233_);
lean_ctor_set(v___x_1250_, 0, v___x_1253_);
v___x_1255_ = v___x_1250_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1253_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v_a_1233_);
v___x_1255_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1256_ = lean_array_push(v_fst_1247_, v___x_1255_);
v___x_1257_ = lean_unsigned_to_nat(1u);
v___x_1258_ = lean_nat_add(v_snd_1239_, v___x_1257_);
lean_dec(v_snd_1239_);
v___x_1259_ = lean_nat_add(v_snd_1248_, v___x_1257_);
lean_dec(v_snd_1248_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 1, v___x_1259_);
lean_ctor_set(v___x_1226_, 0, v___x_1258_);
v___x_1261_ = v___x_1226_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1262_; size_t v___x_1263_; size_t v___x_1264_; 
v___x_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1256_);
lean_ctor_set(v___x_1262_, 1, v___x_1261_);
v___x_1263_ = ((size_t)1ULL);
v___x_1264_ = lean_usize_add(v_i_1220_, v___x_1263_);
v_i_1220_ = v___x_1264_;
v_b_1221_ = v___x_1262_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15___boxed(lean_object* v_inst_1274_, lean_object* v_original_1275_, lean_object* v___x_1276_, lean_object* v_edited_1277_, lean_object* v___x_1278_, lean_object* v_as_1279_, lean_object* v_sz_1280_, lean_object* v_i_1281_, lean_object* v_b_1282_){
_start:
{
uint32_t v_inst_5372__boxed_1283_; size_t v_sz_boxed_1284_; size_t v_i_boxed_1285_; lean_object* v_res_1286_; 
v_inst_5372__boxed_1283_ = lean_unbox_uint32(v_inst_1274_);
lean_dec(v_inst_1274_);
v_sz_boxed_1284_ = lean_unbox_usize(v_sz_1280_);
lean_dec(v_sz_1280_);
v_i_boxed_1285_ = lean_unbox_usize(v_i_1281_);
lean_dec(v_i_1281_);
v_res_1286_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(v_inst_5372__boxed_1283_, v_original_1275_, v___x_1276_, v_edited_1277_, v___x_1278_, v_as_1279_, v_sz_boxed_1284_, v_i_boxed_1285_, v_b_1282_);
lean_dec_ref(v_as_1279_);
lean_dec(v___x_1278_);
lean_dec_ref(v_edited_1277_);
lean_dec(v___x_1276_);
lean_dec_ref(v_original_1275_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(uint32_t v_inst_1287_, lean_object* v_edited_1288_, lean_object* v___x_1289_, lean_object* v_original_1290_, lean_object* v___x_1291_, lean_object* v_as_1292_, size_t v_sz_1293_, size_t v_i_1294_, lean_object* v_b_1295_){
_start:
{
uint8_t v___x_1296_; 
v___x_1296_ = lean_usize_dec_lt(v_i_1294_, v_sz_1293_);
if (v___x_1296_ == 0)
{
return v_b_1295_;
}
else
{
lean_object* v_snd_1297_; lean_object* v_fst_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1347_; 
v_snd_1297_ = lean_ctor_get(v_b_1295_, 1);
v_fst_1298_ = lean_ctor_get(v_b_1295_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_b_1295_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1300_ = v_b_1295_;
v_isShared_1301_ = v_isSharedCheck_1347_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_snd_1297_);
lean_inc(v_fst_1298_);
lean_dec(v_b_1295_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1347_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v_fst_1302_; lean_object* v_snd_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1346_; 
v_fst_1302_ = lean_ctor_get(v_snd_1297_, 0);
v_snd_1303_ = lean_ctor_get(v_snd_1297_, 1);
v_isSharedCheck_1346_ = !lean_is_exclusive(v_snd_1297_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1305_ = v_snd_1297_;
v_isShared_1306_ = v_isSharedCheck_1346_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_snd_1303_);
lean_inc(v_fst_1302_);
lean_dec(v_snd_1297_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1346_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v_a_1307_; lean_object* v___x_1309_; 
v_a_1307_ = lean_array_uget_borrowed(v_as_1292_, v_i_1294_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 1, v_fst_1302_);
lean_ctor_set(v___x_1305_, 0, v_fst_1298_);
v___x_1309_ = v___x_1305_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_fst_1298_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v_fst_1302_);
v___x_1309_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
uint32_t v___x_1310_; lean_object* v___x_1311_; lean_object* v_fst_1312_; lean_object* v_snd_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1344_; 
v___x_1310_ = lean_unbox_uint32(v_a_1307_);
v___x_1311_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(v_inst_1287_, v_original_1290_, v___x_1291_, v___x_1310_, v___x_1309_);
v_fst_1312_ = lean_ctor_get(v___x_1311_, 0);
v_snd_1313_ = lean_ctor_get(v___x_1311_, 1);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1315_ = v___x_1311_;
v_isShared_1316_ = v_isSharedCheck_1344_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_snd_1313_);
lean_inc(v_fst_1312_);
lean_dec(v___x_1311_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1344_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 1, v_snd_1303_);
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_fst_1312_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_snd_1303_);
v___x_1318_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
uint32_t v___x_1319_; lean_object* v___x_1320_; lean_object* v_fst_1321_; lean_object* v_snd_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1342_; 
v___x_1319_ = lean_unbox_uint32(v_a_1307_);
v___x_1320_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v_inst_1287_, v_edited_1288_, v___x_1289_, v___x_1319_, v___x_1318_);
v_fst_1321_ = lean_ctor_get(v___x_1320_, 0);
v_snd_1322_ = lean_ctor_get(v___x_1320_, 1);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1324_ = v___x_1320_;
v_isShared_1325_ = v_isSharedCheck_1342_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_snd_1322_);
lean_inc(v_fst_1321_);
lean_dec(v___x_1320_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1342_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
uint8_t v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1329_; 
v___x_1326_ = 2;
v___x_1327_ = lean_box(v___x_1326_);
lean_inc(v_a_1307_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 1, v_a_1307_);
lean_ctor_set(v___x_1324_, 0, v___x_1327_);
v___x_1329_ = v___x_1324_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_a_1307_);
v___x_1329_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___x_1330_ = lean_array_push(v_fst_1321_, v___x_1329_);
v___x_1331_ = lean_unsigned_to_nat(1u);
v___x_1332_ = lean_nat_add(v_snd_1313_, v___x_1331_);
lean_dec(v_snd_1313_);
v___x_1333_ = lean_nat_add(v_snd_1322_, v___x_1331_);
lean_dec(v_snd_1322_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 1, v___x_1333_);
lean_ctor_set(v___x_1300_, 0, v___x_1332_);
v___x_1335_ = v___x_1300_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1332_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
lean_object* v___x_1336_; size_t v___x_1337_; size_t v___x_1338_; lean_object* v___x_1339_; 
v___x_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1330_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
v___x_1337_ = ((size_t)1ULL);
v___x_1338_ = lean_usize_add(v_i_1294_, v___x_1337_);
v___x_1339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(v_inst_1287_, v_original_1290_, v___x_1291_, v_edited_1288_, v___x_1289_, v_as_1292_, v_sz_1293_, v___x_1338_, v___x_1336_);
return v___x_1339_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5___boxed(lean_object* v_inst_1348_, lean_object* v_edited_1349_, lean_object* v___x_1350_, lean_object* v_original_1351_, lean_object* v___x_1352_, lean_object* v_as_1353_, lean_object* v_sz_1354_, lean_object* v_i_1355_, lean_object* v_b_1356_){
_start:
{
uint32_t v_inst_5467__boxed_1357_; size_t v_sz_boxed_1358_; size_t v_i_boxed_1359_; lean_object* v_res_1360_; 
v_inst_5467__boxed_1357_ = lean_unbox_uint32(v_inst_1348_);
lean_dec(v_inst_1348_);
v_sz_boxed_1358_ = lean_unbox_usize(v_sz_1354_);
lean_dec(v_sz_1354_);
v_i_boxed_1359_ = lean_unbox_usize(v_i_1355_);
lean_dec(v_i_1355_);
v_res_1360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v_inst_5467__boxed_1357_, v_edited_1349_, v___x_1350_, v_original_1351_, v___x_1352_, v_as_1353_, v_sz_boxed_1358_, v_i_boxed_1359_, v_b_1356_);
lean_dec_ref(v_as_1353_);
lean_dec(v___x_1352_);
lean_dec_ref(v_original_1351_);
lean_dec(v___x_1350_);
lean_dec_ref(v_edited_1349_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(uint32_t v_inst_1368_, lean_object* v_original_1369_, lean_object* v_edited_1370_){
_start:
{
lean_object* v_i_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v_i_1371_ = lean_unsigned_to_nat(0u);
v___x_1372_ = lean_array_get_size(v_original_1369_);
v___x_1373_ = lean_nat_dec_lt(v_i_1371_, v___x_1372_);
if (v___x_1373_ == 0)
{
size_t v_sz_1374_; size_t v___x_1375_; lean_object* v___x_1376_; 
lean_dec_ref(v_original_1369_);
v_sz_1374_ = lean_array_size(v_edited_1370_);
v___x_1375_ = ((size_t)0ULL);
v___x_1376_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(v_sz_1374_, v___x_1375_, v_edited_1370_);
return v___x_1376_;
}
else
{
lean_object* v___x_1377_; uint8_t v___x_1378_; 
v___x_1377_ = lean_array_get_size(v_edited_1370_);
v___x_1378_ = lean_nat_dec_lt(v_i_1371_, v___x_1377_);
if (v___x_1378_ == 0)
{
size_t v_sz_1379_; size_t v___x_1380_; lean_object* v___x_1381_; 
lean_dec_ref(v_edited_1370_);
v_sz_1379_ = lean_array_size(v_original_1369_);
v___x_1380_ = ((size_t)0ULL);
v___x_1381_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(v_sz_1379_, v___x_1380_, v_original_1369_);
return v___x_1381_;
}
else
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v_ds_1384_; lean_object* v___x_1385_; size_t v_sz_1386_; size_t v___x_1387_; lean_object* v___x_1388_; lean_object* v_snd_1389_; lean_object* v_fst_1390_; lean_object* v_fst_1391_; lean_object* v_snd_1392_; lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1411_; 
lean_inc_ref(v_original_1369_);
v___x_1382_ = l_Array_toSubarray___redArg(v_original_1369_, v_i_1371_, v___x_1372_);
lean_inc_ref(v_edited_1370_);
v___x_1383_ = l_Array_toSubarray___redArg(v_edited_1370_, v_i_1371_, v___x_1377_);
v_ds_1384_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v___x_1382_, v___x_1383_);
v___x_1385_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__2));
v_sz_1386_ = lean_array_size(v_ds_1384_);
v___x_1387_ = ((size_t)0ULL);
v___x_1388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v_inst_1368_, v_edited_1370_, v___x_1377_, v_original_1369_, v___x_1372_, v_ds_1384_, v_sz_1386_, v___x_1387_, v___x_1385_);
lean_dec_ref(v_ds_1384_);
v_snd_1389_ = lean_ctor_get(v___x_1388_, 1);
lean_inc(v_snd_1389_);
v_fst_1390_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_fst_1390_);
lean_dec_ref(v___x_1388_);
v_fst_1391_ = lean_ctor_get(v_snd_1389_, 0);
v_snd_1392_ = lean_ctor_get(v_snd_1389_, 1);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_snd_1389_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1394_ = v_snd_1389_;
v_isShared_1395_ = v_isSharedCheck_1411_;
goto v_resetjp_1393_;
}
else
{
lean_inc(v_snd_1392_);
lean_inc(v_fst_1391_);
lean_dec(v_snd_1389_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1411_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1397_; 
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 1, v_fst_1391_);
lean_ctor_set(v___x_1394_, 0, v_fst_1390_);
v___x_1397_ = v___x_1394_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_fst_1390_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_fst_1391_);
v___x_1397_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_object* v___x_1398_; lean_object* v_fst_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1408_; 
v___x_1398_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(v___x_1372_, v_original_1369_, v___x_1397_);
lean_dec_ref(v_original_1369_);
v_fst_1399_ = lean_ctor_get(v___x_1398_, 0);
v_isSharedCheck_1408_ = !lean_is_exclusive(v___x_1398_);
if (v_isSharedCheck_1408_ == 0)
{
lean_object* v_unused_1409_; 
v_unused_1409_ = lean_ctor_get(v___x_1398_, 1);
lean_dec(v_unused_1409_);
v___x_1401_ = v___x_1398_;
v_isShared_1402_ = v_isSharedCheck_1408_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_fst_1399_);
lean_dec(v___x_1398_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1408_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1404_; 
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 1, v_snd_1392_);
v___x_1404_ = v___x_1401_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_fst_1399_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_snd_1392_);
v___x_1404_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; lean_object* v_fst_1406_; 
v___x_1405_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(v___x_1377_, v_edited_1370_, v___x_1404_);
lean_dec_ref(v_edited_1370_);
v_fst_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_fst_1406_);
lean_dec_ref(v___x_1405_);
return v_fst_1406_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___boxed(lean_object* v_inst_1412_, lean_object* v_original_1413_, lean_object* v_edited_1414_){
_start:
{
uint32_t v_inst_5568__boxed_1415_; lean_object* v_res_1416_; 
v_inst_5568__boxed_1415_ = lean_unbox_uint32(v_inst_1412_);
lean_dec(v_inst_1412_);
v_res_1416_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v_inst_5568__boxed_1415_, v_original_1413_, v_edited_1414_);
return v_res_1416_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(lean_object* v_s_1417_, lean_object* v_a_1418_, uint8_t v_b_1419_){
_start:
{
lean_object* v_str_1420_; lean_object* v_startInclusive_1421_; lean_object* v_endExclusive_1422_; lean_object* v___x_1423_; uint8_t v___x_1424_; 
v_str_1420_ = lean_ctor_get(v_s_1417_, 0);
v_startInclusive_1421_ = lean_ctor_get(v_s_1417_, 1);
v_endExclusive_1422_ = lean_ctor_get(v_s_1417_, 2);
v___x_1423_ = lean_nat_sub(v_endExclusive_1422_, v_startInclusive_1421_);
v___x_1424_ = lean_nat_dec_eq(v_a_1418_, v___x_1423_);
lean_dec(v___x_1423_);
if (v___x_1424_ == 0)
{
lean_object* v___x_1425_; uint32_t v___x_1426_; uint32_t v___x_1427_; uint8_t v___x_1428_; 
v___x_1425_ = lean_nat_add(v_startInclusive_1421_, v_a_1418_);
lean_dec(v_a_1418_);
v___x_1426_ = lean_string_utf8_get_fast(v_str_1420_, v___x_1425_);
v___x_1427_ = 10;
v___x_1428_ = lean_uint32_dec_eq(v___x_1426_, v___x_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = lean_string_utf8_next_fast(v_str_1420_, v___x_1425_);
lean_dec(v___x_1425_);
v___x_1430_ = lean_nat_sub(v___x_1429_, v_startInclusive_1421_);
v_a_1418_ = v___x_1430_;
v_b_1419_ = v___x_1428_;
goto _start;
}
else
{
lean_dec(v___x_1425_);
return v___x_1428_;
}
}
else
{
lean_dec(v_a_1418_);
return v_b_1419_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg___boxed(lean_object* v_s_1432_, lean_object* v_a_1433_, lean_object* v_b_1434_){
_start:
{
uint8_t v_b_boxed_1435_; uint8_t v_res_1436_; lean_object* v_r_1437_; 
v_b_boxed_1435_ = lean_unbox(v_b_1434_);
v_res_1436_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1432_, v_a_1433_, v_b_boxed_1435_);
lean_dec_ref(v_s_1432_);
v_r_1437_ = lean_box(v_res_1436_);
return v_r_1437_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(lean_object* v_s_1438_){
_start:
{
lean_object* v_searcher_1439_; uint8_t v___x_1440_; uint8_t v___x_1441_; 
v_searcher_1439_ = lean_unsigned_to_nat(0u);
v___x_1440_ = 0;
v___x_1441_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1438_, v_searcher_1439_, v___x_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0___boxed(lean_object* v_s_1442_){
_start:
{
uint8_t v_res_1443_; lean_object* v_r_1444_; 
v_res_1443_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v_s_1442_);
lean_dec_ref(v_s_1442_);
v_r_1444_ = lean_box(v_res_1443_);
return v_r_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(lean_object* v_oldWs_1445_, lean_object* v_newWs_1446_){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v___x_1447_ = lean_unsigned_to_nat(0u);
v___x_1448_ = lean_string_utf8_byte_size(v_oldWs_1445_);
lean_inc_ref(v_oldWs_1445_);
v___x_1449_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1449_, 0, v_oldWs_1445_);
lean_ctor_set(v___x_1449_, 1, v___x_1447_);
lean_ctor_set(v___x_1449_, 2, v___x_1448_);
v___x_1450_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_1449_);
lean_dec_ref(v___x_1449_);
if (v___x_1450_ == 0)
{
uint32_t v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1451_ = 65;
v___x_1452_ = lean_string_data(v_oldWs_1445_);
v___x_1453_ = lean_array_mk(v___x_1452_);
v___x_1454_ = lean_string_data(v_newWs_1446_);
v___x_1455_ = lean_array_mk(v___x_1454_);
v___x_1456_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_1451_, v___x_1453_, v___x_1455_);
v___x_1457_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_1456_);
lean_dec_ref(v___x_1456_);
return v___x_1457_;
}
else
{
uint8_t v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; 
lean_dec_ref(v_oldWs_1445_);
v___x_1458_ = 2;
v___x_1459_ = lean_box(v___x_1458_);
v___x_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
lean_ctor_set(v___x_1460_, 1, v_newWs_1446_);
v___x_1461_ = lean_unsigned_to_nat(1u);
v___x_1462_ = lean_mk_empty_array_with_capacity(v___x_1461_);
v___x_1463_ = lean_array_push(v___x_1462_, v___x_1460_);
return v___x_1463_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(lean_object* v_s_1464_, lean_object* v_inst_1465_, lean_object* v_R_1466_, lean_object* v_a_1467_, uint8_t v_b_1468_, lean_object* v_c_1469_){
_start:
{
uint8_t v___x_1470_; 
v___x_1470_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1464_, v_a_1467_, v_b_1468_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___boxed(lean_object* v_s_1471_, lean_object* v_inst_1472_, lean_object* v_R_1473_, lean_object* v_a_1474_, lean_object* v_b_1475_, lean_object* v_c_1476_){
_start:
{
uint8_t v_b_boxed_1477_; uint8_t v_res_1478_; lean_object* v_r_1479_; 
v_b_boxed_1477_ = lean_unbox(v_b_1475_);
v_res_1478_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(v_s_1471_, v_inst_1472_, v_R_1473_, v_a_1474_, v_b_boxed_1477_, v_c_1476_);
lean_dec_ref(v_s_1471_);
v_r_1479_ = lean_box(v_res_1478_);
return v_r_1479_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5(lean_object* v_as_1480_, lean_object* v_as_x27_1481_, lean_object* v_b_1482_, lean_object* v_a_1483_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg(v_as_x27_1481_, v_b_1482_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___boxed(lean_object* v_as_1485_, lean_object* v_as_x27_1486_, lean_object* v_b_1487_, lean_object* v_a_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5(v_as_1485_, v_as_x27_1486_, v_b_1487_, v_a_1488_);
lean_dec(v_as_1485_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8(lean_object* v_lsize_1490_, lean_object* v_rsize_1491_, lean_object* v_histogram_1492_, lean_object* v_index_1493_, uint32_t v_val_1494_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(v_histogram_1492_, v_index_1493_, v_val_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___boxed(lean_object* v_lsize_1496_, lean_object* v_rsize_1497_, lean_object* v_histogram_1498_, lean_object* v_index_1499_, lean_object* v_val_1500_){
_start:
{
uint32_t v_val_boxed_1501_; lean_object* v_res_1502_; 
v_val_boxed_1501_ = lean_unbox_uint32(v_val_1500_);
lean_dec(v_val_1500_);
v_res_1502_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8(v_lsize_1496_, v_rsize_1497_, v_histogram_1498_, v_index_1499_, v_val_boxed_1501_);
lean_dec(v_rsize_1497_);
lean_dec(v_lsize_1496_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9(lean_object* v_upperBound_1503_, lean_object* v___x_1504_, lean_object* v_fst_1505_, lean_object* v___x_1506_, lean_object* v_inst_1507_, lean_object* v_R_1508_, lean_object* v_a_1509_, lean_object* v_b_1510_, lean_object* v_c_1511_){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(v_upperBound_1503_, v___x_1504_, v_fst_1505_, v___x_1506_, v_a_1509_, v_b_1510_);
return v___x_1512_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___boxed(lean_object* v_upperBound_1513_, lean_object* v___x_1514_, lean_object* v_fst_1515_, lean_object* v___x_1516_, lean_object* v_inst_1517_, lean_object* v_R_1518_, lean_object* v_a_1519_, lean_object* v_b_1520_, lean_object* v_c_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9(v_upperBound_1513_, v___x_1514_, v_fst_1515_, v___x_1516_, v_inst_1517_, v_R_1518_, v_a_1519_, v_b_1520_, v_c_1521_);
lean_dec(v___x_1516_);
lean_dec_ref(v_fst_1515_);
lean_dec(v___x_1514_);
lean_dec(v_upperBound_1513_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10(lean_object* v_lsize_1523_, lean_object* v_rsize_1524_, lean_object* v_histogram_1525_, lean_object* v_index_1526_, uint32_t v_val_1527_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(v_histogram_1525_, v_index_1526_, v_val_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___boxed(lean_object* v_lsize_1529_, lean_object* v_rsize_1530_, lean_object* v_histogram_1531_, lean_object* v_index_1532_, lean_object* v_val_1533_){
_start:
{
uint32_t v_val_boxed_1534_; lean_object* v_res_1535_; 
v_val_boxed_1534_ = lean_unbox_uint32(v_val_1533_);
lean_dec(v_val_1533_);
v_res_1535_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10(v_lsize_1529_, v_rsize_1530_, v_histogram_1531_, v_index_1532_, v_val_boxed_1534_);
lean_dec(v_rsize_1530_);
lean_dec(v_lsize_1529_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11(lean_object* v_upperBound_1536_, lean_object* v_fst_1537_, lean_object* v___x_1538_, lean_object* v_fst_1539_, lean_object* v_inst_1540_, lean_object* v_R_1541_, lean_object* v_a_1542_, lean_object* v_b_1543_, lean_object* v_c_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg(v_upperBound_1536_, v_fst_1537_, v___x_1538_, v_fst_1539_, v_a_1542_, v_b_1543_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___boxed(lean_object* v_upperBound_1546_, lean_object* v_fst_1547_, lean_object* v___x_1548_, lean_object* v_fst_1549_, lean_object* v_inst_1550_, lean_object* v_R_1551_, lean_object* v_a_1552_, lean_object* v_b_1553_, lean_object* v_c_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11(v_upperBound_1546_, v_fst_1547_, v___x_1548_, v_fst_1549_, v_inst_1550_, v_R_1551_, v_a_1552_, v_b_1553_, v_c_1554_);
lean_dec_ref(v_fst_1549_);
lean_dec(v___x_1548_);
lean_dec_ref(v_fst_1547_);
lean_dec(v_upperBound_1546_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11(lean_object* v_00_u03b2_1556_, lean_object* v_m_1557_, uint32_t v_a_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(v_m_1557_, v_a_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___boxed(lean_object* v_00_u03b2_1560_, lean_object* v_m_1561_, lean_object* v_a_1562_){
_start:
{
uint32_t v_a_boxed_1563_; lean_object* v_res_1564_; 
v_a_boxed_1563_ = lean_unbox_uint32(v_a_1562_);
lean_dec(v_a_1562_);
v_res_1564_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11(v_00_u03b2_1560_, v_m_1561_, v_a_boxed_1563_);
lean_dec_ref(v_m_1561_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12(lean_object* v_00_u03b2_1565_, lean_object* v_m_1566_, uint32_t v_a_1567_, lean_object* v_b_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_m_1566_, v_a_1567_, v_b_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___boxed(lean_object* v_00_u03b2_1570_, lean_object* v_m_1571_, lean_object* v_a_1572_, lean_object* v_b_1573_){
_start:
{
uint32_t v_a_boxed_1574_; lean_object* v_res_1575_; 
v_a_boxed_1574_ = lean_unbox_uint32(v_a_1572_);
lean_dec(v_a_1572_);
v_res_1575_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12(v_00_u03b2_1570_, v_m_1571_, v_a_boxed_1574_, v_b_1573_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14(lean_object* v_inst_1576_, lean_object* v_R_1577_, lean_object* v_a_1578_, lean_object* v_b_1579_){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(v_a_1578_, v_b_1579_);
return v___x_1580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20(lean_object* v_00_u03b2_1581_, uint32_t v_a_1582_, lean_object* v_x_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg(v_a_1582_, v_x_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___boxed(lean_object* v_00_u03b2_1585_, lean_object* v_a_1586_, lean_object* v_x_1587_){
_start:
{
uint32_t v_a_boxed_1588_; lean_object* v_res_1589_; 
v_a_boxed_1588_ = lean_unbox_uint32(v_a_1586_);
lean_dec(v_a_1586_);
v_res_1589_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20(v_00_u03b2_1585_, v_a_boxed_1588_, v_x_1587_);
lean_dec(v_x_1587_);
return v_res_1589_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22(lean_object* v_00_u03b2_1590_, uint32_t v_a_1591_, lean_object* v_x_1592_){
_start:
{
uint8_t v___x_1593_; 
v___x_1593_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg(v_a_1591_, v_x_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___boxed(lean_object* v_00_u03b2_1594_, lean_object* v_a_1595_, lean_object* v_x_1596_){
_start:
{
uint32_t v_a_boxed_1597_; uint8_t v_res_1598_; lean_object* v_r_1599_; 
v_a_boxed_1597_ = lean_unbox_uint32(v_a_1595_);
lean_dec(v_a_1595_);
v_res_1598_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22(v_00_u03b2_1594_, v_a_boxed_1597_, v_x_1596_);
lean_dec(v_x_1596_);
v_r_1599_ = lean_box(v_res_1598_);
return v_r_1599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23(lean_object* v_00_u03b2_1600_, lean_object* v_data_1601_){
_start:
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23___redArg(v_data_1601_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24(lean_object* v_00_u03b2_1603_, uint32_t v_a_1604_, lean_object* v_b_1605_, lean_object* v_x_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(v_a_1604_, v_b_1605_, v_x_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___boxed(lean_object* v_00_u03b2_1608_, lean_object* v_a_1609_, lean_object* v_b_1610_, lean_object* v_x_1611_){
_start:
{
uint32_t v_a_boxed_1612_; lean_object* v_res_1613_; 
v_a_boxed_1612_ = lean_unbox_uint32(v_a_1609_);
lean_dec(v_a_1609_);
v_res_1613_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24(v_00_u03b2_1608_, v_a_boxed_1612_, v_b_1610_, v_x_1611_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28(lean_object* v_00_u03b2_1614_, lean_object* v_i_1615_, lean_object* v_source_1616_, lean_object* v_target_1617_){
_start:
{
lean_object* v___x_1618_; 
v___x_1618_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28___redArg(v_i_1615_, v_source_1616_, v_target_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_1619_, lean_object* v_x_1620_, lean_object* v_x_1621_){
_start:
{
lean_object* v___x_1622_; 
v___x_1622_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29___redArg(v_x_1620_, v_x_1621_);
return v___x_1622_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(lean_object* v_s_1623_, lean_object* v_stopPos_1624_, lean_object* v_i_1625_){
_start:
{
uint8_t v___y_1630_; uint8_t v___x_1631_; 
v___x_1631_ = lean_nat_dec_lt(v_i_1625_, v_stopPos_1624_);
if (v___x_1631_ == 0)
{
return v_i_1625_;
}
else
{
uint32_t v___x_1632_; uint8_t v___y_1634_; uint32_t v___x_1639_; uint8_t v___x_1640_; 
v___x_1632_ = lean_string_utf8_get(v_s_1623_, v_i_1625_);
v___x_1639_ = 32;
v___x_1640_ = lean_uint32_dec_eq(v___x_1632_, v___x_1639_);
if (v___x_1640_ == 0)
{
uint32_t v___x_1641_; uint8_t v___x_1642_; 
v___x_1641_ = 9;
v___x_1642_ = lean_uint32_dec_eq(v___x_1632_, v___x_1641_);
v___y_1634_ = v___x_1642_;
goto v___jp_1633_;
}
else
{
v___y_1634_ = v___x_1640_;
goto v___jp_1633_;
}
v___jp_1633_:
{
if (v___y_1634_ == 0)
{
uint32_t v___x_1635_; uint8_t v___x_1636_; 
v___x_1635_ = 13;
v___x_1636_ = lean_uint32_dec_eq(v___x_1632_, v___x_1635_);
if (v___x_1636_ == 0)
{
uint32_t v___x_1637_; uint8_t v___x_1638_; 
v___x_1637_ = 10;
v___x_1638_ = lean_uint32_dec_eq(v___x_1632_, v___x_1637_);
v___y_1630_ = v___x_1638_;
goto v___jp_1629_;
}
else
{
v___y_1630_ = v___x_1636_;
goto v___jp_1629_;
}
}
else
{
goto v___jp_1626_;
}
}
}
v___jp_1626_:
{
lean_object* v___x_1627_; 
v___x_1627_ = lean_string_utf8_next(v_s_1623_, v_i_1625_);
lean_dec(v_i_1625_);
v_i_1625_ = v___x_1627_;
goto _start;
}
v___jp_1629_:
{
if (v___y_1630_ == 0)
{
return v_i_1625_;
}
else
{
goto v___jp_1626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0___boxed(lean_object* v_s_1643_, lean_object* v_stopPos_1644_, lean_object* v_i_1645_){
_start:
{
lean_object* v_res_1646_; 
v_res_1646_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1643_, v_stopPos_1644_, v_i_1645_);
lean_dec(v_stopPos_1644_);
lean_dec_ref(v_s_1643_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(lean_object* v_s_1647_, lean_object* v_b_1648_, lean_object* v_i_1649_, lean_object* v_r_1650_, lean_object* v_ws_1651_){
_start:
{
uint8_t v___y_1661_; uint8_t v___x_1664_; 
v___x_1664_ = lean_string_utf8_at_end(v_s_1647_, v_i_1649_);
if (v___x_1664_ == 0)
{
uint32_t v___x_1665_; uint8_t v___y_1667_; uint32_t v___x_1672_; uint8_t v___x_1673_; 
v___x_1665_ = lean_string_utf8_get(v_s_1647_, v_i_1649_);
v___x_1672_ = 32;
v___x_1673_ = lean_uint32_dec_eq(v___x_1665_, v___x_1672_);
if (v___x_1673_ == 0)
{
uint32_t v___x_1674_; uint8_t v___x_1675_; 
v___x_1674_ = 9;
v___x_1675_ = lean_uint32_dec_eq(v___x_1665_, v___x_1674_);
v___y_1667_ = v___x_1675_;
goto v___jp_1666_;
}
else
{
v___y_1667_ = v___x_1673_;
goto v___jp_1666_;
}
v___jp_1666_:
{
if (v___y_1667_ == 0)
{
uint32_t v___x_1668_; uint8_t v___x_1669_; 
v___x_1668_ = 13;
v___x_1669_ = lean_uint32_dec_eq(v___x_1665_, v___x_1668_);
if (v___x_1669_ == 0)
{
uint32_t v___x_1670_; uint8_t v___x_1671_; 
v___x_1670_ = 10;
v___x_1671_ = lean_uint32_dec_eq(v___x_1665_, v___x_1670_);
v___y_1661_ = v___x_1671_;
goto v___jp_1660_;
}
else
{
v___y_1661_ = v___x_1669_;
goto v___jp_1660_;
}
}
else
{
goto v___jp_1652_;
}
}
}
else
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1676_ = lean_string_utf8_extract(v_s_1647_, v_b_1648_, v_i_1649_);
lean_dec(v_i_1649_);
lean_dec(v_b_1648_);
v___x_1677_ = lean_array_push(v_r_1650_, v___x_1676_);
v___x_1678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
lean_ctor_set(v___x_1678_, 1, v_ws_1651_);
return v___x_1678_;
}
v___jp_1652_:
{
lean_object* v___x_1653_; lean_object* v_e_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1653_ = lean_string_utf8_byte_size(v_s_1647_);
lean_inc(v_i_1649_);
v_e_1654_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1647_, v___x_1653_, v_i_1649_);
v___x_1655_ = lean_string_utf8_extract(v_s_1647_, v_b_1648_, v_i_1649_);
lean_dec(v_b_1648_);
v___x_1656_ = lean_array_push(v_r_1650_, v___x_1655_);
v___x_1657_ = lean_string_utf8_extract(v_s_1647_, v_i_1649_, v_e_1654_);
lean_dec(v_i_1649_);
v___x_1658_ = lean_array_push(v_ws_1651_, v___x_1657_);
lean_inc(v_e_1654_);
v_b_1648_ = v_e_1654_;
v_i_1649_ = v_e_1654_;
v_r_1650_ = v___x_1656_;
v_ws_1651_ = v___x_1658_;
goto _start;
}
v___jp_1660_:
{
if (v___y_1661_ == 0)
{
lean_object* v___x_1662_; 
v___x_1662_ = lean_string_utf8_next(v_s_1647_, v_i_1649_);
lean_dec(v_i_1649_);
v_i_1649_ = v___x_1662_;
goto _start;
}
else
{
goto v___jp_1652_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux___boxed(lean_object* v_s_1679_, lean_object* v_b_1680_, lean_object* v_i_1681_, lean_object* v_r_1682_, lean_object* v_ws_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1679_, v_b_1680_, v_i_1681_, v_r_1682_, v_ws_1683_);
lean_dec_ref(v_s_1679_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(lean_object* v_s_1687_){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1688_ = lean_unsigned_to_nat(0u);
v___x_1689_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_1690_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1687_, v___x_1688_, v___x_1688_, v___x_1689_, v___x_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___boxed(lean_object* v_s_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_1691_);
lean_dec_ref(v_s_1691_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(size_t v_sz_1693_, size_t v_i_1694_, lean_object* v_bs_1695_){
_start:
{
uint8_t v___x_1696_; 
v___x_1696_ = lean_usize_dec_lt(v_i_1694_, v_sz_1693_);
if (v___x_1696_ == 0)
{
return v_bs_1695_;
}
else
{
lean_object* v_v_1697_; lean_object* v_fst_1698_; lean_object* v_snd_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1733_; 
v_v_1697_ = lean_array_uget(v_bs_1695_, v_i_1694_);
v_fst_1698_ = lean_ctor_get(v_v_1697_, 0);
v_snd_1699_ = lean_ctor_get(v_v_1697_, 1);
v_isSharedCheck_1733_ = !lean_is_exclusive(v_v_1697_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1701_ = v_v_1697_;
v_isShared_1702_ = v_isSharedCheck_1733_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_snd_1699_);
lean_inc(v_fst_1698_);
lean_dec(v_v_1697_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1733_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
lean_object* v___x_1703_; lean_object* v_bs_x27_1704_; lean_object* v___y_1706_; lean_object* v___x_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; 
v___x_1703_ = lean_unsigned_to_nat(0u);
v_bs_x27_1704_ = lean_array_uset(v_bs_1695_, v_i_1694_, v___x_1703_);
v___x_1711_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_1712_ = lean_array_get_size(v_snd_1699_);
v___x_1713_ = lean_nat_dec_lt(v___x_1703_, v___x_1712_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1715_; 
lean_dec(v_snd_1699_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 1, v___x_1711_);
v___x_1715_ = v___x_1701_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_fst_1698_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v___x_1711_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
v___y_1706_ = v___x_1715_;
goto v___jp_1705_;
}
}
else
{
uint8_t v___x_1717_; 
v___x_1717_ = lean_nat_dec_le(v___x_1712_, v___x_1712_);
if (v___x_1717_ == 0)
{
if (v___x_1713_ == 0)
{
lean_object* v___x_1719_; 
lean_dec(v_snd_1699_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 1, v___x_1711_);
v___x_1719_ = v___x_1701_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_fst_1698_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v___x_1711_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
v___y_1706_ = v___x_1719_;
goto v___jp_1705_;
}
}
else
{
size_t v___x_1721_; size_t v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1725_; 
v___x_1721_ = ((size_t)0ULL);
v___x_1722_ = lean_usize_of_nat(v___x_1712_);
v___x_1723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_1699_, v___x_1721_, v___x_1722_, v___x_1711_);
lean_dec(v_snd_1699_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 1, v___x_1723_);
v___x_1725_ = v___x_1701_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_fst_1698_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v___x_1723_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
v___y_1706_ = v___x_1725_;
goto v___jp_1705_;
}
}
}
else
{
size_t v___x_1727_; size_t v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1727_ = ((size_t)0ULL);
v___x_1728_ = lean_usize_of_nat(v___x_1712_);
v___x_1729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_1699_, v___x_1727_, v___x_1728_, v___x_1711_);
lean_dec(v_snd_1699_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 1, v___x_1729_);
v___x_1731_ = v___x_1701_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_fst_1698_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v___x_1729_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
v___y_1706_ = v___x_1731_;
goto v___jp_1705_;
}
}
}
v___jp_1705_:
{
size_t v___x_1707_; size_t v___x_1708_; lean_object* v___x_1709_; 
v___x_1707_ = ((size_t)1ULL);
v___x_1708_ = lean_usize_add(v_i_1694_, v___x_1707_);
v___x_1709_ = lean_array_uset(v_bs_x27_1704_, v_i_1694_, v___y_1706_);
v_i_1694_ = v___x_1708_;
v_bs_1695_ = v___x_1709_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0___boxed(lean_object* v_sz_1734_, lean_object* v_i_1735_, lean_object* v_bs_1736_){
_start:
{
size_t v_sz_boxed_1737_; size_t v_i_boxed_1738_; lean_object* v_res_1739_; 
v_sz_boxed_1737_ = lean_unbox_usize(v_sz_1734_);
lean_dec(v_sz_1734_);
v_i_boxed_1738_ = lean_unbox_usize(v_i_1735_);
lean_dec(v_i_1735_);
v_res_1739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_boxed_1737_, v_i_boxed_1738_, v_bs_1736_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(size_t v_sz_1740_, size_t v_i_1741_, lean_object* v_bs_1742_){
_start:
{
uint8_t v___x_1743_; 
v___x_1743_ = lean_usize_dec_lt(v_i_1741_, v_sz_1740_);
if (v___x_1743_ == 0)
{
return v_bs_1742_;
}
else
{
lean_object* v_v_1744_; lean_object* v___x_1745_; lean_object* v_bs_x27_1746_; uint8_t v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; size_t v___x_1750_; size_t v___x_1751_; lean_object* v___x_1752_; 
v_v_1744_ = lean_array_uget(v_bs_1742_, v_i_1741_);
v___x_1745_ = lean_unsigned_to_nat(0u);
v_bs_x27_1746_ = lean_array_uset(v_bs_1742_, v_i_1741_, v___x_1745_);
v___x_1747_ = 0;
v___x_1748_ = lean_box(v___x_1747_);
v___x_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
lean_ctor_set(v___x_1749_, 1, v_v_1744_);
v___x_1750_ = ((size_t)1ULL);
v___x_1751_ = lean_usize_add(v_i_1741_, v___x_1750_);
v___x_1752_ = lean_array_uset(v_bs_x27_1746_, v_i_1741_, v___x_1749_);
v_i_1741_ = v___x_1751_;
v_bs_1742_ = v___x_1752_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8___boxed(lean_object* v_sz_1754_, lean_object* v_i_1755_, lean_object* v_bs_1756_){
_start:
{
size_t v_sz_boxed_1757_; size_t v_i_boxed_1758_; lean_object* v_res_1759_; 
v_sz_boxed_1757_ = lean_unbox_usize(v_sz_1754_);
lean_dec(v_sz_1754_);
v_i_boxed_1758_ = lean_unbox_usize(v_i_1755_);
lean_dec(v_i_1755_);
v_res_1759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_boxed_1757_, v_i_boxed_1758_, v_bs_1756_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(lean_object* v_inst_1760_, lean_object* v_original_1761_, lean_object* v___x_1762_, lean_object* v_a_1763_, lean_object* v_b_1764_){
_start:
{
lean_object* v_fst_1765_; lean_object* v_snd_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1790_; 
v_fst_1765_ = lean_ctor_get(v_b_1764_, 0);
v_snd_1766_ = lean_ctor_get(v_b_1764_, 1);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_b_1764_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1768_ = v_b_1764_;
v_isShared_1769_ = v_isSharedCheck_1790_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_snd_1766_);
lean_inc(v_fst_1765_);
lean_dec(v_b_1764_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1790_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
uint8_t v___y_1771_; uint8_t v___x_1786_; 
v___x_1786_ = lean_nat_dec_lt(v_snd_1766_, v___x_1762_);
if (v___x_1786_ == 0)
{
v___y_1771_ = v___x_1786_;
goto v___jp_1770_;
}
else
{
lean_object* v___x_1787_; uint8_t v___x_1788_; 
lean_inc_ref(v_inst_1760_);
v___x_1787_ = lean_array_get_borrowed(v_inst_1760_, v_original_1761_, v_snd_1766_);
v___x_1788_ = lean_string_dec_eq(v___x_1787_, v_a_1763_);
if (v___x_1788_ == 0)
{
v___y_1771_ = v___x_1786_;
goto v___jp_1770_;
}
else
{
lean_object* v___x_1789_; 
lean_del_object(v___x_1768_);
lean_dec_ref(v_inst_1760_);
v___x_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1789_, 0, v_fst_1765_);
lean_ctor_set(v___x_1789_, 1, v_snd_1766_);
return v___x_1789_;
}
}
v___jp_1770_:
{
if (v___y_1771_ == 0)
{
lean_object* v___x_1773_; 
lean_dec_ref(v_inst_1760_);
if (v_isShared_1769_ == 0)
{
v___x_1773_ = v___x_1768_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_fst_1765_);
lean_ctor_set(v_reuseFailAlloc_1774_, 1, v_snd_1766_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
else
{
uint8_t v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1775_ = 1;
lean_inc_ref(v_inst_1760_);
v___x_1776_ = lean_array_get_borrowed(v_inst_1760_, v_original_1761_, v_snd_1766_);
v___x_1777_ = lean_box(v___x_1775_);
lean_inc(v___x_1776_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 1, v___x_1776_);
lean_ctor_set(v___x_1768_, 0, v___x_1777_);
v___x_1779_ = v___x_1768_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1777_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v___x_1776_);
v___x_1779_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1780_ = lean_array_push(v_fst_1765_, v___x_1779_);
v___x_1781_ = lean_unsigned_to_nat(1u);
v___x_1782_ = lean_nat_add(v_snd_1766_, v___x_1781_);
lean_dec(v_snd_1766_);
v___x_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1780_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
v_b_1764_ = v___x_1783_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___boxed(lean_object* v_inst_1791_, lean_object* v_original_1792_, lean_object* v___x_1793_, lean_object* v_a_1794_, lean_object* v_b_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(v_inst_1791_, v_original_1792_, v___x_1793_, v_a_1794_, v_b_1795_);
lean_dec_ref(v_a_1794_);
lean_dec(v___x_1793_);
lean_dec_ref(v_original_1792_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(lean_object* v_inst_1797_, lean_object* v_edited_1798_, lean_object* v___x_1799_, lean_object* v_a_1800_, lean_object* v_b_1801_){
_start:
{
lean_object* v_fst_1802_; lean_object* v_snd_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1827_; 
v_fst_1802_ = lean_ctor_get(v_b_1801_, 0);
v_snd_1803_ = lean_ctor_get(v_b_1801_, 1);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_b_1801_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1805_ = v_b_1801_;
v_isShared_1806_ = v_isSharedCheck_1827_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_snd_1803_);
lean_inc(v_fst_1802_);
lean_dec(v_b_1801_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1827_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
uint8_t v___y_1808_; uint8_t v___x_1823_; 
v___x_1823_ = lean_nat_dec_lt(v_snd_1803_, v___x_1799_);
if (v___x_1823_ == 0)
{
v___y_1808_ = v___x_1823_;
goto v___jp_1807_;
}
else
{
lean_object* v___x_1824_; uint8_t v___x_1825_; 
lean_inc_ref(v_inst_1797_);
v___x_1824_ = lean_array_get_borrowed(v_inst_1797_, v_edited_1798_, v_snd_1803_);
v___x_1825_ = lean_string_dec_eq(v___x_1824_, v_a_1800_);
if (v___x_1825_ == 0)
{
v___y_1808_ = v___x_1823_;
goto v___jp_1807_;
}
else
{
lean_object* v___x_1826_; 
lean_del_object(v___x_1805_);
lean_dec_ref(v_inst_1797_);
v___x_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1826_, 0, v_fst_1802_);
lean_ctor_set(v___x_1826_, 1, v_snd_1803_);
return v___x_1826_;
}
}
v___jp_1807_:
{
if (v___y_1808_ == 0)
{
lean_object* v___x_1810_; 
lean_dec_ref(v_inst_1797_);
if (v_isShared_1806_ == 0)
{
v___x_1810_ = v___x_1805_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1811_; 
v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_fst_1802_);
lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_snd_1803_);
v___x_1810_ = v_reuseFailAlloc_1811_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
return v___x_1810_;
}
}
else
{
uint8_t v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1812_ = 0;
lean_inc_ref(v_inst_1797_);
v___x_1813_ = lean_array_get_borrowed(v_inst_1797_, v_edited_1798_, v_snd_1803_);
v___x_1814_ = lean_box(v___x_1812_);
lean_inc(v___x_1813_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 1, v___x_1813_);
lean_ctor_set(v___x_1805_, 0, v___x_1814_);
v___x_1816_ = v___x_1805_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1814_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v___x_1813_);
v___x_1816_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1817_ = lean_array_push(v_fst_1802_, v___x_1816_);
v___x_1818_ = lean_unsigned_to_nat(1u);
v___x_1819_ = lean_nat_add(v_snd_1803_, v___x_1818_);
lean_dec(v_snd_1803_);
v___x_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1817_);
lean_ctor_set(v___x_1820_, 1, v___x_1819_);
v_b_1801_ = v___x_1820_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___boxed(lean_object* v_inst_1828_, lean_object* v_edited_1829_, lean_object* v___x_1830_, lean_object* v_a_1831_, lean_object* v_b_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v_inst_1828_, v_edited_1829_, v___x_1830_, v_a_1831_, v_b_1832_);
lean_dec_ref(v_a_1831_);
lean_dec(v___x_1830_);
lean_dec_ref(v_edited_1829_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(lean_object* v_inst_1834_, lean_object* v_original_1835_, lean_object* v___x_1836_, lean_object* v_edited_1837_, lean_object* v___x_1838_, lean_object* v_as_1839_, size_t v_sz_1840_, size_t v_i_1841_, lean_object* v_b_1842_){
_start:
{
uint8_t v___x_1843_; 
v___x_1843_ = lean_usize_dec_lt(v_i_1841_, v_sz_1840_);
if (v___x_1843_ == 0)
{
lean_dec_ref(v_inst_1834_);
return v_b_1842_;
}
else
{
lean_object* v_snd_1844_; lean_object* v_fst_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1892_; 
v_snd_1844_ = lean_ctor_get(v_b_1842_, 1);
v_fst_1845_ = lean_ctor_get(v_b_1842_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_b_1842_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1847_ = v_b_1842_;
v_isShared_1848_ = v_isSharedCheck_1892_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_snd_1844_);
lean_inc(v_fst_1845_);
lean_dec(v_b_1842_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1892_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v_fst_1849_; lean_object* v_snd_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1891_; 
v_fst_1849_ = lean_ctor_get(v_snd_1844_, 0);
v_snd_1850_ = lean_ctor_get(v_snd_1844_, 1);
v_isSharedCheck_1891_ = !lean_is_exclusive(v_snd_1844_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1852_ = v_snd_1844_;
v_isShared_1853_ = v_isSharedCheck_1891_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_snd_1850_);
lean_inc(v_fst_1849_);
lean_dec(v_snd_1844_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1891_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v_a_1854_; lean_object* v___x_1856_; 
v_a_1854_ = lean_array_uget_borrowed(v_as_1839_, v_i_1841_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 1, v_fst_1849_);
lean_ctor_set(v___x_1852_, 0, v_fst_1845_);
v___x_1856_ = v___x_1852_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_fst_1845_);
lean_ctor_set(v_reuseFailAlloc_1890_, 1, v_fst_1849_);
v___x_1856_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
lean_object* v___x_1857_; lean_object* v_fst_1858_; lean_object* v_snd_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1889_; 
lean_inc_ref(v_inst_1834_);
v___x_1857_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(v_inst_1834_, v_original_1835_, v___x_1836_, v_a_1854_, v___x_1856_);
v_fst_1858_ = lean_ctor_get(v___x_1857_, 0);
v_snd_1859_ = lean_ctor_get(v___x_1857_, 1);
v_isSharedCheck_1889_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1889_ == 0)
{
v___x_1861_ = v___x_1857_;
v_isShared_1862_ = v_isSharedCheck_1889_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_snd_1859_);
lean_inc(v_fst_1858_);
lean_dec(v___x_1857_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1889_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1864_; 
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 1, v_snd_1850_);
v___x_1864_ = v___x_1861_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v_fst_1858_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v_snd_1850_);
v___x_1864_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
lean_object* v___x_1865_; lean_object* v_fst_1866_; lean_object* v_snd_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1887_; 
lean_inc_ref(v_inst_1834_);
v___x_1865_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v_inst_1834_, v_edited_1837_, v___x_1838_, v_a_1854_, v___x_1864_);
v_fst_1866_ = lean_ctor_get(v___x_1865_, 0);
v_snd_1867_ = lean_ctor_get(v___x_1865_, 1);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1869_ = v___x_1865_;
v_isShared_1870_ = v_isSharedCheck_1887_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_snd_1867_);
lean_inc(v_fst_1866_);
lean_dec(v___x_1865_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1887_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
uint8_t v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1871_ = 2;
v___x_1872_ = lean_box(v___x_1871_);
lean_inc(v_a_1854_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 1, v_a_1854_);
lean_ctor_set(v___x_1869_, 0, v___x_1872_);
v___x_1874_ = v___x_1869_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v___x_1872_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_a_1854_);
v___x_1874_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1875_ = lean_array_push(v_fst_1866_, v___x_1874_);
v___x_1876_ = lean_unsigned_to_nat(1u);
v___x_1877_ = lean_nat_add(v_snd_1859_, v___x_1876_);
lean_dec(v_snd_1859_);
v___x_1878_ = lean_nat_add(v_snd_1867_, v___x_1876_);
lean_dec(v_snd_1867_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 1, v___x_1878_);
lean_ctor_set(v___x_1847_, 0, v___x_1877_);
v___x_1880_ = v___x_1847_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1885_; 
v_reuseFailAlloc_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1885_, 0, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_1885_, 1, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1885_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
lean_object* v___x_1881_; size_t v___x_1882_; size_t v___x_1883_; 
v___x_1881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1881_, 0, v___x_1875_);
lean_ctor_set(v___x_1881_, 1, v___x_1880_);
v___x_1882_ = ((size_t)1ULL);
v___x_1883_ = lean_usize_add(v_i_1841_, v___x_1882_);
v_i_1841_ = v___x_1883_;
v_b_1842_ = v___x_1881_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14___boxed(lean_object* v_inst_1893_, lean_object* v_original_1894_, lean_object* v___x_1895_, lean_object* v_edited_1896_, lean_object* v___x_1897_, lean_object* v_as_1898_, lean_object* v_sz_1899_, lean_object* v_i_1900_, lean_object* v_b_1901_){
_start:
{
size_t v_sz_boxed_1902_; size_t v_i_boxed_1903_; lean_object* v_res_1904_; 
v_sz_boxed_1902_ = lean_unbox_usize(v_sz_1899_);
lean_dec(v_sz_1899_);
v_i_boxed_1903_ = lean_unbox_usize(v_i_1900_);
lean_dec(v_i_1900_);
v_res_1904_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v_inst_1893_, v_original_1894_, v___x_1895_, v_edited_1896_, v___x_1897_, v_as_1898_, v_sz_boxed_1902_, v_i_boxed_1903_, v_b_1901_);
lean_dec_ref(v_as_1898_);
lean_dec(v___x_1897_);
lean_dec_ref(v_edited_1896_);
lean_dec(v___x_1895_);
lean_dec_ref(v_original_1894_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(lean_object* v_inst_1905_, lean_object* v_edited_1906_, lean_object* v___x_1907_, lean_object* v_original_1908_, lean_object* v___x_1909_, lean_object* v_as_1910_, size_t v_sz_1911_, size_t v_i_1912_, lean_object* v_b_1913_){
_start:
{
uint8_t v___x_1914_; 
v___x_1914_ = lean_usize_dec_lt(v_i_1912_, v_sz_1911_);
if (v___x_1914_ == 0)
{
lean_dec_ref(v_inst_1905_);
return v_b_1913_;
}
else
{
lean_object* v_snd_1915_; lean_object* v_fst_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1963_; 
v_snd_1915_ = lean_ctor_get(v_b_1913_, 1);
v_fst_1916_ = lean_ctor_get(v_b_1913_, 0);
v_isSharedCheck_1963_ = !lean_is_exclusive(v_b_1913_);
if (v_isSharedCheck_1963_ == 0)
{
v___x_1918_ = v_b_1913_;
v_isShared_1919_ = v_isSharedCheck_1963_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_snd_1915_);
lean_inc(v_fst_1916_);
lean_dec(v_b_1913_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1963_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v_fst_1920_; lean_object* v_snd_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1962_; 
v_fst_1920_ = lean_ctor_get(v_snd_1915_, 0);
v_snd_1921_ = lean_ctor_get(v_snd_1915_, 1);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_snd_1915_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1923_ = v_snd_1915_;
v_isShared_1924_ = v_isSharedCheck_1962_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_snd_1921_);
lean_inc(v_fst_1920_);
lean_dec(v_snd_1915_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1962_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v_a_1925_; lean_object* v___x_1927_; 
v_a_1925_ = lean_array_uget_borrowed(v_as_1910_, v_i_1912_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 1, v_fst_1920_);
lean_ctor_set(v___x_1923_, 0, v_fst_1916_);
v___x_1927_ = v___x_1923_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_fst_1916_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_fst_1920_);
v___x_1927_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1928_; lean_object* v_fst_1929_; lean_object* v_snd_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1960_; 
lean_inc_ref(v_inst_1905_);
v___x_1928_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(v_inst_1905_, v_original_1908_, v___x_1909_, v_a_1925_, v___x_1927_);
v_fst_1929_ = lean_ctor_get(v___x_1928_, 0);
v_snd_1930_ = lean_ctor_get(v___x_1928_, 1);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1932_ = v___x_1928_;
v_isShared_1933_ = v_isSharedCheck_1960_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_snd_1930_);
lean_inc(v_fst_1929_);
lean_dec(v___x_1928_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1960_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
lean_ctor_set(v___x_1932_, 1, v_snd_1921_);
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_fst_1929_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_snd_1921_);
v___x_1935_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1936_; lean_object* v_fst_1937_; lean_object* v_snd_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1958_; 
lean_inc_ref(v_inst_1905_);
v___x_1936_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v_inst_1905_, v_edited_1906_, v___x_1907_, v_a_1925_, v___x_1935_);
v_fst_1937_ = lean_ctor_get(v___x_1936_, 0);
v_snd_1938_ = lean_ctor_get(v___x_1936_, 1);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1936_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1940_ = v___x_1936_;
v_isShared_1941_ = v_isSharedCheck_1958_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_snd_1938_);
lean_inc(v_fst_1937_);
lean_dec(v___x_1936_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1958_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
uint8_t v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1945_; 
v___x_1942_ = 2;
v___x_1943_ = lean_box(v___x_1942_);
lean_inc(v_a_1925_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 1, v_a_1925_);
lean_ctor_set(v___x_1940_, 0, v___x_1943_);
v___x_1945_ = v___x_1940_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1943_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_a_1925_);
v___x_1945_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1951_; 
v___x_1946_ = lean_array_push(v_fst_1937_, v___x_1945_);
v___x_1947_ = lean_unsigned_to_nat(1u);
v___x_1948_ = lean_nat_add(v_snd_1930_, v___x_1947_);
lean_dec(v_snd_1930_);
v___x_1949_ = lean_nat_add(v_snd_1938_, v___x_1947_);
lean_dec(v_snd_1938_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 1, v___x_1949_);
lean_ctor_set(v___x_1918_, 0, v___x_1948_);
v___x_1951_ = v___x_1918_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1948_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v___x_1949_);
v___x_1951_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
lean_object* v___x_1952_; size_t v___x_1953_; size_t v___x_1954_; lean_object* v___x_1955_; 
v___x_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1946_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = ((size_t)1ULL);
v___x_1954_ = lean_usize_add(v_i_1912_, v___x_1953_);
v___x_1955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v_inst_1905_, v_original_1908_, v___x_1909_, v_edited_1906_, v___x_1907_, v_as_1910_, v_sz_1911_, v___x_1954_, v___x_1952_);
return v___x_1955_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4___boxed(lean_object* v_inst_1964_, lean_object* v_edited_1965_, lean_object* v___x_1966_, lean_object* v_original_1967_, lean_object* v___x_1968_, lean_object* v_as_1969_, lean_object* v_sz_1970_, lean_object* v_i_1971_, lean_object* v_b_1972_){
_start:
{
size_t v_sz_boxed_1973_; size_t v_i_boxed_1974_; lean_object* v_res_1975_; 
v_sz_boxed_1973_ = lean_unbox_usize(v_sz_1970_);
lean_dec(v_sz_1970_);
v_i_boxed_1974_ = lean_unbox_usize(v_i_1971_);
lean_dec(v_i_1971_);
v_res_1975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v_inst_1964_, v_edited_1965_, v___x_1966_, v_original_1967_, v___x_1968_, v_as_1969_, v_sz_boxed_1973_, v_i_boxed_1974_, v_b_1972_);
lean_dec_ref(v_as_1969_);
lean_dec(v___x_1968_);
lean_dec_ref(v_original_1967_);
lean_dec(v___x_1966_);
lean_dec_ref(v_edited_1965_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(lean_object* v_a_1976_, lean_object* v_b_1977_){
_start:
{
lean_object* v_array_1978_; lean_object* v_start_1979_; lean_object* v_stop_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1993_; 
v_array_1978_ = lean_ctor_get(v_a_1976_, 0);
v_start_1979_ = lean_ctor_get(v_a_1976_, 1);
v_stop_1980_ = lean_ctor_get(v_a_1976_, 2);
v_isSharedCheck_1993_ = !lean_is_exclusive(v_a_1976_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1982_ = v_a_1976_;
v_isShared_1983_ = v_isSharedCheck_1993_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_stop_1980_);
lean_inc(v_start_1979_);
lean_inc(v_array_1978_);
lean_dec(v_a_1976_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1993_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
uint8_t v___x_1984_; 
v___x_1984_ = lean_nat_dec_lt(v_start_1979_, v_stop_1980_);
if (v___x_1984_ == 0)
{
lean_del_object(v___x_1982_);
lean_dec(v_stop_1980_);
lean_dec(v_start_1979_);
lean_dec_ref(v_array_1978_);
return v_b_1977_;
}
else
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1988_; 
v___x_1985_ = lean_unsigned_to_nat(1u);
v___x_1986_ = lean_nat_add(v_start_1979_, v___x_1985_);
lean_inc_ref(v_array_1978_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 1, v___x_1986_);
v___x_1988_ = v___x_1982_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_array_1978_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v___x_1986_);
lean_ctor_set(v_reuseFailAlloc_1992_, 2, v_stop_1980_);
v___x_1988_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = lean_array_fget(v_array_1978_, v_start_1979_);
lean_dec(v_start_1979_);
lean_dec_ref(v_array_1978_);
v___x_1990_ = lean_array_push(v_b_1977_, v___x_1989_);
v_a_1976_ = v___x_1988_;
v_b_1977_ = v___x_1990_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6(lean_object* v_left_1994_, lean_object* v_right_1995_, lean_object* v_i_1996_){
_start:
{
lean_object* v_start_1997_; lean_object* v_stop_1998_; lean_object* v___x_1999_; uint8_t v___x_2013_; 
v_start_1997_ = lean_ctor_get(v_left_1994_, 1);
v_stop_1998_ = lean_ctor_get(v_left_1994_, 2);
v___x_1999_ = lean_nat_sub(v_stop_1998_, v_start_1997_);
v___x_2013_ = lean_nat_dec_lt(v_i_1996_, v___x_1999_);
if (v___x_2013_ == 0)
{
goto v___jp_2000_;
}
else
{
lean_object* v_start_2014_; lean_object* v_stop_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; 
v_start_2014_ = lean_ctor_get(v_right_1995_, 1);
v_stop_2015_ = lean_ctor_get(v_right_1995_, 2);
v___x_2016_ = lean_nat_sub(v_stop_2015_, v_start_2014_);
v___x_2017_ = lean_nat_dec_lt(v_i_1996_, v___x_2016_);
if (v___x_2017_ == 0)
{
lean_dec(v___x_2016_);
goto v___jp_2000_;
}
else
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; uint8_t v___x_2025_; 
v___x_2018_ = lean_nat_sub(v___x_1999_, v_i_1996_);
lean_dec(v___x_1999_);
v___x_2019_ = lean_unsigned_to_nat(1u);
v___x_2020_ = lean_nat_sub(v___x_2018_, v___x_2019_);
v___x_2021_ = l_Subarray_get___redArg(v_left_1994_, v___x_2020_);
lean_dec(v___x_2020_);
v___x_2022_ = lean_nat_sub(v___x_2016_, v_i_1996_);
lean_dec(v___x_2016_);
v___x_2023_ = lean_nat_sub(v___x_2022_, v___x_2019_);
v___x_2024_ = l_Subarray_get___redArg(v_right_1995_, v___x_2023_);
lean_dec(v___x_2023_);
v___x_2025_ = lean_string_dec_eq(v___x_2021_, v___x_2024_);
lean_dec(v___x_2024_);
lean_dec(v___x_2021_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
lean_dec(v_i_1996_);
lean_inc_ref(v_left_1994_);
v___x_2026_ = l_Subarray_take___redArg(v_left_1994_, v___x_2018_);
v___x_2027_ = l_Subarray_take___redArg(v_right_1995_, v___x_2022_);
lean_dec(v___x_2022_);
v___x_2028_ = l_Subarray_drop___redArg(v_left_1994_, v___x_2018_);
lean_dec(v___x_2018_);
v___x_2029_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2030_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v___x_2028_, v___x_2029_);
v___x_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2027_);
lean_ctor_set(v___x_2031_, 1, v___x_2030_);
v___x_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2026_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
return v___x_2032_;
}
else
{
lean_object* v___x_2033_; 
lean_dec(v___x_2022_);
lean_dec(v___x_2018_);
v___x_2033_ = lean_nat_add(v_i_1996_, v___x_2019_);
lean_dec(v_i_1996_);
v_i_1996_ = v___x_2033_;
goto _start;
}
}
}
v___jp_2000_:
{
lean_object* v_start_2001_; lean_object* v_stop_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v_start_2001_ = lean_ctor_get(v_right_1995_, 1);
v_stop_2002_ = lean_ctor_get(v_right_1995_, 2);
v___x_2003_ = lean_nat_sub(v___x_1999_, v_i_1996_);
lean_dec(v___x_1999_);
lean_inc_ref(v_left_1994_);
v___x_2004_ = l_Subarray_take___redArg(v_left_1994_, v___x_2003_);
v___x_2005_ = lean_nat_sub(v_stop_2002_, v_start_2001_);
v___x_2006_ = lean_nat_sub(v___x_2005_, v_i_1996_);
lean_dec(v_i_1996_);
lean_dec(v___x_2005_);
v___x_2007_ = l_Subarray_take___redArg(v_right_1995_, v___x_2006_);
lean_dec(v___x_2006_);
v___x_2008_ = l_Subarray_drop___redArg(v_left_1994_, v___x_2003_);
lean_dec(v___x_2003_);
v___x_2009_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2010_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v___x_2008_, v___x_2009_);
v___x_2011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2011_, 0, v___x_2007_);
lean_ctor_set(v___x_2011_, 1, v___x_2010_);
v___x_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2012_, 0, v___x_2004_);
lean_ctor_set(v___x_2012_, 1, v___x_2011_);
return v___x_2012_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3(lean_object* v_left_2035_, lean_object* v_right_2036_){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2037_ = lean_unsigned_to_nat(0u);
v___x_2038_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6(v_left_2035_, v_right_2036_, v___x_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2_spec__4(lean_object* v_left_2039_, lean_object* v_right_2040_, lean_object* v_pref_2041_){
_start:
{
lean_object* v_start_2042_; lean_object* v_stop_2043_; lean_object* v_i_2044_; lean_object* v___x_2050_; uint8_t v___x_2051_; 
v_start_2042_ = lean_ctor_get(v_left_2039_, 1);
v_stop_2043_ = lean_ctor_get(v_left_2039_, 2);
v_i_2044_ = lean_array_get_size(v_pref_2041_);
v___x_2050_ = lean_nat_sub(v_stop_2043_, v_start_2042_);
v___x_2051_ = lean_nat_dec_lt(v_i_2044_, v___x_2050_);
lean_dec(v___x_2050_);
if (v___x_2051_ == 0)
{
goto v___jp_2045_;
}
else
{
lean_object* v_start_2052_; lean_object* v_stop_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; 
v_start_2052_ = lean_ctor_get(v_right_2040_, 1);
v_stop_2053_ = lean_ctor_get(v_right_2040_, 2);
v___x_2054_ = lean_nat_sub(v_stop_2053_, v_start_2052_);
v___x_2055_ = lean_nat_dec_lt(v_i_2044_, v___x_2054_);
lean_dec(v___x_2054_);
if (v___x_2055_ == 0)
{
goto v___jp_2045_;
}
else
{
lean_object* v___x_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v___x_2056_ = l_Subarray_get___redArg(v_left_2039_, v_i_2044_);
v___x_2057_ = l_Subarray_get___redArg(v_right_2040_, v_i_2044_);
v___x_2058_ = lean_string_dec_eq(v___x_2056_, v___x_2057_);
lean_dec(v___x_2057_);
if (v___x_2058_ == 0)
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
lean_dec(v___x_2056_);
v___x_2059_ = l_Subarray_drop___redArg(v_left_2039_, v_i_2044_);
v___x_2060_ = l_Subarray_drop___redArg(v_right_2040_, v_i_2044_);
v___x_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2059_);
lean_ctor_set(v___x_2061_, 1, v___x_2060_);
v___x_2062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2062_, 0, v_pref_2041_);
lean_ctor_set(v___x_2062_, 1, v___x_2061_);
return v___x_2062_;
}
else
{
lean_object* v___x_2063_; 
v___x_2063_ = lean_array_push(v_pref_2041_, v___x_2056_);
v_pref_2041_ = v___x_2063_;
goto _start;
}
}
}
v___jp_2045_:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2046_ = l_Subarray_drop___redArg(v_left_2039_, v_i_2044_);
v___x_2047_ = l_Subarray_drop___redArg(v_right_2040_, v_i_2044_);
v___x_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2048_, 0, v___x_2046_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
v___x_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2049_, 0, v_pref_2041_);
lean_ctor_set(v___x_2049_, 1, v___x_2048_);
return v___x_2049_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2(lean_object* v_left_2065_, lean_object* v_right_2066_){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2068_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2_spec__4(v_left_2065_, v_right_2066_, v___x_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(lean_object* v_as_x27_2069_, lean_object* v_b_2070_){
_start:
{
if (lean_obj_tag(v_as_x27_2069_) == 0)
{
return v_b_2070_;
}
else
{
lean_object* v_head_2071_; lean_object* v_snd_2072_; lean_object* v_leftIndex_2073_; 
v_head_2071_ = lean_ctor_get(v_as_x27_2069_, 0);
lean_inc(v_head_2071_);
v_snd_2072_ = lean_ctor_get(v_head_2071_, 1);
lean_inc(v_snd_2072_);
v_leftIndex_2073_ = lean_ctor_get(v_snd_2072_, 1);
lean_inc(v_leftIndex_2073_);
if (lean_obj_tag(v_leftIndex_2073_) == 1)
{
lean_object* v_rightIndex_2074_; 
v_rightIndex_2074_ = lean_ctor_get(v_snd_2072_, 3);
lean_inc(v_rightIndex_2074_);
if (lean_obj_tag(v_rightIndex_2074_) == 1)
{
if (lean_obj_tag(v_b_2070_) == 0)
{
lean_object* v_tail_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2105_; 
v_tail_2075_ = lean_ctor_get(v_as_x27_2069_, 1);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_as_x27_2069_);
if (v_isSharedCheck_2105_ == 0)
{
lean_object* v_unused_2106_; 
v_unused_2106_ = lean_ctor_get(v_as_x27_2069_, 0);
lean_dec(v_unused_2106_);
v___x_2077_ = v_as_x27_2069_;
v_isShared_2078_ = v_isSharedCheck_2105_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_tail_2075_);
lean_dec(v_as_x27_2069_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2105_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v_fst_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2103_; 
v_fst_2079_ = lean_ctor_get(v_head_2071_, 0);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_head_2071_);
if (v_isSharedCheck_2103_ == 0)
{
lean_object* v_unused_2104_; 
v_unused_2104_ = lean_ctor_get(v_head_2071_, 1);
lean_dec(v_unused_2104_);
v___x_2081_ = v_head_2071_;
v_isShared_2082_ = v_isSharedCheck_2103_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_fst_2079_);
lean_dec(v_head_2071_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2103_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v_leftCount_2083_; lean_object* v_rightCount_2084_; lean_object* v_val_2085_; lean_object* v_val_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2102_; 
v_leftCount_2083_ = lean_ctor_get(v_snd_2072_, 0);
lean_inc(v_leftCount_2083_);
v_rightCount_2084_ = lean_ctor_get(v_snd_2072_, 2);
lean_inc(v_rightCount_2084_);
lean_dec(v_snd_2072_);
v_val_2085_ = lean_ctor_get(v_leftIndex_2073_, 0);
lean_inc(v_val_2085_);
lean_dec_ref(v_leftIndex_2073_);
v_val_2086_ = lean_ctor_get(v_rightIndex_2074_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v_rightIndex_2074_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2088_ = v_rightIndex_2074_;
v_isShared_2089_ = v_isSharedCheck_2102_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_val_2086_);
lean_dec(v_rightIndex_2074_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2102_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2090_; lean_object* v___x_2092_; 
v___x_2090_ = lean_nat_add(v_leftCount_2083_, v_rightCount_2084_);
lean_dec(v_rightCount_2084_);
lean_dec(v_leftCount_2083_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 1, v_val_2086_);
lean_ctor_set(v___x_2081_, 0, v_val_2085_);
v___x_2092_ = v___x_2081_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_val_2085_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v_val_2086_);
v___x_2092_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v___x_2094_; 
if (v_isShared_2078_ == 0)
{
lean_ctor_set_tag(v___x_2077_, 0);
lean_ctor_set(v___x_2077_, 1, v___x_2092_);
lean_ctor_set(v___x_2077_, 0, v_fst_2079_);
v___x_2094_ = v___x_2077_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_fst_2079_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
lean_object* v___x_2095_; lean_object* v___x_2097_; 
v___x_2095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2090_);
lean_ctor_set(v___x_2095_, 1, v___x_2094_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v___x_2095_);
v___x_2097_ = v___x_2088_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
v_as_x27_2069_ = v_tail_2075_;
v_b_2070_ = v___x_2097_;
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
lean_object* v_val_2107_; lean_object* v_tail_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2149_; 
v_val_2107_ = lean_ctor_get(v_b_2070_, 0);
lean_inc(v_val_2107_);
v_tail_2108_ = lean_ctor_get(v_as_x27_2069_, 1);
v_isSharedCheck_2149_ = !lean_is_exclusive(v_as_x27_2069_);
if (v_isSharedCheck_2149_ == 0)
{
lean_object* v_unused_2150_; 
v_unused_2150_ = lean_ctor_get(v_as_x27_2069_, 0);
lean_dec(v_unused_2150_);
v___x_2110_ = v_as_x27_2069_;
v_isShared_2111_ = v_isSharedCheck_2149_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_tail_2108_);
lean_dec(v_as_x27_2069_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2149_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v_fst_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2147_; 
v_fst_2112_ = lean_ctor_get(v_head_2071_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_head_2071_);
if (v_isSharedCheck_2147_ == 0)
{
lean_object* v_unused_2148_; 
v_unused_2148_ = lean_ctor_get(v_head_2071_, 1);
lean_dec(v_unused_2148_);
v___x_2114_ = v_head_2071_;
v_isShared_2115_ = v_isSharedCheck_2147_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_fst_2112_);
lean_dec(v_head_2071_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2147_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v_leftCount_2116_; lean_object* v_rightCount_2117_; lean_object* v_val_2118_; lean_object* v_val_2119_; lean_object* v_fst_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2145_; 
v_leftCount_2116_ = lean_ctor_get(v_snd_2072_, 0);
lean_inc(v_leftCount_2116_);
v_rightCount_2117_ = lean_ctor_get(v_snd_2072_, 2);
lean_inc(v_rightCount_2117_);
lean_dec(v_snd_2072_);
v_val_2118_ = lean_ctor_get(v_leftIndex_2073_, 0);
lean_inc(v_val_2118_);
lean_dec_ref(v_leftIndex_2073_);
v_val_2119_ = lean_ctor_get(v_rightIndex_2074_, 0);
lean_inc(v_val_2119_);
lean_dec_ref(v_rightIndex_2074_);
v_fst_2120_ = lean_ctor_get(v_val_2107_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v_val_2107_);
if (v_isSharedCheck_2145_ == 0)
{
lean_object* v_unused_2146_; 
v_unused_2146_ = lean_ctor_get(v_val_2107_, 1);
lean_dec(v_unused_2146_);
v___x_2122_ = v_val_2107_;
v_isShared_2123_ = v_isSharedCheck_2145_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_fst_2120_);
lean_dec(v_val_2107_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2145_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2124_; uint8_t v___x_2125_; 
v___x_2124_ = lean_nat_add(v_leftCount_2116_, v_rightCount_2117_);
lean_dec(v_rightCount_2117_);
lean_dec(v_leftCount_2116_);
v___x_2125_ = lean_nat_dec_lt(v___x_2124_, v_fst_2120_);
lean_dec(v_fst_2120_);
if (v___x_2125_ == 0)
{
lean_dec(v___x_2124_);
lean_del_object(v___x_2122_);
lean_dec(v_val_2119_);
lean_dec(v_val_2118_);
lean_del_object(v___x_2114_);
lean_dec(v_fst_2112_);
lean_del_object(v___x_2110_);
v_as_x27_2069_ = v_tail_2108_;
goto _start;
}
else
{
lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2143_; 
v_isSharedCheck_2143_ = !lean_is_exclusive(v_b_2070_);
if (v_isSharedCheck_2143_ == 0)
{
lean_object* v_unused_2144_; 
v_unused_2144_ = lean_ctor_get(v_b_2070_, 0);
lean_dec(v_unused_2144_);
v___x_2128_ = v_b_2070_;
v_isShared_2129_ = v_isSharedCheck_2143_;
goto v_resetjp_2127_;
}
else
{
lean_dec(v_b_2070_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2143_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2123_ == 0)
{
lean_ctor_set(v___x_2122_, 1, v_val_2119_);
lean_ctor_set(v___x_2122_, 0, v_val_2118_);
v___x_2131_ = v___x_2122_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_val_2118_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v_val_2119_);
v___x_2131_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2133_; 
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 1, v___x_2131_);
v___x_2133_ = v___x_2114_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_fst_2112_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
lean_object* v___x_2135_; 
if (v_isShared_2111_ == 0)
{
lean_ctor_set_tag(v___x_2110_, 0);
lean_ctor_set(v___x_2110_, 1, v___x_2133_);
lean_ctor_set(v___x_2110_, 0, v___x_2124_);
v___x_2135_ = v___x_2110_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v___x_2124_);
lean_ctor_set(v_reuseFailAlloc_2140_, 1, v___x_2133_);
v___x_2135_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
lean_object* v___x_2137_; 
if (v_isShared_2129_ == 0)
{
lean_ctor_set(v___x_2128_, 0, v___x_2135_);
v___x_2137_ = v___x_2128_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2135_);
v___x_2137_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
v_as_x27_2069_ = v_tail_2108_;
v_b_2070_ = v___x_2137_;
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
else
{
lean_object* v_tail_2151_; 
lean_dec_ref(v_leftIndex_2073_);
lean_dec(v_rightIndex_2074_);
lean_dec(v_snd_2072_);
lean_dec(v_head_2071_);
v_tail_2151_ = lean_ctor_get(v_as_x27_2069_, 1);
lean_inc(v_tail_2151_);
lean_dec_ref(v_as_x27_2069_);
v_as_x27_2069_ = v_tail_2151_;
goto _start;
}
}
else
{
lean_object* v_tail_2153_; 
lean_dec(v_leftIndex_2073_);
lean_dec(v_snd_2072_);
lean_dec(v_head_2071_);
v_tail_2153_ = lean_ctor_get(v_as_x27_2069_, 1);
lean_inc(v_tail_2153_);
lean_dec_ref(v_as_x27_2069_);
v_as_x27_2069_ = v_tail_2153_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(lean_object* v_a_2155_, lean_object* v_b_2156_, lean_object* v_x_2157_){
_start:
{
if (lean_obj_tag(v_x_2157_) == 0)
{
lean_dec(v_b_2156_);
lean_dec_ref(v_a_2155_);
return v_x_2157_;
}
else
{
lean_object* v_key_2158_; lean_object* v_value_2159_; lean_object* v_tail_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2172_; 
v_key_2158_ = lean_ctor_get(v_x_2157_, 0);
v_value_2159_ = lean_ctor_get(v_x_2157_, 1);
v_tail_2160_ = lean_ctor_get(v_x_2157_, 2);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_x_2157_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2162_ = v_x_2157_;
v_isShared_2163_ = v_isSharedCheck_2172_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_tail_2160_);
lean_inc(v_value_2159_);
lean_inc(v_key_2158_);
lean_dec(v_x_2157_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2172_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
uint8_t v___x_2164_; 
v___x_2164_ = lean_string_dec_eq(v_key_2158_, v_a_2155_);
if (v___x_2164_ == 0)
{
lean_object* v___x_2165_; lean_object* v___x_2167_; 
v___x_2165_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(v_a_2155_, v_b_2156_, v_tail_2160_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 2, v___x_2165_);
v___x_2167_ = v___x_2162_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_key_2158_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v_value_2159_);
lean_ctor_set(v_reuseFailAlloc_2168_, 2, v___x_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
else
{
lean_object* v___x_2170_; 
lean_dec(v_value_2159_);
lean_dec(v_key_2158_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 1, v_b_2156_);
lean_ctor_set(v___x_2162_, 0, v_a_2155_);
v___x_2170_ = v___x_2162_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2155_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_b_2156_);
lean_ctor_set(v_reuseFailAlloc_2171_, 2, v_tail_2160_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(lean_object* v_a_2173_, lean_object* v_x_2174_){
_start:
{
if (lean_obj_tag(v_x_2174_) == 0)
{
uint8_t v___x_2175_; 
v___x_2175_ = 0;
return v___x_2175_;
}
else
{
lean_object* v_key_2176_; lean_object* v_tail_2177_; uint8_t v___x_2178_; 
v_key_2176_ = lean_ctor_get(v_x_2174_, 0);
v_tail_2177_ = lean_ctor_get(v_x_2174_, 2);
v___x_2178_ = lean_string_dec_eq(v_key_2176_, v_a_2173_);
if (v___x_2178_ == 0)
{
v_x_2174_ = v_tail_2177_;
goto _start;
}
else
{
return v___x_2178_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg___boxed(lean_object* v_a_2180_, lean_object* v_x_2181_){
_start:
{
uint8_t v_res_2182_; lean_object* v_r_2183_; 
v_res_2182_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(v_a_2180_, v_x_2181_);
lean_dec(v_x_2181_);
lean_dec_ref(v_a_2180_);
v_r_2183_ = lean_box(v_res_2182_);
return v_r_2183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29___redArg(lean_object* v_x_2184_, lean_object* v_x_2185_){
_start:
{
if (lean_obj_tag(v_x_2185_) == 0)
{
return v_x_2184_;
}
else
{
lean_object* v_key_2186_; lean_object* v_value_2187_; lean_object* v_tail_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2211_; 
v_key_2186_ = lean_ctor_get(v_x_2185_, 0);
v_value_2187_ = lean_ctor_get(v_x_2185_, 1);
v_tail_2188_ = lean_ctor_get(v_x_2185_, 2);
v_isSharedCheck_2211_ = !lean_is_exclusive(v_x_2185_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2190_ = v_x_2185_;
v_isShared_2191_ = v_isSharedCheck_2211_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_tail_2188_);
lean_inc(v_value_2187_);
lean_inc(v_key_2186_);
lean_dec(v_x_2185_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2211_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2192_; uint64_t v___x_2193_; uint64_t v___x_2194_; uint64_t v___x_2195_; uint64_t v_fold_2196_; uint64_t v___x_2197_; uint64_t v___x_2198_; uint64_t v___x_2199_; size_t v___x_2200_; size_t v___x_2201_; size_t v___x_2202_; size_t v___x_2203_; size_t v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2207_; 
v___x_2192_ = lean_array_get_size(v_x_2184_);
v___x_2193_ = lean_string_hash(v_key_2186_);
v___x_2194_ = 32ULL;
v___x_2195_ = lean_uint64_shift_right(v___x_2193_, v___x_2194_);
v_fold_2196_ = lean_uint64_xor(v___x_2193_, v___x_2195_);
v___x_2197_ = 16ULL;
v___x_2198_ = lean_uint64_shift_right(v_fold_2196_, v___x_2197_);
v___x_2199_ = lean_uint64_xor(v_fold_2196_, v___x_2198_);
v___x_2200_ = lean_uint64_to_usize(v___x_2199_);
v___x_2201_ = lean_usize_of_nat(v___x_2192_);
v___x_2202_ = ((size_t)1ULL);
v___x_2203_ = lean_usize_sub(v___x_2201_, v___x_2202_);
v___x_2204_ = lean_usize_land(v___x_2200_, v___x_2203_);
v___x_2205_ = lean_array_uget_borrowed(v_x_2184_, v___x_2204_);
lean_inc(v___x_2205_);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 2, v___x_2205_);
v___x_2207_ = v___x_2190_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v_key_2186_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v_value_2187_);
lean_ctor_set(v_reuseFailAlloc_2210_, 2, v___x_2205_);
v___x_2207_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
lean_object* v___x_2208_; 
v___x_2208_ = lean_array_uset(v_x_2184_, v___x_2204_, v___x_2207_);
v_x_2184_ = v___x_2208_;
v_x_2185_ = v_tail_2188_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28___redArg(lean_object* v_i_2212_, lean_object* v_source_2213_, lean_object* v_target_2214_){
_start:
{
lean_object* v___x_2215_; uint8_t v___x_2216_; 
v___x_2215_ = lean_array_get_size(v_source_2213_);
v___x_2216_ = lean_nat_dec_lt(v_i_2212_, v___x_2215_);
if (v___x_2216_ == 0)
{
lean_dec_ref(v_source_2213_);
lean_dec(v_i_2212_);
return v_target_2214_;
}
else
{
lean_object* v_es_2217_; lean_object* v___x_2218_; lean_object* v_source_2219_; lean_object* v_target_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v_es_2217_ = lean_array_fget(v_source_2213_, v_i_2212_);
v___x_2218_ = lean_box(0);
v_source_2219_ = lean_array_fset(v_source_2213_, v_i_2212_, v___x_2218_);
v_target_2220_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29___redArg(v_target_2214_, v_es_2217_);
v___x_2221_ = lean_unsigned_to_nat(1u);
v___x_2222_ = lean_nat_add(v_i_2212_, v___x_2221_);
lean_dec(v_i_2212_);
v_i_2212_ = v___x_2222_;
v_source_2213_ = v_source_2219_;
v_target_2214_ = v_target_2220_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23___redArg(lean_object* v_data_2224_){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v_nbuckets_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2225_ = lean_array_get_size(v_data_2224_);
v___x_2226_ = lean_unsigned_to_nat(2u);
v_nbuckets_2227_ = lean_nat_mul(v___x_2225_, v___x_2226_);
v___x_2228_ = lean_unsigned_to_nat(0u);
v___x_2229_ = lean_box(0);
v___x_2230_ = lean_mk_array(v_nbuckets_2227_, v___x_2229_);
v___x_2231_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28___redArg(v___x_2228_, v_data_2224_, v___x_2230_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(lean_object* v_m_2232_, lean_object* v_a_2233_, lean_object* v_b_2234_){
_start:
{
lean_object* v_size_2235_; lean_object* v_buckets_2236_; lean_object* v___x_2238_; uint8_t v_isShared_2239_; uint8_t v_isSharedCheck_2279_; 
v_size_2235_ = lean_ctor_get(v_m_2232_, 0);
v_buckets_2236_ = lean_ctor_get(v_m_2232_, 1);
v_isSharedCheck_2279_ = !lean_is_exclusive(v_m_2232_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2238_ = v_m_2232_;
v_isShared_2239_ = v_isSharedCheck_2279_;
goto v_resetjp_2237_;
}
else
{
lean_inc(v_buckets_2236_);
lean_inc(v_size_2235_);
lean_dec(v_m_2232_);
v___x_2238_ = lean_box(0);
v_isShared_2239_ = v_isSharedCheck_2279_;
goto v_resetjp_2237_;
}
v_resetjp_2237_:
{
lean_object* v___x_2240_; uint64_t v___x_2241_; uint64_t v___x_2242_; uint64_t v___x_2243_; uint64_t v_fold_2244_; uint64_t v___x_2245_; uint64_t v___x_2246_; uint64_t v___x_2247_; size_t v___x_2248_; size_t v___x_2249_; size_t v___x_2250_; size_t v___x_2251_; size_t v___x_2252_; lean_object* v_bkt_2253_; uint8_t v___x_2254_; 
v___x_2240_ = lean_array_get_size(v_buckets_2236_);
v___x_2241_ = lean_string_hash(v_a_2233_);
v___x_2242_ = 32ULL;
v___x_2243_ = lean_uint64_shift_right(v___x_2241_, v___x_2242_);
v_fold_2244_ = lean_uint64_xor(v___x_2241_, v___x_2243_);
v___x_2245_ = 16ULL;
v___x_2246_ = lean_uint64_shift_right(v_fold_2244_, v___x_2245_);
v___x_2247_ = lean_uint64_xor(v_fold_2244_, v___x_2246_);
v___x_2248_ = lean_uint64_to_usize(v___x_2247_);
v___x_2249_ = lean_usize_of_nat(v___x_2240_);
v___x_2250_ = ((size_t)1ULL);
v___x_2251_ = lean_usize_sub(v___x_2249_, v___x_2250_);
v___x_2252_ = lean_usize_land(v___x_2248_, v___x_2251_);
v_bkt_2253_ = lean_array_uget_borrowed(v_buckets_2236_, v___x_2252_);
v___x_2254_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(v_a_2233_, v_bkt_2253_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; lean_object* v_size_x27_2256_; lean_object* v___x_2257_; lean_object* v_buckets_x27_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; uint8_t v___x_2264_; 
v___x_2255_ = lean_unsigned_to_nat(1u);
v_size_x27_2256_ = lean_nat_add(v_size_2235_, v___x_2255_);
lean_dec(v_size_2235_);
lean_inc(v_bkt_2253_);
v___x_2257_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2257_, 0, v_a_2233_);
lean_ctor_set(v___x_2257_, 1, v_b_2234_);
lean_ctor_set(v___x_2257_, 2, v_bkt_2253_);
v_buckets_x27_2258_ = lean_array_uset(v_buckets_2236_, v___x_2252_, v___x_2257_);
v___x_2259_ = lean_unsigned_to_nat(4u);
v___x_2260_ = lean_nat_mul(v_size_x27_2256_, v___x_2259_);
v___x_2261_ = lean_unsigned_to_nat(3u);
v___x_2262_ = lean_nat_div(v___x_2260_, v___x_2261_);
lean_dec(v___x_2260_);
v___x_2263_ = lean_array_get_size(v_buckets_x27_2258_);
v___x_2264_ = lean_nat_dec_le(v___x_2262_, v___x_2263_);
lean_dec(v___x_2262_);
if (v___x_2264_ == 0)
{
lean_object* v_val_2265_; lean_object* v___x_2267_; 
v_val_2265_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23___redArg(v_buckets_x27_2258_);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 1, v_val_2265_);
lean_ctor_set(v___x_2238_, 0, v_size_x27_2256_);
v___x_2267_ = v___x_2238_;
goto v_reusejp_2266_;
}
else
{
lean_object* v_reuseFailAlloc_2268_; 
v_reuseFailAlloc_2268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2268_, 0, v_size_x27_2256_);
lean_ctor_set(v_reuseFailAlloc_2268_, 1, v_val_2265_);
v___x_2267_ = v_reuseFailAlloc_2268_;
goto v_reusejp_2266_;
}
v_reusejp_2266_:
{
return v___x_2267_;
}
}
else
{
lean_object* v___x_2270_; 
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 1, v_buckets_x27_2258_);
lean_ctor_set(v___x_2238_, 0, v_size_x27_2256_);
v___x_2270_ = v___x_2238_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_size_x27_2256_);
lean_ctor_set(v_reuseFailAlloc_2271_, 1, v_buckets_x27_2258_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
else
{
lean_object* v___x_2272_; lean_object* v_buckets_x27_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2277_; 
lean_inc(v_bkt_2253_);
v___x_2272_ = lean_box(0);
v_buckets_x27_2273_ = lean_array_uset(v_buckets_2236_, v___x_2252_, v___x_2272_);
v___x_2274_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(v_a_2233_, v_b_2234_, v_bkt_2253_);
v___x_2275_ = lean_array_uset(v_buckets_x27_2273_, v___x_2252_, v___x_2274_);
if (v_isShared_2239_ == 0)
{
lean_ctor_set(v___x_2238_, 1, v___x_2275_);
v___x_2277_ = v___x_2238_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_size_2235_);
lean_ctor_set(v_reuseFailAlloc_2278_, 1, v___x_2275_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(lean_object* v_a_2280_, lean_object* v_x_2281_){
_start:
{
if (lean_obj_tag(v_x_2281_) == 0)
{
lean_object* v___x_2282_; 
v___x_2282_ = lean_box(0);
return v___x_2282_;
}
else
{
lean_object* v_key_2283_; lean_object* v_value_2284_; lean_object* v_tail_2285_; uint8_t v___x_2286_; 
v_key_2283_ = lean_ctor_get(v_x_2281_, 0);
v_value_2284_ = lean_ctor_get(v_x_2281_, 1);
v_tail_2285_ = lean_ctor_get(v_x_2281_, 2);
v___x_2286_ = lean_string_dec_eq(v_key_2283_, v_a_2280_);
if (v___x_2286_ == 0)
{
v_x_2281_ = v_tail_2285_;
goto _start;
}
else
{
lean_object* v___x_2288_; 
lean_inc(v_value_2284_);
v___x_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2288_, 0, v_value_2284_);
return v___x_2288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg___boxed(lean_object* v_a_2289_, lean_object* v_x_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(v_a_2289_, v_x_2290_);
lean_dec(v_x_2290_);
lean_dec_ref(v_a_2289_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(lean_object* v_m_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v_buckets_2294_; lean_object* v___x_2295_; uint64_t v___x_2296_; uint64_t v___x_2297_; uint64_t v___x_2298_; uint64_t v_fold_2299_; uint64_t v___x_2300_; uint64_t v___x_2301_; uint64_t v___x_2302_; size_t v___x_2303_; size_t v___x_2304_; size_t v___x_2305_; size_t v___x_2306_; size_t v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v_buckets_2294_ = lean_ctor_get(v_m_2292_, 1);
v___x_2295_ = lean_array_get_size(v_buckets_2294_);
v___x_2296_ = lean_string_hash(v_a_2293_);
v___x_2297_ = 32ULL;
v___x_2298_ = lean_uint64_shift_right(v___x_2296_, v___x_2297_);
v_fold_2299_ = lean_uint64_xor(v___x_2296_, v___x_2298_);
v___x_2300_ = 16ULL;
v___x_2301_ = lean_uint64_shift_right(v_fold_2299_, v___x_2300_);
v___x_2302_ = lean_uint64_xor(v_fold_2299_, v___x_2301_);
v___x_2303_ = lean_uint64_to_usize(v___x_2302_);
v___x_2304_ = lean_usize_of_nat(v___x_2295_);
v___x_2305_ = ((size_t)1ULL);
v___x_2306_ = lean_usize_sub(v___x_2304_, v___x_2305_);
v___x_2307_ = lean_usize_land(v___x_2303_, v___x_2306_);
v___x_2308_ = lean_array_uget_borrowed(v_buckets_2294_, v___x_2307_);
v___x_2309_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(v_a_2293_, v___x_2308_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg___boxed(lean_object* v_m_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_m_2310_, v_a_2311_);
lean_dec_ref(v_a_2311_);
lean_dec_ref(v_m_2310_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(lean_object* v_histogram_2313_, lean_object* v_index_2314_, lean_object* v_val_2315_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_histogram_2313_, v_val_2315_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2317_ = lean_unsigned_to_nat(1u);
v___x_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2318_, 0, v_index_2314_);
v___x_2319_ = lean_unsigned_to_nat(0u);
v___x_2320_ = lean_box(0);
v___x_2321_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2317_);
lean_ctor_set(v___x_2321_, 1, v___x_2318_);
lean_ctor_set(v___x_2321_, 2, v___x_2319_);
lean_ctor_set(v___x_2321_, 3, v___x_2320_);
v___x_2322_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2313_, v_val_2315_, v___x_2321_);
return v___x_2322_;
}
else
{
lean_object* v_val_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2344_; 
v_val_2323_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2325_ = v___x_2316_;
v_isShared_2326_ = v_isSharedCheck_2344_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_val_2323_);
lean_dec(v___x_2316_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2344_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v_leftCount_2327_; lean_object* v_rightCount_2328_; lean_object* v_rightIndex_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2342_; 
v_leftCount_2327_ = lean_ctor_get(v_val_2323_, 0);
v_rightCount_2328_ = lean_ctor_get(v_val_2323_, 2);
v_rightIndex_2329_ = lean_ctor_get(v_val_2323_, 3);
v_isSharedCheck_2342_ = !lean_is_exclusive(v_val_2323_);
if (v_isSharedCheck_2342_ == 0)
{
lean_object* v_unused_2343_; 
v_unused_2343_ = lean_ctor_get(v_val_2323_, 1);
lean_dec(v_unused_2343_);
v___x_2331_ = v_val_2323_;
v_isShared_2332_ = v_isSharedCheck_2342_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_rightIndex_2329_);
lean_inc(v_rightCount_2328_);
lean_inc(v_leftCount_2327_);
lean_dec(v_val_2323_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2342_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2336_; 
v___x_2333_ = lean_unsigned_to_nat(1u);
v___x_2334_ = lean_nat_add(v_leftCount_2327_, v___x_2333_);
lean_dec(v_leftCount_2327_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v_index_2314_);
v___x_2336_ = v___x_2325_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_index_2314_);
v___x_2336_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2338_; 
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 1, v___x_2336_);
lean_ctor_set(v___x_2331_, 0, v___x_2334_);
v___x_2338_ = v___x_2331_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2334_);
lean_ctor_set(v_reuseFailAlloc_2340_, 1, v___x_2336_);
lean_ctor_set(v_reuseFailAlloc_2340_, 2, v_rightCount_2328_);
lean_ctor_set(v_reuseFailAlloc_2340_, 3, v_rightIndex_2329_);
v___x_2338_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2313_, v_val_2315_, v___x_2338_);
return v___x_2339_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(lean_object* v_upperBound_2345_, lean_object* v_fst_2346_, lean_object* v___x_2347_, lean_object* v_fst_2348_, lean_object* v_a_2349_, lean_object* v_b_2350_){
_start:
{
uint8_t v___x_2351_; 
v___x_2351_ = lean_nat_dec_lt(v_a_2349_, v_upperBound_2345_);
if (v___x_2351_ == 0)
{
lean_dec(v_a_2349_);
return v_b_2350_;
}
else
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2352_ = l_Subarray_get___redArg(v_fst_2348_, v_a_2349_);
lean_inc(v_a_2349_);
v___x_2353_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(v_b_2350_, v_a_2349_, v___x_2352_);
v___x_2354_ = lean_unsigned_to_nat(1u);
v___x_2355_ = lean_nat_add(v_a_2349_, v___x_2354_);
lean_dec(v_a_2349_);
v_a_2349_ = v___x_2355_;
v_b_2350_ = v___x_2353_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_upperBound_2357_, lean_object* v_fst_2358_, lean_object* v___x_2359_, lean_object* v_fst_2360_, lean_object* v_a_2361_, lean_object* v_b_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(v_upperBound_2357_, v_fst_2358_, v___x_2359_, v_fst_2360_, v_a_2361_, v_b_2362_);
lean_dec_ref(v_fst_2360_);
lean_dec(v___x_2359_);
lean_dec_ref(v_fst_2358_);
lean_dec(v_upperBound_2357_);
return v_res_2363_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(lean_object* v_x_2364_, lean_object* v_x_2365_){
_start:
{
if (lean_obj_tag(v_x_2365_) == 0)
{
lean_inc(v_x_2364_);
return v_x_2364_;
}
else
{
lean_object* v_key_2366_; lean_object* v_value_2367_; lean_object* v_tail_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v_key_2366_ = lean_ctor_get(v_x_2365_, 0);
v_value_2367_ = lean_ctor_get(v_x_2365_, 1);
v_tail_2368_ = lean_ctor_get(v_x_2365_, 2);
v___x_2369_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(v_x_2364_, v_tail_2368_);
lean_inc(v_value_2367_);
lean_inc(v_key_2366_);
v___x_2370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2370_, 0, v_key_2366_);
lean_ctor_set(v___x_2370_, 1, v_value_2367_);
v___x_2371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2370_);
lean_ctor_set(v___x_2371_, 1, v___x_2369_);
return v___x_2371_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5___boxed(lean_object* v_x_2372_, lean_object* v_x_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(v_x_2372_, v_x_2373_);
lean_dec(v_x_2373_);
lean_dec(v_x_2372_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(lean_object* v_as_2375_, size_t v_i_2376_, size_t v_stop_2377_, lean_object* v_b_2378_){
_start:
{
uint8_t v___x_2379_; 
v___x_2379_ = lean_usize_dec_eq(v_i_2376_, v_stop_2377_);
if (v___x_2379_ == 0)
{
size_t v___x_2380_; size_t v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2380_ = ((size_t)1ULL);
v___x_2381_ = lean_usize_sub(v_i_2376_, v___x_2380_);
v___x_2382_ = lean_array_uget_borrowed(v_as_2375_, v___x_2381_);
v___x_2383_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(v_b_2378_, v___x_2382_);
lean_dec(v_b_2378_);
v_i_2376_ = v___x_2381_;
v_b_2378_ = v___x_2383_;
goto _start;
}
else
{
return v_b_2378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6___boxed(lean_object* v_as_2385_, lean_object* v_i_2386_, lean_object* v_stop_2387_, lean_object* v_b_2388_){
_start:
{
size_t v_i_boxed_2389_; size_t v_stop_boxed_2390_; lean_object* v_res_2391_; 
v_i_boxed_2389_ = lean_unbox_usize(v_i_2386_);
lean_dec(v_i_2386_);
v_stop_boxed_2390_ = lean_unbox_usize(v_stop_2387_);
lean_dec(v_stop_2387_);
v_res_2391_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(v_as_2385_, v_i_boxed_2389_, v_stop_boxed_2390_, v_b_2388_);
lean_dec_ref(v_as_2385_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(lean_object* v_histogram_2392_, lean_object* v_index_2393_, lean_object* v_val_2394_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_histogram_2392_, v_val_2394_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2396_ = lean_unsigned_to_nat(0u);
v___x_2397_ = lean_box(0);
v___x_2398_ = lean_unsigned_to_nat(1u);
v___x_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2399_, 0, v_index_2393_);
v___x_2400_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2396_);
lean_ctor_set(v___x_2400_, 1, v___x_2397_);
lean_ctor_set(v___x_2400_, 2, v___x_2398_);
lean_ctor_set(v___x_2400_, 3, v___x_2399_);
v___x_2401_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2392_, v_val_2394_, v___x_2400_);
return v___x_2401_;
}
else
{
lean_object* v_val_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2423_; 
v_val_2402_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2404_ = v___x_2395_;
v_isShared_2405_ = v_isSharedCheck_2423_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_val_2402_);
lean_dec(v___x_2395_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2423_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v_leftCount_2406_; lean_object* v_leftIndex_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2420_; 
v_leftCount_2406_ = lean_ctor_get(v_val_2402_, 0);
v_leftIndex_2407_ = lean_ctor_get(v_val_2402_, 1);
v_isSharedCheck_2420_ = !lean_is_exclusive(v_val_2402_);
if (v_isSharedCheck_2420_ == 0)
{
lean_object* v_unused_2421_; lean_object* v_unused_2422_; 
v_unused_2421_ = lean_ctor_get(v_val_2402_, 3);
lean_dec(v_unused_2421_);
v_unused_2422_ = lean_ctor_get(v_val_2402_, 2);
lean_dec(v_unused_2422_);
v___x_2409_ = v_val_2402_;
v_isShared_2410_ = v_isSharedCheck_2420_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_leftIndex_2407_);
lean_inc(v_leftCount_2406_);
lean_dec(v_val_2402_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2420_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2414_; 
v___x_2411_ = lean_unsigned_to_nat(1u);
v___x_2412_ = lean_nat_add(v_leftCount_2406_, v___x_2411_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 0, v_index_2393_);
v___x_2414_ = v___x_2404_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_index_2393_);
v___x_2414_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
lean_object* v___x_2416_; 
if (v_isShared_2410_ == 0)
{
lean_ctor_set(v___x_2409_, 3, v___x_2414_);
lean_ctor_set(v___x_2409_, 2, v___x_2412_);
v___x_2416_ = v___x_2409_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_leftCount_2406_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_leftIndex_2407_);
lean_ctor_set(v_reuseFailAlloc_2418_, 2, v___x_2412_);
lean_ctor_set(v_reuseFailAlloc_2418_, 3, v___x_2414_);
v___x_2416_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
lean_object* v___x_2417_; 
v___x_2417_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2392_, v_val_2394_, v___x_2416_);
return v___x_2417_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(lean_object* v_upperBound_2424_, lean_object* v___x_2425_, lean_object* v_fst_2426_, lean_object* v___x_2427_, lean_object* v_a_2428_, lean_object* v_b_2429_){
_start:
{
uint8_t v___x_2430_; 
v___x_2430_ = lean_nat_dec_lt(v_a_2428_, v_upperBound_2424_);
if (v___x_2430_ == 0)
{
lean_dec(v_a_2428_);
return v_b_2429_;
}
else
{
lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2431_ = l_Subarray_get___redArg(v_fst_2426_, v_a_2428_);
lean_inc(v_a_2428_);
v___x_2432_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(v_b_2429_, v_a_2428_, v___x_2431_);
v___x_2433_ = lean_unsigned_to_nat(1u);
v___x_2434_ = lean_nat_add(v_a_2428_, v___x_2433_);
lean_dec(v_a_2428_);
v_a_2428_ = v___x_2434_;
v_b_2429_ = v___x_2432_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg___boxed(lean_object* v_upperBound_2436_, lean_object* v___x_2437_, lean_object* v_fst_2438_, lean_object* v___x_2439_, lean_object* v_a_2440_, lean_object* v_b_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(v_upperBound_2436_, v___x_2437_, v_fst_2438_, v___x_2439_, v_a_2440_, v_b_2441_);
lean_dec(v___x_2439_);
lean_dec_ref(v_fst_2438_);
lean_dec(v___x_2437_);
lean_dec(v_upperBound_2436_);
return v_res_2442_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2443_ = lean_box(0);
v___x_2444_ = lean_unsigned_to_nat(16u);
v___x_2445_ = lean_mk_array(v___x_2444_, v___x_2443_);
return v___x_2445_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v_hist_2448_; 
v___x_2446_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0);
v___x_2447_ = lean_unsigned_to_nat(0u);
v_hist_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_2448_, 0, v___x_2447_);
lean_ctor_set(v_hist_2448_, 1, v___x_2446_);
return v_hist_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(lean_object* v_left_2449_, lean_object* v_right_2450_){
_start:
{
lean_object* v___x_2451_; lean_object* v_snd_2452_; lean_object* v_fst_2453_; lean_object* v_fst_2454_; lean_object* v_snd_2455_; lean_object* v___x_2456_; lean_object* v_snd_2457_; lean_object* v_fst_2458_; lean_object* v_fst_2459_; lean_object* v_snd_2460_; lean_object* v_start_2461_; lean_object* v_stop_2462_; lean_object* v___x_2463_; lean_object* v_hist_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v_start_2467_; lean_object* v_stop_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v_buckets_2471_; lean_object* v___x_2472_; lean_object* v___y_2474_; lean_object* v___x_2500_; lean_object* v___x_2501_; uint8_t v___x_2502_; 
v___x_2451_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2(v_left_2449_, v_right_2450_);
v_snd_2452_ = lean_ctor_get(v___x_2451_, 1);
lean_inc(v_snd_2452_);
v_fst_2453_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_fst_2453_);
lean_dec_ref(v___x_2451_);
v_fst_2454_ = lean_ctor_get(v_snd_2452_, 0);
lean_inc(v_fst_2454_);
v_snd_2455_ = lean_ctor_get(v_snd_2452_, 1);
lean_inc(v_snd_2455_);
lean_dec(v_snd_2452_);
v___x_2456_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3(v_fst_2454_, v_snd_2455_);
v_snd_2457_ = lean_ctor_get(v___x_2456_, 1);
lean_inc(v_snd_2457_);
v_fst_2458_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_fst_2458_);
lean_dec_ref(v___x_2456_);
v_fst_2459_ = lean_ctor_get(v_snd_2457_, 0);
lean_inc(v_fst_2459_);
v_snd_2460_ = lean_ctor_get(v_snd_2457_, 1);
lean_inc(v_snd_2460_);
lean_dec(v_snd_2457_);
v_start_2461_ = lean_ctor_get(v_fst_2458_, 1);
v_stop_2462_ = lean_ctor_get(v_fst_2458_, 2);
v___x_2463_ = lean_unsigned_to_nat(0u);
v_hist_2464_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1);
v___x_2465_ = lean_nat_sub(v_stop_2462_, v_start_2461_);
v___x_2466_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(v___x_2465_, v_fst_2459_, v___x_2465_, v_fst_2458_, v___x_2463_, v_hist_2464_);
v_start_2467_ = lean_ctor_get(v_fst_2459_, 1);
v_stop_2468_ = lean_ctor_get(v_fst_2459_, 2);
v___x_2469_ = lean_nat_sub(v_stop_2468_, v_start_2467_);
v___x_2470_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(v___x_2469_, v___x_2469_, v_fst_2459_, v___x_2465_, v___x_2463_, v___x_2466_);
lean_dec(v___x_2465_);
lean_dec(v___x_2469_);
v_buckets_2471_ = lean_ctor_get(v___x_2470_, 1);
lean_inc_ref(v_buckets_2471_);
lean_dec_ref(v___x_2470_);
v___x_2472_ = lean_box(0);
v___x_2500_ = lean_box(0);
v___x_2501_ = lean_array_get_size(v_buckets_2471_);
v___x_2502_ = lean_nat_dec_lt(v___x_2463_, v___x_2501_);
if (v___x_2502_ == 0)
{
lean_dec_ref(v_buckets_2471_);
v___y_2474_ = v___x_2500_;
goto v___jp_2473_;
}
else
{
size_t v___x_2503_; size_t v___x_2504_; lean_object* v___x_2505_; 
v___x_2503_ = lean_usize_of_nat(v___x_2501_);
v___x_2504_ = ((size_t)0ULL);
v___x_2505_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(v_buckets_2471_, v___x_2503_, v___x_2504_, v___x_2500_);
lean_dec_ref(v_buckets_2471_);
v___y_2474_ = v___x_2505_;
goto v___jp_2473_;
}
v___jp_2473_:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(v___y_2474_, v___x_2472_);
if (lean_obj_tag(v___x_2475_) == 1)
{
lean_object* v_val_2476_; lean_object* v_snd_2477_; lean_object* v_snd_2478_; lean_object* v_fst_2479_; lean_object* v_fst_2480_; lean_object* v_snd_2481_; lean_object* v___x_2482_; lean_object* v_fst_2483_; lean_object* v_snd_2484_; lean_object* v___x_2485_; lean_object* v_fst_2486_; lean_object* v_snd_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v_val_2476_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_val_2476_);
lean_dec_ref(v___x_2475_);
v_snd_2477_ = lean_ctor_get(v_val_2476_, 1);
lean_inc(v_snd_2477_);
lean_dec(v_val_2476_);
v_snd_2478_ = lean_ctor_get(v_snd_2477_, 1);
lean_inc(v_snd_2478_);
v_fst_2479_ = lean_ctor_get(v_snd_2477_, 0);
lean_inc(v_fst_2479_);
lean_dec(v_snd_2477_);
v_fst_2480_ = lean_ctor_get(v_snd_2478_, 0);
lean_inc(v_fst_2480_);
v_snd_2481_ = lean_ctor_get(v_snd_2478_, 1);
lean_inc(v_snd_2481_);
lean_dec(v_snd_2478_);
v___x_2482_ = l_Subarray_split___redArg(v_fst_2458_, v_fst_2480_);
lean_dec(v_fst_2480_);
v_fst_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_fst_2483_);
v_snd_2484_ = lean_ctor_get(v___x_2482_, 1);
lean_inc(v_snd_2484_);
lean_dec_ref(v___x_2482_);
v___x_2485_ = l_Subarray_split___redArg(v_fst_2459_, v_snd_2481_);
lean_dec(v_snd_2481_);
v_fst_2486_ = lean_ctor_get(v___x_2485_, 0);
lean_inc(v_fst_2486_);
v_snd_2487_ = lean_ctor_get(v___x_2485_, 1);
lean_inc(v_snd_2487_);
lean_dec_ref(v___x_2485_);
v___x_2488_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v_fst_2483_, v_fst_2486_);
v___x_2489_ = l_Array_append___redArg(v_fst_2453_, v___x_2488_);
lean_dec_ref(v___x_2488_);
v___x_2490_ = lean_unsigned_to_nat(1u);
v___x_2491_ = lean_mk_empty_array_with_capacity(v___x_2490_);
v___x_2492_ = lean_array_push(v___x_2491_, v_fst_2479_);
v___x_2493_ = l_Array_append___redArg(v___x_2489_, v___x_2492_);
lean_dec_ref(v___x_2492_);
v___x_2494_ = l_Subarray_drop___redArg(v_snd_2484_, v___x_2490_);
v___x_2495_ = l_Subarray_drop___redArg(v_snd_2487_, v___x_2490_);
v___x_2496_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v___x_2494_, v___x_2495_);
v___x_2497_ = l_Array_append___redArg(v___x_2493_, v___x_2496_);
lean_dec_ref(v___x_2496_);
v___x_2498_ = l_Array_append___redArg(v___x_2497_, v_snd_2460_);
lean_dec(v_snd_2460_);
return v___x_2498_;
}
else
{
lean_object* v___x_2499_; 
lean_dec(v___x_2475_);
lean_dec(v_fst_2459_);
lean_dec(v_fst_2458_);
v___x_2499_ = l_Array_append___redArg(v_fst_2453_, v_snd_2460_);
lean_dec(v_snd_2460_);
return v___x_2499_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(lean_object* v___x_2506_, lean_object* v_edited_2507_, lean_object* v_b_2508_){
_start:
{
lean_object* v_fst_2509_; lean_object* v_snd_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2529_; 
v_fst_2509_ = lean_ctor_get(v_b_2508_, 0);
v_snd_2510_ = lean_ctor_get(v_b_2508_, 1);
v_isSharedCheck_2529_ = !lean_is_exclusive(v_b_2508_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2512_ = v_b_2508_;
v_isShared_2513_ = v_isSharedCheck_2529_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_snd_2510_);
lean_inc(v_fst_2509_);
lean_dec(v_b_2508_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2529_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
uint8_t v___x_2514_; 
v___x_2514_ = lean_nat_dec_lt(v_snd_2510_, v___x_2506_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2516_; 
if (v_isShared_2513_ == 0)
{
v___x_2516_ = v___x_2512_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_fst_2509_);
lean_ctor_set(v_reuseFailAlloc_2517_, 1, v_snd_2510_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
else
{
uint8_t v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2522_; 
v___x_2518_ = 0;
v___x_2519_ = lean_array_fget_borrowed(v_edited_2507_, v_snd_2510_);
v___x_2520_ = lean_box(v___x_2518_);
lean_inc(v___x_2519_);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 1, v___x_2519_);
lean_ctor_set(v___x_2512_, 0, v___x_2520_);
v___x_2522_ = v___x_2512_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2520_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v___x_2519_);
v___x_2522_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2523_ = lean_array_push(v_fst_2509_, v___x_2522_);
v___x_2524_ = lean_unsigned_to_nat(1u);
v___x_2525_ = lean_nat_add(v_snd_2510_, v___x_2524_);
lean_dec(v_snd_2510_);
v___x_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2523_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
v_b_2508_ = v___x_2526_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___boxed(lean_object* v___x_2530_, lean_object* v_edited_2531_, lean_object* v_b_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(v___x_2530_, v_edited_2531_, v_b_2532_);
lean_dec_ref(v_edited_2531_);
lean_dec(v___x_2530_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(size_t v_sz_2534_, size_t v_i_2535_, lean_object* v_bs_2536_){
_start:
{
uint8_t v___x_2537_; 
v___x_2537_ = lean_usize_dec_lt(v_i_2535_, v_sz_2534_);
if (v___x_2537_ == 0)
{
return v_bs_2536_;
}
else
{
lean_object* v_v_2538_; lean_object* v___x_2539_; lean_object* v_bs_x27_2540_; uint8_t v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; size_t v___x_2544_; size_t v___x_2545_; lean_object* v___x_2546_; 
v_v_2538_ = lean_array_uget(v_bs_2536_, v_i_2535_);
v___x_2539_ = lean_unsigned_to_nat(0u);
v_bs_x27_2540_ = lean_array_uset(v_bs_2536_, v_i_2535_, v___x_2539_);
v___x_2541_ = 1;
v___x_2542_ = lean_box(v___x_2541_);
v___x_2543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
lean_ctor_set(v___x_2543_, 1, v_v_2538_);
v___x_2544_ = ((size_t)1ULL);
v___x_2545_ = lean_usize_add(v_i_2535_, v___x_2544_);
v___x_2546_ = lean_array_uset(v_bs_x27_2540_, v_i_2535_, v___x_2543_);
v_i_2535_ = v___x_2545_;
v_bs_2536_ = v___x_2546_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7___boxed(lean_object* v_sz_2548_, lean_object* v_i_2549_, lean_object* v_bs_2550_){
_start:
{
size_t v_sz_boxed_2551_; size_t v_i_boxed_2552_; lean_object* v_res_2553_; 
v_sz_boxed_2551_ = lean_unbox_usize(v_sz_2548_);
lean_dec(v_sz_2548_);
v_i_boxed_2552_ = lean_unbox_usize(v_i_2549_);
lean_dec(v_i_2549_);
v_res_2553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_boxed_2551_, v_i_boxed_2552_, v_bs_2550_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(lean_object* v___x_2554_, lean_object* v_original_2555_, lean_object* v_b_2556_){
_start:
{
lean_object* v_fst_2557_; lean_object* v_snd_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2577_; 
v_fst_2557_ = lean_ctor_get(v_b_2556_, 0);
v_snd_2558_ = lean_ctor_get(v_b_2556_, 1);
v_isSharedCheck_2577_ = !lean_is_exclusive(v_b_2556_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2560_ = v_b_2556_;
v_isShared_2561_ = v_isSharedCheck_2577_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_snd_2558_);
lean_inc(v_fst_2557_);
lean_dec(v_b_2556_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2577_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
uint8_t v___x_2562_; 
v___x_2562_ = lean_nat_dec_lt(v_snd_2558_, v___x_2554_);
if (v___x_2562_ == 0)
{
lean_object* v___x_2564_; 
if (v_isShared_2561_ == 0)
{
v___x_2564_ = v___x_2560_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_fst_2557_);
lean_ctor_set(v_reuseFailAlloc_2565_, 1, v_snd_2558_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
else
{
uint8_t v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2570_; 
v___x_2566_ = 1;
v___x_2567_ = lean_array_fget_borrowed(v_original_2555_, v_snd_2558_);
v___x_2568_ = lean_box(v___x_2566_);
lean_inc(v___x_2567_);
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 1, v___x_2567_);
lean_ctor_set(v___x_2560_, 0, v___x_2568_);
v___x_2570_ = v___x_2560_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v___x_2568_);
lean_ctor_set(v_reuseFailAlloc_2576_, 1, v___x_2567_);
v___x_2570_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2571_ = lean_array_push(v_fst_2557_, v___x_2570_);
v___x_2572_ = lean_unsigned_to_nat(1u);
v___x_2573_ = lean_nat_add(v_snd_2558_, v___x_2572_);
lean_dec(v_snd_2558_);
v___x_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2571_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v_b_2556_ = v___x_2574_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___boxed(lean_object* v___x_2578_, lean_object* v_original_2579_, lean_object* v_b_2580_){
_start:
{
lean_object* v_res_2581_; 
v_res_2581_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(v___x_2578_, v_original_2579_, v_b_2580_);
lean_dec_ref(v_original_2579_);
lean_dec(v___x_2578_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(lean_object* v_inst_2587_, lean_object* v_original_2588_, lean_object* v_edited_2589_){
_start:
{
lean_object* v_i_2590_; lean_object* v___x_2591_; uint8_t v___x_2592_; 
v_i_2590_ = lean_unsigned_to_nat(0u);
v___x_2591_ = lean_array_get_size(v_original_2588_);
v___x_2592_ = lean_nat_dec_lt(v_i_2590_, v___x_2591_);
if (v___x_2592_ == 0)
{
size_t v_sz_2593_; size_t v___x_2594_; lean_object* v___x_2595_; 
lean_dec_ref(v_original_2588_);
lean_dec_ref(v_inst_2587_);
v_sz_2593_ = lean_array_size(v_edited_2589_);
v___x_2594_ = ((size_t)0ULL);
v___x_2595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_2593_, v___x_2594_, v_edited_2589_);
return v___x_2595_;
}
else
{
lean_object* v___x_2596_; uint8_t v___x_2597_; 
v___x_2596_ = lean_array_get_size(v_edited_2589_);
v___x_2597_ = lean_nat_dec_lt(v_i_2590_, v___x_2596_);
if (v___x_2597_ == 0)
{
size_t v_sz_2598_; size_t v___x_2599_; lean_object* v___x_2600_; 
lean_dec_ref(v_edited_2589_);
lean_dec_ref(v_inst_2587_);
v_sz_2598_ = lean_array_size(v_original_2588_);
v___x_2599_ = ((size_t)0ULL);
v___x_2600_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_2598_, v___x_2599_, v_original_2588_);
return v___x_2600_;
}
else
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v_ds_2603_; lean_object* v___x_2604_; size_t v_sz_2605_; size_t v___x_2606_; lean_object* v___x_2607_; lean_object* v_snd_2608_; lean_object* v_fst_2609_; lean_object* v_fst_2610_; lean_object* v_snd_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2630_; 
lean_inc_ref(v_original_2588_);
v___x_2601_ = l_Array_toSubarray___redArg(v_original_2588_, v_i_2590_, v___x_2591_);
lean_inc_ref(v_edited_2589_);
v___x_2602_ = l_Array_toSubarray___redArg(v_edited_2589_, v_i_2590_, v___x_2596_);
v_ds_2603_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v___x_2601_, v___x_2602_);
v___x_2604_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__1));
v_sz_2605_ = lean_array_size(v_ds_2603_);
v___x_2606_ = ((size_t)0ULL);
v___x_2607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v_inst_2587_, v_edited_2589_, v___x_2596_, v_original_2588_, v___x_2591_, v_ds_2603_, v_sz_2605_, v___x_2606_, v___x_2604_);
lean_dec_ref(v_ds_2603_);
v_snd_2608_ = lean_ctor_get(v___x_2607_, 1);
lean_inc(v_snd_2608_);
v_fst_2609_ = lean_ctor_get(v___x_2607_, 0);
lean_inc(v_fst_2609_);
lean_dec_ref(v___x_2607_);
v_fst_2610_ = lean_ctor_get(v_snd_2608_, 0);
v_snd_2611_ = lean_ctor_get(v_snd_2608_, 1);
v_isSharedCheck_2630_ = !lean_is_exclusive(v_snd_2608_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2613_ = v_snd_2608_;
v_isShared_2614_ = v_isSharedCheck_2630_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_snd_2611_);
lean_inc(v_fst_2610_);
lean_dec(v_snd_2608_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2630_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 1, v_fst_2610_);
lean_ctor_set(v___x_2613_, 0, v_fst_2609_);
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_fst_2609_);
lean_ctor_set(v_reuseFailAlloc_2629_, 1, v_fst_2610_);
v___x_2616_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
lean_object* v___x_2617_; lean_object* v_fst_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2627_; 
v___x_2617_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(v___x_2591_, v_original_2588_, v___x_2616_);
lean_dec_ref(v_original_2588_);
v_fst_2618_ = lean_ctor_get(v___x_2617_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2627_ == 0)
{
lean_object* v_unused_2628_; 
v_unused_2628_ = lean_ctor_get(v___x_2617_, 1);
lean_dec(v_unused_2628_);
v___x_2620_ = v___x_2617_;
v_isShared_2621_ = v_isSharedCheck_2627_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_fst_2618_);
lean_dec(v___x_2617_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2627_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2623_; 
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 1, v_snd_2611_);
v___x_2623_ = v___x_2620_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_fst_2618_);
lean_ctor_set(v_reuseFailAlloc_2626_, 1, v_snd_2611_);
v___x_2623_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
lean_object* v___x_2624_; lean_object* v_fst_2625_; 
v___x_2624_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(v___x_2596_, v_edited_2589_, v___x_2623_);
lean_dec_ref(v_edited_2589_);
v_fst_2625_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_fst_2625_);
lean_dec_ref(v___x_2624_);
return v_fst_2625_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(lean_object* v___x_2631_, uint8_t v_inSubst_2632_, lean_object* v___x_2633_, lean_object* v_____r_2634_, lean_object* v_wssIdx_2635_){
_start:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2636_ = lean_box(v_inSubst_2632_);
v___x_2637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2637_, 0, v___x_2631_);
lean_ctor_set(v___x_2637_, 1, v___x_2636_);
v___x_2638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2638_, 0, v_wssIdx_2635_);
lean_ctor_set(v___x_2638_, 1, v___x_2637_);
v___x_2639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2639_, 0, v___x_2633_);
lean_ctor_set(v___x_2639_, 1, v___x_2638_);
v___x_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1___boxed(lean_object* v___x_2641_, lean_object* v_inSubst_2642_, lean_object* v___x_2643_, lean_object* v_____r_2644_, lean_object* v_wssIdx_2645_){
_start:
{
uint8_t v_inSubst_boxed_2646_; lean_object* v_res_2647_; 
v_inSubst_boxed_2646_ = lean_unbox(v_inSubst_2642_);
v_res_2647_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2641_, v_inSubst_boxed_2646_, v___x_2643_, v_____r_2644_, v_wssIdx_2645_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(lean_object* v_fst_2648_, uint8_t v___x_2649_, lean_object* v_fst_2650_, lean_object* v___x_2651_, lean_object* v_00___2652_){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2653_ = lean_box(v___x_2649_);
v___x_2654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2654_, 0, v_fst_2648_);
lean_ctor_set(v___x_2654_, 1, v___x_2653_);
v___x_2655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2655_, 0, v_fst_2650_);
lean_ctor_set(v___x_2655_, 1, v___x_2654_);
v___x_2656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2656_, 0, v___x_2651_);
lean_ctor_set(v___x_2656_, 1, v___x_2655_);
v___x_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2656_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0___boxed(lean_object* v_fst_2658_, lean_object* v___x_2659_, lean_object* v_fst_2660_, lean_object* v___x_2661_, lean_object* v_00___2662_){
_start:
{
uint8_t v___x_9266__boxed_2663_; lean_object* v_res_2664_; 
v___x_9266__boxed_2663_ = lean_unbox(v___x_2659_);
v_res_2664_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2658_, v___x_9266__boxed_2663_, v_fst_2660_, v___x_2661_, v_00___2662_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(uint8_t v_inSubst_2665_, lean_object* v_snd_2666_, lean_object* v_fst_2667_, lean_object* v_____r_2668_, lean_object* v_withWs_2669_, lean_object* v_wssIdx_2670_){
_start:
{
lean_object* v_wss_x27Idx_2672_; uint8_t v___x_2678_; 
v___x_2678_ = lean_unbox(v_snd_2666_);
if (v___x_2678_ == 0)
{
v_wss_x27Idx_2672_ = v_fst_2667_;
goto v___jp_2671_;
}
else
{
lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2679_ = lean_unsigned_to_nat(1u);
v___x_2680_ = lean_nat_add(v_fst_2667_, v___x_2679_);
lean_dec(v_fst_2667_);
v_wss_x27Idx_2672_ = v___x_2680_;
goto v___jp_2671_;
}
v___jp_2671_:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2673_ = lean_box(v_inSubst_2665_);
v___x_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2674_, 0, v_wss_x27Idx_2672_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v___x_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2675_, 0, v_wssIdx_2670_);
lean_ctor_set(v___x_2675_, 1, v___x_2674_);
v___x_2676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2676_, 0, v_withWs_2669_);
lean_ctor_set(v___x_2676_, 1, v___x_2675_);
v___x_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2676_);
return v___x_2677_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2___boxed(lean_object* v_inSubst_2681_, lean_object* v_snd_2682_, lean_object* v_fst_2683_, lean_object* v_____r_2684_, lean_object* v_withWs_2685_, lean_object* v_wssIdx_2686_){
_start:
{
uint8_t v_inSubst_boxed_2687_; lean_object* v_res_2688_; 
v_inSubst_boxed_2687_ = lean_unbox(v_inSubst_2681_);
v_res_2688_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_boxed_2687_, v_snd_2682_, v_fst_2683_, v_____r_2684_, v_withWs_2685_, v_wssIdx_2686_);
lean_dec(v_snd_2682_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(lean_object* v_upperBound_2689_, lean_object* v_diff_2690_, lean_object* v_snd_2691_, lean_object* v_snd_2692_, lean_object* v_a_2693_, lean_object* v_b_2694_){
_start:
{
lean_object* v_a_2696_; lean_object* v___y_2701_; uint8_t v___x_2704_; 
v___x_2704_ = lean_nat_dec_lt(v_a_2693_, v_upperBound_2689_);
if (v___x_2704_ == 0)
{
lean_dec(v_a_2693_);
return v_b_2694_;
}
else
{
lean_object* v___x_2705_; lean_object* v_snd_2706_; lean_object* v_snd_2707_; lean_object* v_fst_2708_; lean_object* v_fst_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2849_; 
v___x_2705_ = lean_array_fget_borrowed(v_diff_2690_, v_a_2693_);
v_snd_2706_ = lean_ctor_get(v_b_2694_, 1);
lean_inc(v_snd_2706_);
v_snd_2707_ = lean_ctor_get(v_snd_2706_, 1);
lean_inc(v_snd_2707_);
v_fst_2708_ = lean_ctor_get(v___x_2705_, 0);
v_fst_2709_ = lean_ctor_get(v_b_2694_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v_b_2694_);
if (v_isSharedCheck_2849_ == 0)
{
lean_object* v_unused_2850_; 
v_unused_2850_ = lean_ctor_get(v_b_2694_, 1);
lean_dec(v_unused_2850_);
v___x_2711_ = v_b_2694_;
v_isShared_2712_ = v_isSharedCheck_2849_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_fst_2709_);
lean_dec(v_b_2694_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2849_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v_fst_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2847_; 
v_fst_2713_ = lean_ctor_get(v_snd_2706_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v_snd_2706_);
if (v_isSharedCheck_2847_ == 0)
{
lean_object* v_unused_2848_; 
v_unused_2848_ = lean_ctor_get(v_snd_2706_, 1);
lean_dec(v_unused_2848_);
v___x_2715_ = v_snd_2706_;
v_isShared_2716_ = v_isSharedCheck_2847_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_fst_2713_);
lean_dec(v_snd_2706_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2847_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v_fst_2717_; lean_object* v_snd_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2846_; 
v_fst_2717_ = lean_ctor_get(v_snd_2707_, 0);
v_snd_2718_ = lean_ctor_get(v_snd_2707_, 1);
v_isSharedCheck_2846_ = !lean_is_exclusive(v_snd_2707_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2720_ = v_snd_2707_;
v_isShared_2721_ = v_isSharedCheck_2846_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_snd_2718_);
lean_inc(v_fst_2717_);
lean_dec(v_snd_2707_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2846_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2722_; lean_object* v___y_2724_; lean_object* v___y_2739_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; uint8_t v___x_2750_; 
lean_inc(v___x_2705_);
v___x_2722_ = lean_array_push(v_fst_2709_, v___x_2705_);
v___x_2747_ = lean_unsigned_to_nat(1u);
v___x_2748_ = lean_nat_add(v_a_2693_, v___x_2747_);
v___x_2749_ = lean_array_get_size(v_diff_2690_);
v___x_2750_ = lean_nat_dec_lt(v___x_2748_, v___x_2749_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; 
lean_dec(v___x_2748_);
lean_del_object(v___x_2720_);
lean_del_object(v___x_2715_);
lean_del_object(v___x_2711_);
v___x_2751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2751_, 0, v_fst_2717_);
lean_ctor_set(v___x_2751_, 1, v_snd_2718_);
v___x_2752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2752_, 0, v_fst_2713_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2722_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v_a_2696_ = v___x_2753_;
goto v___jp_2695_;
}
else
{
lean_object* v___x_2754_; lean_object* v_fst_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2844_; 
v___x_2754_ = lean_array_fget(v_diff_2690_, v___x_2748_);
lean_dec(v___x_2748_);
v_fst_2755_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2844_ == 0)
{
lean_object* v_unused_2845_; 
v_unused_2845_ = lean_ctor_get(v___x_2754_, 1);
lean_dec(v_unused_2845_);
v___x_2757_ = v___x_2754_;
v_isShared_2758_ = v_isSharedCheck_2844_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_fst_2755_);
lean_dec(v___x_2754_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2844_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
uint8_t v_inSubst_2759_; lean_object* v___y_2761_; lean_object* v___x_2770_; uint8_t v___x_2771_; 
v_inSubst_2759_ = 0;
v___x_2770_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2771_ = lean_unbox(v_fst_2708_);
switch(v___x_2771_)
{
case 0:
{
uint8_t v___x_2772_; 
lean_del_object(v___x_2720_);
lean_del_object(v___x_2715_);
lean_del_object(v___x_2711_);
v___x_2772_ = lean_unbox(v_fst_2755_);
switch(v___x_2772_)
{
case 0:
{
lean_object* v___x_2773_; lean_object* v___x_2775_; 
v___x_2773_ = lean_array_get_borrowed(v___x_2770_, v_snd_2691_, v_fst_2717_);
lean_inc(v___x_2773_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 1, v___x_2773_);
v___x_2775_ = v___x_2757_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_fst_2755_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v___x_2773_);
v___x_2775_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2776_ = lean_array_push(v___x_2722_, v___x_2775_);
v___x_2777_ = lean_nat_add(v_fst_2717_, v___x_2747_);
lean_dec(v_fst_2717_);
v___x_2778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2777_);
lean_ctor_set(v___x_2778_, 1, v_snd_2718_);
v___x_2779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2779_, 0, v_fst_2713_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
v___x_2780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2776_);
lean_ctor_set(v___x_2780_, 1, v___x_2779_);
v_a_2696_ = v___x_2780_;
goto v___jp_2695_;
}
}
case 1:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
lean_del_object(v___x_2757_);
lean_dec(v_fst_2755_);
lean_dec(v_snd_2718_);
v___x_2782_ = lean_box(0);
v___x_2783_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2717_, v___x_2704_, v_fst_2713_, v___x_2722_, v___x_2782_);
v___y_2701_ = v___x_2783_;
goto v___jp_2700_;
}
default: 
{
lean_object* v___x_2784_; uint8_t v___x_2785_; 
lean_dec(v_fst_2755_);
v___x_2784_ = lean_array_get_borrowed(v___x_2770_, v_snd_2691_, v_fst_2717_);
v___x_2785_ = lean_unbox(v_snd_2718_);
if (v___x_2785_ == 0)
{
lean_object* v___x_2787_; 
lean_inc(v___x_2784_);
lean_inc(v_fst_2708_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 1, v___x_2784_);
lean_ctor_set(v___x_2757_, 0, v_fst_2708_);
v___x_2787_ = v___x_2757_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_fst_2708_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v___x_2784_);
v___x_2787_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = lean_mk_empty_array_with_capacity(v___x_2747_);
v___x_2789_ = lean_array_push(v___x_2788_, v___x_2787_);
v___y_2761_ = v___x_2789_;
goto v___jp_2760_;
}
}
else
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
lean_del_object(v___x_2757_);
v___x_2791_ = lean_array_get_borrowed(v___x_2770_, v_snd_2692_, v_fst_2713_);
lean_inc(v___x_2784_);
lean_inc(v___x_2791_);
v___x_2792_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2791_, v___x_2784_);
v___y_2761_ = v___x_2792_;
goto v___jp_2760_;
}
}
}
}
case 1:
{
uint8_t v___x_2793_; 
lean_del_object(v___x_2720_);
lean_del_object(v___x_2715_);
lean_del_object(v___x_2711_);
v___x_2793_ = lean_unbox(v_fst_2755_);
switch(v___x_2793_)
{
case 0:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
lean_del_object(v___x_2757_);
lean_dec(v_fst_2755_);
lean_dec(v_snd_2718_);
v___x_2794_ = lean_box(0);
v___x_2795_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2717_, v___x_2704_, v_fst_2713_, v___x_2722_, v___x_2794_);
v___y_2701_ = v___x_2795_;
goto v___jp_2700_;
}
case 1:
{
lean_object* v___x_2796_; lean_object* v___x_2798_; 
v___x_2796_ = lean_array_get_borrowed(v___x_2770_, v_snd_2692_, v_fst_2713_);
lean_inc(v___x_2796_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 1, v___x_2796_);
v___x_2798_ = v___x_2757_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_fst_2755_);
lean_ctor_set(v_reuseFailAlloc_2804_, 1, v___x_2796_);
v___x_2798_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2799_ = lean_array_push(v___x_2722_, v___x_2798_);
v___x_2800_ = lean_nat_add(v_fst_2713_, v___x_2747_);
lean_dec(v_fst_2713_);
v___x_2801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2801_, 0, v_fst_2717_);
lean_ctor_set(v___x_2801_, 1, v_snd_2718_);
v___x_2802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2800_);
lean_ctor_set(v___x_2802_, 1, v___x_2801_);
v___x_2803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2803_, 0, v___x_2799_);
lean_ctor_set(v___x_2803_, 1, v___x_2802_);
v_a_2696_ = v___x_2803_;
goto v___jp_2695_;
}
}
default: 
{
uint8_t v___x_2808_; 
lean_dec(v_fst_2755_);
v___x_2808_ = lean_unbox(v_snd_2718_);
if (v___x_2808_ == 0)
{
lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; uint8_t v___x_2813_; 
v___x_2809_ = lean_array_get_borrowed(v___x_2770_, v_snd_2692_, v_fst_2713_);
v___x_2810_ = lean_unsigned_to_nat(0u);
v___x_2811_ = lean_string_utf8_byte_size(v___x_2809_);
lean_inc(v___x_2809_);
v___x_2812_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2809_);
lean_ctor_set(v___x_2812_, 1, v___x_2810_);
lean_ctor_set(v___x_2812_, 2, v___x_2811_);
v___x_2813_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_2812_);
lean_dec_ref(v___x_2812_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2815_; 
lean_inc(v___x_2809_);
lean_inc(v_fst_2708_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 1, v___x_2809_);
lean_ctor_set(v___x_2757_, 0, v_fst_2708_);
v___x_2815_ = v___x_2757_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_fst_2708_);
lean_ctor_set(v_reuseFailAlloc_2820_, 1, v___x_2809_);
v___x_2815_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2816_ = lean_array_push(v___x_2722_, v___x_2815_);
v___x_2817_ = lean_nat_add(v_fst_2713_, v___x_2747_);
lean_dec(v_fst_2713_);
v___x_2818_ = lean_box(0);
v___x_2819_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2759_, v_snd_2718_, v_fst_2717_, v___x_2818_, v___x_2816_, v___x_2817_);
lean_dec(v_snd_2718_);
v___y_2701_ = v___x_2819_;
goto v___jp_2700_;
}
}
else
{
lean_del_object(v___x_2757_);
goto v___jp_2805_;
}
}
else
{
lean_del_object(v___x_2757_);
goto v___jp_2805_;
}
v___jp_2805_:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = lean_box(0);
v___x_2807_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2759_, v_snd_2718_, v_fst_2717_, v___x_2806_, v___x_2722_, v_fst_2713_);
lean_dec(v_snd_2718_);
v___y_2701_ = v___x_2807_;
goto v___jp_2700_;
}
}
}
}
default: 
{
uint8_t v___x_2821_; 
v___x_2821_ = lean_unbox(v_fst_2755_);
if (v___x_2821_ == 1)
{
lean_object* v___x_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; 
v___x_2822_ = lean_array_get_borrowed(v___x_2770_, v_snd_2692_, v_fst_2713_);
v___x_2823_ = lean_array_get_size(v_snd_2691_);
v___x_2824_ = lean_nat_dec_lt(v_fst_2717_, v___x_2823_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2826_; 
lean_inc(v___x_2822_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 1, v___x_2822_);
v___x_2826_ = v___x_2757_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_fst_2755_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v___x_2822_);
v___x_2826_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = lean_mk_empty_array_with_capacity(v___x_2747_);
v___x_2828_ = lean_array_push(v___x_2827_, v___x_2826_);
v___y_2724_ = v___x_2828_;
goto v___jp_2723_;
}
}
else
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
lean_del_object(v___x_2757_);
lean_dec(v_fst_2755_);
v___x_2830_ = lean_array_fget_borrowed(v_snd_2691_, v_fst_2717_);
lean_inc(v___x_2830_);
lean_inc(v___x_2822_);
v___x_2831_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2822_, v___x_2830_);
v___y_2724_ = v___x_2831_;
goto v___jp_2723_;
}
}
else
{
lean_object* v___x_2832_; lean_object* v___x_2833_; uint8_t v___x_2834_; 
lean_dec(v_fst_2755_);
lean_del_object(v___x_2720_);
lean_del_object(v___x_2715_);
lean_del_object(v___x_2711_);
v___x_2832_ = lean_array_get_borrowed(v___x_2770_, v_snd_2691_, v_fst_2717_);
v___x_2833_ = lean_array_get_size(v_snd_2692_);
v___x_2834_ = lean_nat_dec_lt(v_fst_2713_, v___x_2833_);
if (v___x_2834_ == 0)
{
uint8_t v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2838_; 
v___x_2835_ = 0;
v___x_2836_ = lean_box(v___x_2835_);
lean_inc(v___x_2832_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 1, v___x_2832_);
lean_ctor_set(v___x_2757_, 0, v___x_2836_);
v___x_2838_ = v___x_2757_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2836_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v___x_2832_);
v___x_2838_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = lean_mk_empty_array_with_capacity(v___x_2747_);
v___x_2840_ = lean_array_push(v___x_2839_, v___x_2838_);
v___y_2739_ = v___x_2840_;
goto v___jp_2738_;
}
}
else
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
lean_del_object(v___x_2757_);
v___x_2842_ = lean_array_fget_borrowed(v_snd_2692_, v_fst_2713_);
lean_inc(v___x_2832_);
lean_inc(v___x_2842_);
v___x_2843_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2842_, v___x_2832_);
v___y_2739_ = v___x_2843_;
goto v___jp_2738_;
}
}
}
}
v___jp_2760_:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; uint8_t v___x_2764_; 
v___x_2762_ = l_Array_append___redArg(v___x_2722_, v___y_2761_);
lean_dec_ref(v___y_2761_);
v___x_2763_ = lean_nat_add(v_fst_2717_, v___x_2747_);
lean_dec(v_fst_2717_);
v___x_2764_ = lean_unbox(v_snd_2718_);
lean_dec(v_snd_2718_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = lean_box(0);
v___x_2766_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2763_, v_inSubst_2759_, v___x_2762_, v___x_2765_, v_fst_2713_);
v___y_2701_ = v___x_2766_;
goto v___jp_2700_;
}
else
{
lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2767_ = lean_nat_add(v_fst_2713_, v___x_2747_);
lean_dec(v_fst_2713_);
v___x_2768_ = lean_box(0);
v___x_2769_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2763_, v_inSubst_2759_, v___x_2762_, v___x_2768_, v___x_2767_);
v___y_2701_ = v___x_2769_;
goto v___jp_2700_;
}
}
}
}
v___jp_2723_:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2730_; 
v___x_2725_ = l_Array_append___redArg(v___x_2722_, v___y_2724_);
lean_dec_ref(v___y_2724_);
v___x_2726_ = lean_unsigned_to_nat(1u);
v___x_2727_ = lean_nat_add(v_fst_2713_, v___x_2726_);
lean_dec(v_fst_2713_);
v___x_2728_ = lean_nat_add(v_fst_2717_, v___x_2726_);
lean_dec(v_fst_2717_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v___x_2728_);
v___x_2730_ = v___x_2720_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2728_);
lean_ctor_set(v_reuseFailAlloc_2737_, 1, v_snd_2718_);
v___x_2730_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
lean_object* v___x_2732_; 
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 1, v___x_2730_);
lean_ctor_set(v___x_2715_, 0, v___x_2727_);
v___x_2732_ = v___x_2715_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v___x_2727_);
lean_ctor_set(v_reuseFailAlloc_2736_, 1, v___x_2730_);
v___x_2732_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
lean_object* v___x_2734_; 
if (v_isShared_2712_ == 0)
{
lean_ctor_set(v___x_2711_, 1, v___x_2732_);
lean_ctor_set(v___x_2711_, 0, v___x_2725_);
v___x_2734_ = v___x_2711_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2725_);
lean_ctor_set(v_reuseFailAlloc_2735_, 1, v___x_2732_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
v_a_2696_ = v___x_2734_;
goto v___jp_2695_;
}
}
}
}
v___jp_2738_:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2740_ = l_Array_append___redArg(v___x_2722_, v___y_2739_);
lean_dec_ref(v___y_2739_);
v___x_2741_ = lean_unsigned_to_nat(1u);
v___x_2742_ = lean_nat_add(v_fst_2713_, v___x_2741_);
lean_dec(v_fst_2713_);
v___x_2743_ = lean_nat_add(v_fst_2717_, v___x_2741_);
lean_dec(v_fst_2717_);
v___x_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2743_);
lean_ctor_set(v___x_2744_, 1, v_snd_2718_);
v___x_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2742_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v___x_2746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2740_);
lean_ctor_set(v___x_2746_, 1, v___x_2745_);
v_a_2696_ = v___x_2746_;
goto v___jp_2695_;
}
}
}
}
}
v___jp_2695_:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2697_ = lean_unsigned_to_nat(1u);
v___x_2698_ = lean_nat_add(v_a_2693_, v___x_2697_);
lean_dec(v_a_2693_);
v_a_2693_ = v___x_2698_;
v_b_2694_ = v_a_2696_;
goto _start;
}
v___jp_2700_:
{
if (lean_obj_tag(v___y_2701_) == 0)
{
lean_object* v_a_2702_; 
lean_dec(v_a_2693_);
v_a_2702_ = lean_ctor_get(v___y_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref(v___y_2701_);
return v_a_2702_;
}
else
{
lean_object* v_a_2703_; 
v_a_2703_ = lean_ctor_get(v___y_2701_, 0);
lean_inc(v_a_2703_);
lean_dec_ref(v___y_2701_);
v_a_2696_ = v_a_2703_;
goto v___jp_2695_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___boxed(lean_object* v_upperBound_2851_, lean_object* v_diff_2852_, lean_object* v_snd_2853_, lean_object* v_snd_2854_, lean_object* v_a_2855_, lean_object* v_b_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2851_, v_diff_2852_, v_snd_2853_, v_snd_2854_, v_a_2855_, v_b_2856_);
lean_dec_ref(v_snd_2854_);
lean_dec_ref(v_snd_2853_);
lean_dec_ref(v_diff_2852_);
lean_dec(v_upperBound_2851_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(lean_object* v_s_2868_, lean_object* v_s_x27_2869_){
_start:
{
lean_object* v___x_2870_; lean_object* v_fst_2871_; lean_object* v_snd_2872_; lean_object* v___x_2873_; lean_object* v_fst_2874_; lean_object* v_snd_2875_; lean_object* v___x_2876_; lean_object* v_diff_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v_fst_2882_; lean_object* v___x_2883_; size_t v_sz_2884_; size_t v___x_2885_; lean_object* v___x_2886_; 
v___x_2870_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_2868_);
v_fst_2871_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_fst_2871_);
v_snd_2872_ = lean_ctor_get(v___x_2870_, 1);
lean_inc(v_snd_2872_);
lean_dec_ref(v___x_2870_);
v___x_2873_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_x27_2869_);
v_fst_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_fst_2874_);
v_snd_2875_ = lean_ctor_get(v___x_2873_, 1);
lean_inc(v_snd_2875_);
lean_dec_ref(v___x_2873_);
v___x_2876_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v_diff_2877_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(v___x_2876_, v_fst_2871_, v_fst_2874_);
v___x_2878_ = lean_unsigned_to_nat(0u);
v___x_2879_ = lean_array_get_size(v_diff_2877_);
v___x_2880_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__2));
v___x_2881_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v___x_2879_, v_diff_2877_, v_snd_2875_, v_snd_2872_, v___x_2878_, v___x_2880_);
lean_dec(v_snd_2872_);
lean_dec(v_snd_2875_);
lean_dec_ref(v_diff_2877_);
v_fst_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_fst_2882_);
lean_dec_ref(v___x_2881_);
v___x_2883_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_fst_2882_);
lean_dec(v_fst_2882_);
v_sz_2884_ = lean_array_size(v___x_2883_);
v___x_2885_ = ((size_t)0ULL);
v___x_2886_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_2884_, v___x_2885_, v___x_2883_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___boxed(lean_object* v_s_2887_, lean_object* v_s_x27_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_2887_, v_s_x27_2888_);
lean_dec_ref(v_s_x27_2888_);
lean_dec_ref(v_s_2887_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(lean_object* v_upperBound_2890_, lean_object* v_diff_2891_, lean_object* v_snd_2892_, lean_object* v_snd_2893_, lean_object* v_inst_2894_, lean_object* v_R_2895_, lean_object* v_a_2896_, lean_object* v_b_2897_, lean_object* v_c_2898_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2890_, v_diff_2891_, v_snd_2892_, v_snd_2893_, v_a_2896_, v_b_2897_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___boxed(lean_object* v_upperBound_2900_, lean_object* v_diff_2901_, lean_object* v_snd_2902_, lean_object* v_snd_2903_, lean_object* v_inst_2904_, lean_object* v_R_2905_, lean_object* v_a_2906_, lean_object* v_b_2907_, lean_object* v_c_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(v_upperBound_2900_, v_diff_2901_, v_snd_2902_, v_snd_2903_, v_inst_2904_, v_R_2905_, v_a_2906_, v_b_2907_, v_c_2908_);
lean_dec_ref(v_snd_2903_);
lean_dec_ref(v_snd_2902_);
lean_dec_ref(v_diff_2901_);
lean_dec(v_upperBound_2900_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4(lean_object* v_as_2910_, lean_object* v_as_x27_2911_, lean_object* v_b_2912_, lean_object* v_a_2913_){
_start:
{
lean_object* v___x_2914_; 
v___x_2914_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(v_as_x27_2911_, v_b_2912_);
return v___x_2914_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___boxed(lean_object* v_as_2915_, lean_object* v_as_x27_2916_, lean_object* v_b_2917_, lean_object* v_a_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4(v_as_2915_, v_as_x27_2916_, v_b_2917_, v_a_2918_);
lean_dec(v_as_2915_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7(lean_object* v_lsize_2920_, lean_object* v_rsize_2921_, lean_object* v_histogram_2922_, lean_object* v_index_2923_, lean_object* v_val_2924_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(v_histogram_2922_, v_index_2923_, v_val_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___boxed(lean_object* v_lsize_2926_, lean_object* v_rsize_2927_, lean_object* v_histogram_2928_, lean_object* v_index_2929_, lean_object* v_val_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7(v_lsize_2926_, v_rsize_2927_, v_histogram_2928_, v_index_2929_, v_val_2930_);
lean_dec(v_rsize_2927_);
lean_dec(v_lsize_2926_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8(lean_object* v_upperBound_2932_, lean_object* v___x_2933_, lean_object* v_fst_2934_, lean_object* v___x_2935_, lean_object* v_inst_2936_, lean_object* v_R_2937_, lean_object* v_a_2938_, lean_object* v_b_2939_, lean_object* v_c_2940_){
_start:
{
lean_object* v___x_2941_; 
v___x_2941_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(v_upperBound_2932_, v___x_2933_, v_fst_2934_, v___x_2935_, v_a_2938_, v_b_2939_);
return v___x_2941_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___boxed(lean_object* v_upperBound_2942_, lean_object* v___x_2943_, lean_object* v_fst_2944_, lean_object* v___x_2945_, lean_object* v_inst_2946_, lean_object* v_R_2947_, lean_object* v_a_2948_, lean_object* v_b_2949_, lean_object* v_c_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8(v_upperBound_2942_, v___x_2943_, v_fst_2944_, v___x_2945_, v_inst_2946_, v_R_2947_, v_a_2948_, v_b_2949_, v_c_2950_);
lean_dec(v___x_2945_);
lean_dec_ref(v_fst_2944_);
lean_dec(v___x_2943_);
lean_dec(v_upperBound_2942_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9(lean_object* v_lsize_2952_, lean_object* v_rsize_2953_, lean_object* v_histogram_2954_, lean_object* v_index_2955_, lean_object* v_val_2956_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(v_histogram_2954_, v_index_2955_, v_val_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___boxed(lean_object* v_lsize_2958_, lean_object* v_rsize_2959_, lean_object* v_histogram_2960_, lean_object* v_index_2961_, lean_object* v_val_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9(v_lsize_2958_, v_rsize_2959_, v_histogram_2960_, v_index_2961_, v_val_2962_);
lean_dec(v_rsize_2959_);
lean_dec(v_lsize_2958_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10(lean_object* v_upperBound_2964_, lean_object* v_fst_2965_, lean_object* v___x_2966_, lean_object* v_fst_2967_, lean_object* v_inst_2968_, lean_object* v_R_2969_, lean_object* v_a_2970_, lean_object* v_b_2971_, lean_object* v_c_2972_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(v_upperBound_2964_, v_fst_2965_, v___x_2966_, v_fst_2967_, v_a_2970_, v_b_2971_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___boxed(lean_object* v_upperBound_2974_, lean_object* v_fst_2975_, lean_object* v___x_2976_, lean_object* v_fst_2977_, lean_object* v_inst_2978_, lean_object* v_R_2979_, lean_object* v_a_2980_, lean_object* v_b_2981_, lean_object* v_c_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10(v_upperBound_2974_, v_fst_2975_, v___x_2976_, v_fst_2977_, v_inst_2978_, v_R_2979_, v_a_2980_, v_b_2981_, v_c_2982_);
lean_dec_ref(v_fst_2977_);
lean_dec(v___x_2976_);
lean_dec_ref(v_fst_2975_);
lean_dec(v_upperBound_2974_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11(lean_object* v_00_u03b2_2984_, lean_object* v_m_2985_, lean_object* v_a_2986_){
_start:
{
lean_object* v___x_2987_; 
v___x_2987_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_m_2985_, v_a_2986_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___boxed(lean_object* v_00_u03b2_2988_, lean_object* v_m_2989_, lean_object* v_a_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11(v_00_u03b2_2988_, v_m_2989_, v_a_2990_);
lean_dec_ref(v_a_2990_);
lean_dec_ref(v_m_2989_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12(lean_object* v_00_u03b2_2992_, lean_object* v_m_2993_, lean_object* v_a_2994_, lean_object* v_b_2995_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_m_2993_, v_a_2994_, v_b_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14(lean_object* v_inst_2997_, lean_object* v_R_2998_, lean_object* v_a_2999_, lean_object* v_b_3000_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v_a_2999_, v_b_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20(lean_object* v_00_u03b2_3002_, lean_object* v_a_3003_, lean_object* v_x_3004_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(v_a_3003_, v_x_3004_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___boxed(lean_object* v_00_u03b2_3006_, lean_object* v_a_3007_, lean_object* v_x_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20(v_00_u03b2_3006_, v_a_3007_, v_x_3008_);
lean_dec(v_x_3008_);
lean_dec_ref(v_a_3007_);
return v_res_3009_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22(lean_object* v_00_u03b2_3010_, lean_object* v_a_3011_, lean_object* v_x_3012_){
_start:
{
uint8_t v___x_3013_; 
v___x_3013_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(v_a_3011_, v_x_3012_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___boxed(lean_object* v_00_u03b2_3014_, lean_object* v_a_3015_, lean_object* v_x_3016_){
_start:
{
uint8_t v_res_3017_; lean_object* v_r_3018_; 
v_res_3017_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22(v_00_u03b2_3014_, v_a_3015_, v_x_3016_);
lean_dec(v_x_3016_);
lean_dec_ref(v_a_3015_);
v_r_3018_ = lean_box(v_res_3017_);
return v_r_3018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23(lean_object* v_00_u03b2_3019_, lean_object* v_data_3020_){
_start:
{
lean_object* v___x_3021_; 
v___x_3021_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23___redArg(v_data_3020_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24(lean_object* v_00_u03b2_3022_, lean_object* v_a_3023_, lean_object* v_b_3024_, lean_object* v_x_3025_){
_start:
{
lean_object* v___x_3026_; 
v___x_3026_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(v_a_3023_, v_b_3024_, v_x_3025_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28(lean_object* v_00_u03b2_3027_, lean_object* v_i_3028_, lean_object* v_source_3029_, lean_object* v_target_3030_){
_start:
{
lean_object* v___x_3031_; 
v___x_3031_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28___redArg(v_i_3028_, v_source_3029_, v_target_3030_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_3032_, lean_object* v_x_3033_, lean_object* v_x_3034_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29___redArg(v_x_3033_, v_x_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(lean_object* v_s_3036_){
_start:
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = lean_string_data(v_s_3036_);
v___x_3038_ = lean_array_mk(v___x_3037_);
return v___x_3038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(lean_object* v_s_3039_, lean_object* v_s_x27_3040_){
_start:
{
uint32_t v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v___x_3041_ = 65;
v___x_3042_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3039_);
v___x_3043_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3040_);
v___x_3044_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3041_, v___x_3042_, v___x_3043_);
v___x_3045_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_3044_);
lean_dec_ref(v___x_3044_);
return v___x_3045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(lean_object* v_s_3046_, lean_object* v_s_x27_3047_){
_start:
{
uint8_t v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; uint8_t v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3048_ = 1;
v___x_3049_ = lean_box(v___x_3048_);
v___x_3050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3049_);
lean_ctor_set(v___x_3050_, 1, v_s_3046_);
v___x_3051_ = 0;
v___x_3052_ = lean_box(v___x_3051_);
v___x_3053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
lean_ctor_set(v___x_3053_, 1, v_s_x27_3047_);
v___x_3054_ = lean_unsigned_to_nat(2u);
v___x_3055_ = lean_mk_empty_array_with_capacity(v___x_3054_);
v___x_3056_ = lean_array_push(v___x_3055_, v___x_3050_);
v___x_3057_ = lean_array_push(v___x_3056_, v___x_3053_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(lean_object* v_as_3058_, size_t v_i_3059_, size_t v_stop_3060_, lean_object* v_b_3061_){
_start:
{
lean_object* v___y_3063_; uint8_t v___x_3067_; 
v___x_3067_ = lean_usize_dec_eq(v_i_3059_, v_stop_3060_);
if (v___x_3067_ == 0)
{
lean_object* v___x_3068_; lean_object* v_fst_3069_; uint8_t v___x_3070_; uint8_t v___x_3071_; uint8_t v___x_3072_; 
v___x_3068_ = lean_array_uget_borrowed(v_as_3058_, v_i_3059_);
v_fst_3069_ = lean_ctor_get(v___x_3068_, 0);
v___x_3070_ = 2;
v___x_3071_ = lean_unbox(v_fst_3069_);
v___x_3072_ = l_Lean_Diff_instBEqAction_beq(v___x_3071_, v___x_3070_);
if (v___x_3072_ == 0)
{
lean_object* v___x_3073_; 
lean_inc(v___x_3068_);
v___x_3073_ = lean_array_push(v_b_3061_, v___x_3068_);
v___y_3063_ = v___x_3073_;
goto v___jp_3062_;
}
else
{
v___y_3063_ = v_b_3061_;
goto v___jp_3062_;
}
}
else
{
return v_b_3061_;
}
v___jp_3062_:
{
size_t v___x_3064_; size_t v___x_3065_; 
v___x_3064_ = ((size_t)1ULL);
v___x_3065_ = lean_usize_add(v_i_3059_, v___x_3064_);
v_i_3059_ = v___x_3065_;
v_b_3061_ = v___y_3063_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0___boxed(lean_object* v_as_3074_, lean_object* v_i_3075_, lean_object* v_stop_3076_, lean_object* v_b_3077_){
_start:
{
size_t v_i_boxed_3078_; size_t v_stop_boxed_3079_; lean_object* v_res_3080_; 
v_i_boxed_3078_ = lean_unbox_usize(v_i_3075_);
lean_dec(v_i_3075_);
v_stop_boxed_3079_ = lean_unbox_usize(v_stop_3076_);
lean_dec(v_stop_3076_);
v_res_3080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_as_3074_, v_i_boxed_3078_, v_stop_boxed_3079_, v_b_3077_);
lean_dec_ref(v_as_3074_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff(lean_object* v_s_3081_, lean_object* v_s_x27_3082_, uint8_t v_granularity_3083_){
_start:
{
lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; uint8_t v___y_3088_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; 
switch(v_granularity_3083_)
{
case 0:
{
uint32_t v___x_3106_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___y_3131_; uint8_t v___x_3137_; 
v___x_3106_ = 65;
v___x_3128_ = lean_string_length(v_s_3081_);
v___x_3129_ = lean_string_length(v_s_x27_3082_);
v___x_3137_ = lean_nat_dec_le(v___x_3128_, v___x_3129_);
if (v___x_3137_ == 0)
{
v___y_3131_ = v___x_3129_;
goto v___jp_3130_;
}
else
{
v___y_3131_ = v___x_3128_;
goto v___jp_3130_;
}
v___jp_3107_:
{
lean_object* v___x_3112_; lean_object* v_maxWordDiffDistance_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v_charDiffRaw_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; uint8_t v___x_3120_; 
v___x_3112_ = lean_nat_shiftr(v___y_3111_, v___y_3109_);
lean_dec(v___y_3111_);
v_maxWordDiffDistance_3113_ = lean_nat_add(v___y_3110_, v___x_3112_);
lean_dec(v___x_3112_);
lean_dec(v___y_3110_);
lean_inc_ref(v_s_3081_);
v___x_3114_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3081_);
lean_inc_ref(v_s_x27_3082_);
v___x_3115_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3082_);
v_charDiffRaw_3116_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3106_, v___x_3114_, v___x_3115_);
v___x_3117_ = lean_unsigned_to_nat(0u);
v___x_3118_ = lean_array_get_size(v_charDiffRaw_3116_);
v___x_3119_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0));
v___x_3120_ = lean_nat_dec_lt(v___x_3117_, v___x_3118_);
if (v___x_3120_ == 0)
{
v___y_3096_ = v___y_3108_;
v___y_3097_ = v_maxWordDiffDistance_3113_;
v___y_3098_ = v_charDiffRaw_3116_;
v___y_3099_ = v___x_3119_;
goto v___jp_3095_;
}
else
{
uint8_t v___x_3121_; 
v___x_3121_ = lean_nat_dec_le(v___x_3118_, v___x_3118_);
if (v___x_3121_ == 0)
{
if (v___x_3120_ == 0)
{
v___y_3096_ = v___y_3108_;
v___y_3097_ = v_maxWordDiffDistance_3113_;
v___y_3098_ = v_charDiffRaw_3116_;
v___y_3099_ = v___x_3119_;
goto v___jp_3095_;
}
else
{
size_t v___x_3122_; size_t v___x_3123_; lean_object* v___x_3124_; 
v___x_3122_ = ((size_t)0ULL);
v___x_3123_ = lean_usize_of_nat(v___x_3118_);
v___x_3124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3116_, v___x_3122_, v___x_3123_, v___x_3119_);
v___y_3096_ = v___y_3108_;
v___y_3097_ = v_maxWordDiffDistance_3113_;
v___y_3098_ = v_charDiffRaw_3116_;
v___y_3099_ = v___x_3124_;
goto v___jp_3095_;
}
}
else
{
size_t v___x_3125_; size_t v___x_3126_; lean_object* v___x_3127_; 
v___x_3125_ = ((size_t)0ULL);
v___x_3126_ = lean_usize_of_nat(v___x_3118_);
v___x_3127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3116_, v___x_3125_, v___x_3126_, v___x_3119_);
v___y_3096_ = v___y_3108_;
v___y_3097_ = v_maxWordDiffDistance_3113_;
v___y_3098_ = v_charDiffRaw_3116_;
v___y_3099_ = v___x_3127_;
goto v___jp_3095_;
}
}
}
v___jp_3130_:
{
lean_object* v___x_3132_; lean_object* v_maxCharDiffDistance_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; uint8_t v___x_3136_; 
v___x_3132_ = lean_unsigned_to_nat(5u);
v_maxCharDiffDistance_3133_ = lean_nat_div(v___y_3131_, v___x_3132_);
v___x_3134_ = lean_unsigned_to_nat(1u);
v___x_3135_ = lean_nat_shiftr(v___y_3131_, v___x_3134_);
lean_dec(v___y_3131_);
v___x_3136_ = lean_nat_dec_le(v___x_3128_, v___x_3129_);
if (v___x_3136_ == 0)
{
v___y_3108_ = v_maxCharDiffDistance_3133_;
v___y_3109_ = v___x_3134_;
v___y_3110_ = v___x_3135_;
v___y_3111_ = v___x_3128_;
goto v___jp_3107_;
}
else
{
v___y_3108_ = v_maxCharDiffDistance_3133_;
v___y_3109_ = v___x_3134_;
v___y_3110_ = v___x_3135_;
v___y_3111_ = v___x_3129_;
goto v___jp_3107_;
}
}
}
case 1:
{
lean_object* v___x_3138_; 
v___x_3138_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(v_s_3081_, v_s_x27_3082_);
return v___x_3138_;
}
case 2:
{
lean_object* v___x_3139_; 
v___x_3139_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3081_, v_s_x27_3082_);
lean_dec_ref(v_s_x27_3082_);
lean_dec_ref(v_s_3081_);
return v___x_3139_;
}
case 3:
{
lean_object* v___x_3140_; 
v___x_3140_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3081_, v_s_x27_3082_);
return v___x_3140_;
}
default: 
{
uint8_t v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
lean_dec_ref(v_s_3081_);
v___x_3141_ = 0;
v___x_3142_ = lean_box(v___x_3141_);
v___x_3143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3143_, 0, v___x_3142_);
lean_ctor_set(v___x_3143_, 1, v_s_x27_3082_);
v___x_3144_ = lean_unsigned_to_nat(1u);
v___x_3145_ = lean_mk_empty_array_with_capacity(v___x_3144_);
v___x_3146_ = lean_array_push(v___x_3145_, v___x_3143_);
return v___x_3146_;
}
}
v___jp_3084_:
{
if (v___y_3088_ == 0)
{
uint8_t v___x_3089_; 
lean_dec_ref(v___y_3086_);
v___x_3089_ = lean_nat_dec_le(v___y_3087_, v___y_3085_);
lean_dec(v___y_3085_);
lean_dec(v___y_3087_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; 
v___x_3090_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3081_, v_s_x27_3082_);
return v___x_3090_;
}
else
{
lean_object* v___x_3091_; 
v___x_3091_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3081_, v_s_x27_3082_);
lean_dec_ref(v_s_x27_3082_);
lean_dec_ref(v_s_3081_);
return v___x_3091_;
}
}
else
{
size_t v_sz_3092_; size_t v___x_3093_; lean_object* v___x_3094_; 
lean_dec(v___y_3087_);
lean_dec(v___y_3085_);
lean_dec_ref(v_s_x27_3082_);
lean_dec_ref(v_s_3081_);
v_sz_3092_ = lean_array_size(v___y_3086_);
v___x_3093_ = ((size_t)0ULL);
v___x_3094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_3092_, v___x_3093_, v___y_3086_);
return v___x_3094_;
}
}
v___jp_3095_:
{
lean_object* v_approxEditDistance_3100_; lean_object* v_charArrDiff_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; uint8_t v___x_3104_; 
v_approxEditDistance_3100_ = lean_array_get_size(v___y_3099_);
lean_dec_ref(v___y_3099_);
v_charArrDiff_3101_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v___y_3098_);
lean_dec_ref(v___y_3098_);
v___x_3102_ = lean_array_get_size(v_charArrDiff_3101_);
v___x_3103_ = lean_unsigned_to_nat(3u);
v___x_3104_ = lean_nat_dec_le(v___x_3102_, v___x_3103_);
if (v___x_3104_ == 0)
{
uint8_t v___x_3105_; 
v___x_3105_ = lean_nat_dec_le(v_approxEditDistance_3100_, v___y_3096_);
lean_dec(v___y_3096_);
v___y_3085_ = v___y_3097_;
v___y_3086_ = v_charArrDiff_3101_;
v___y_3087_ = v_approxEditDistance_3100_;
v___y_3088_ = v___x_3105_;
goto v___jp_3084_;
}
else
{
lean_dec(v___y_3096_);
v___y_3085_ = v___y_3097_;
v___y_3086_ = v_charArrDiff_3101_;
v___y_3087_ = v_approxEditDistance_3100_;
v___y_3088_ = v___x_3104_;
goto v___jp_3084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff___boxed(lean_object* v_s_3147_, lean_object* v_s_x27_3148_, lean_object* v_granularity_3149_){
_start:
{
uint8_t v_granularity_boxed_3150_; lean_object* v_res_3151_; 
v_granularity_boxed_3150_ = lean_unbox(v_granularity_3149_);
v_res_3151_ = l_Lean_Meta_Hint_readableDiff(v_s_3147_, v_s_x27_3148_, v_granularity_boxed_3150_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(lean_object* v_as_3152_, size_t v_i_3153_, size_t v_stop_3154_, lean_object* v_b_3155_){
_start:
{
uint8_t v___x_3156_; 
v___x_3156_ = lean_usize_dec_eq(v_i_3153_, v_stop_3154_);
if (v___x_3156_ == 0)
{
lean_object* v___x_3157_; lean_object* v_snd_3158_; lean_object* v___x_3159_; size_t v___x_3160_; size_t v___x_3161_; 
v___x_3157_ = lean_array_uget_borrowed(v_as_3152_, v_i_3153_);
v_snd_3158_ = lean_ctor_get(v___x_3157_, 1);
v___x_3159_ = lean_string_append(v_b_3155_, v_snd_3158_);
v___x_3160_ = ((size_t)1ULL);
v___x_3161_ = lean_usize_add(v_i_3153_, v___x_3160_);
v_i_3153_ = v___x_3161_;
v_b_3155_ = v___x_3159_;
goto _start;
}
else
{
return v_b_3155_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0___boxed(lean_object* v_as_3163_, lean_object* v_i_3164_, lean_object* v_stop_3165_, lean_object* v_b_3166_){
_start:
{
size_t v_i_boxed_3167_; size_t v_stop_boxed_3168_; lean_object* v_res_3169_; 
v_i_boxed_3167_ = lean_unbox_usize(v_i_3164_);
lean_dec(v_i_3164_);
v_stop_boxed_3168_ = lean_unbox_usize(v_stop_3165_);
lean_dec(v_stop_3165_);
v_res_3169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v_as_3163_, v_i_boxed_3167_, v_stop_boxed_3168_, v_b_3166_);
lean_dec_ref(v_as_3163_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(lean_object* v_t_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v___x_3173_; lean_object* v_infoState_3174_; uint8_t v_enabled_3175_; 
v___x_3173_ = lean_st_ref_get(v___y_3171_);
v_infoState_3174_ = lean_ctor_get(v___x_3173_, 7);
lean_inc_ref(v_infoState_3174_);
lean_dec(v___x_3173_);
v_enabled_3175_ = lean_ctor_get_uint8(v_infoState_3174_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3174_);
if (v_enabled_3175_ == 0)
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
lean_dec_ref(v_t_3170_);
v___x_3176_ = lean_box(0);
v___x_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3177_, 0, v___x_3176_);
return v___x_3177_;
}
else
{
lean_object* v___x_3178_; lean_object* v_infoState_3179_; lean_object* v_env_3180_; lean_object* v_nextMacroScope_3181_; lean_object* v_ngen_3182_; lean_object* v_auxDeclNGen_3183_; lean_object* v_traceState_3184_; lean_object* v_cache_3185_; lean_object* v_messages_3186_; lean_object* v_snapshotTasks_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3209_; 
v___x_3178_ = lean_st_ref_take(v___y_3171_);
v_infoState_3179_ = lean_ctor_get(v___x_3178_, 7);
v_env_3180_ = lean_ctor_get(v___x_3178_, 0);
v_nextMacroScope_3181_ = lean_ctor_get(v___x_3178_, 1);
v_ngen_3182_ = lean_ctor_get(v___x_3178_, 2);
v_auxDeclNGen_3183_ = lean_ctor_get(v___x_3178_, 3);
v_traceState_3184_ = lean_ctor_get(v___x_3178_, 4);
v_cache_3185_ = lean_ctor_get(v___x_3178_, 5);
v_messages_3186_ = lean_ctor_get(v___x_3178_, 6);
v_snapshotTasks_3187_ = lean_ctor_get(v___x_3178_, 8);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3189_ = v___x_3178_;
v_isShared_3190_ = v_isSharedCheck_3209_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_snapshotTasks_3187_);
lean_inc(v_infoState_3179_);
lean_inc(v_messages_3186_);
lean_inc(v_cache_3185_);
lean_inc(v_traceState_3184_);
lean_inc(v_auxDeclNGen_3183_);
lean_inc(v_ngen_3182_);
lean_inc(v_nextMacroScope_3181_);
lean_inc(v_env_3180_);
lean_dec(v___x_3178_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3209_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
uint8_t v_enabled_3191_; lean_object* v_assignment_3192_; lean_object* v_lazyAssignment_3193_; lean_object* v_trees_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3208_; 
v_enabled_3191_ = lean_ctor_get_uint8(v_infoState_3179_, sizeof(void*)*3);
v_assignment_3192_ = lean_ctor_get(v_infoState_3179_, 0);
v_lazyAssignment_3193_ = lean_ctor_get(v_infoState_3179_, 1);
v_trees_3194_ = lean_ctor_get(v_infoState_3179_, 2);
v_isSharedCheck_3208_ = !lean_is_exclusive(v_infoState_3179_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3196_ = v_infoState_3179_;
v_isShared_3197_ = v_isSharedCheck_3208_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_trees_3194_);
lean_inc(v_lazyAssignment_3193_);
lean_inc(v_assignment_3192_);
lean_dec(v_infoState_3179_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3208_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3198_; lean_object* v___x_3200_; 
v___x_3198_ = l_Lean_PersistentArray_push___redArg(v_trees_3194_, v_t_3170_);
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 2, v___x_3198_);
v___x_3200_ = v___x_3196_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_assignment_3192_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v_lazyAssignment_3193_);
lean_ctor_set(v_reuseFailAlloc_3207_, 2, v___x_3198_);
lean_ctor_set_uint8(v_reuseFailAlloc_3207_, sizeof(void*)*3, v_enabled_3191_);
v___x_3200_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
lean_object* v___x_3202_; 
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 7, v___x_3200_);
v___x_3202_ = v___x_3189_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_env_3180_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v_nextMacroScope_3181_);
lean_ctor_set(v_reuseFailAlloc_3206_, 2, v_ngen_3182_);
lean_ctor_set(v_reuseFailAlloc_3206_, 3, v_auxDeclNGen_3183_);
lean_ctor_set(v_reuseFailAlloc_3206_, 4, v_traceState_3184_);
lean_ctor_set(v_reuseFailAlloc_3206_, 5, v_cache_3185_);
lean_ctor_set(v_reuseFailAlloc_3206_, 6, v_messages_3186_);
lean_ctor_set(v_reuseFailAlloc_3206_, 7, v___x_3200_);
lean_ctor_set(v_reuseFailAlloc_3206_, 8, v_snapshotTasks_3187_);
v___x_3202_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3203_ = lean_st_ref_set(v___y_3171_, v___x_3202_);
v___x_3204_ = lean_box(0);
v___x_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3204_);
return v___x_3205_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg___boxed(lean_object* v_t_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
lean_object* v_res_3213_; 
v_res_3213_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3210_, v___y_3211_);
lean_dec(v___y_3211_);
return v_res_3213_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3214_ = lean_unsigned_to_nat(32u);
v___x_3215_ = lean_mk_empty_array_with_capacity(v___x_3214_);
v___x_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
return v___x_3216_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1(void){
_start:
{
size_t v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3217_ = ((size_t)5ULL);
v___x_3218_ = lean_unsigned_to_nat(0u);
v___x_3219_ = lean_unsigned_to_nat(32u);
v___x_3220_ = lean_mk_empty_array_with_capacity(v___x_3219_);
v___x_3221_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0);
v___x_3222_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3222_, 0, v___x_3221_);
lean_ctor_set(v___x_3222_, 1, v___x_3220_);
lean_ctor_set(v___x_3222_, 2, v___x_3218_);
lean_ctor_set(v___x_3222_, 3, v___x_3218_);
lean_ctor_set_usize(v___x_3222_, 4, v___x_3217_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(lean_object* v_t_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
lean_object* v___x_3227_; lean_object* v_infoState_3228_; uint8_t v_enabled_3229_; 
v___x_3227_ = lean_st_ref_get(v___y_3225_);
v_infoState_3228_ = lean_ctor_get(v___x_3227_, 7);
lean_inc_ref(v_infoState_3228_);
lean_dec(v___x_3227_);
v_enabled_3229_ = lean_ctor_get_uint8(v_infoState_3228_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3228_);
if (v_enabled_3229_ == 0)
{
lean_object* v___x_3230_; lean_object* v___x_3231_; 
lean_dec_ref(v_t_3223_);
v___x_3230_ = lean_box(0);
v___x_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
return v___x_3231_;
}
else
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3232_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1);
v___x_3233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3233_, 0, v_t_3223_);
lean_ctor_set(v___x_3233_, 1, v___x_3232_);
v___x_3234_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v___x_3233_, v___y_3225_);
return v___x_3234_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___boxed(lean_object* v_t_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v_t_3235_, v___y_3236_, v___y_3237_);
lean_dec(v___y_3237_);
lean_dec_ref(v___y_3236_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0(lean_object* v___x_3240_, lean_object* v___y_3241_){
_start:
{
lean_object* v___x_3242_; 
v___x_3242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3240_);
lean_ctor_set(v___x_3242_, 1, v___y_3241_);
return v___x_3242_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3244_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__0));
v___x_3245_ = l_Lean_stringToMessageData(v___x_3244_);
return v___x_3245_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3247_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__2));
v___x_3248_ = l_Lean_stringToMessageData(v___x_3247_);
return v___x_3248_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29(void){
_start:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; 
v___x_3297_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__28));
v___x_3298_ = l_Lean_Json_mkObj(v___x_3297_);
return v___x_3298_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30(void){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3299_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29);
v___x_3300_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__19));
v___x_3301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___x_3300_);
lean_ctor_set(v___x_3301_, 1, v___x_3299_);
return v___x_3301_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31(void){
_start:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3302_ = lean_box(0);
v___x_3303_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30);
v___x_3304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
lean_ctor_set(v___x_3304_, 1, v___x_3302_);
return v___x_3304_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33(void){
_start:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3307_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__32));
v___x_3308_ = l_Lean_MessageData_ofFormat(v___x_3307_);
return v___x_3308_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35(void){
_start:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__34));
v___x_3311_ = l_Lean_stringToMessageData(v___x_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(lean_object* v_suggestions_3313_, uint8_t v_forceList_3314_, lean_object* v_codeActionPrefix_x3f_3315_, lean_object* v_ref_3316_, lean_object* v_as_3317_, size_t v_sz_3318_, size_t v_i_3319_, lean_object* v_b_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v_a_3325_; lean_object* v___y_3330_; lean_object* v___y_3334_; lean_object* v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3341_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; uint8_t v___x_3369_; 
v___x_3369_ = lean_usize_dec_lt(v_i_3319_, v_sz_3318_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3370_; 
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec(v_ref_3316_);
lean_dec(v_codeActionPrefix_x3f_3315_);
v___x_3370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3370_, 0, v_b_3320_);
return v___x_3370_;
}
else
{
lean_object* v_a_3371_; lean_object* v_span_x3f_3372_; lean_object* v___x_3373_; uint8_t v___y_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3378_; lean_object* v___y_3379_; lean_object* v___y_3380_; uint8_t v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; uint8_t v___y_3461_; uint8_t v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; uint8_t v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; uint8_t v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; uint8_t v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v_postInfo_x3f_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; uint8_t v___y_3485_; lean_object* v___y_3486_; uint8_t v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v_edits_3491_; uint8_t v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v_stop_3501_; uint8_t v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v_edits_3506_; lean_object* v___y_3522_; uint8_t v___y_3523_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3526_; uint8_t v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v_edits_3531_; lean_object* v___y_3532_; lean_object* v___x_3556_; lean_object* v___y_3558_; uint8_t v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3561_; lean_object* v___y_3562_; uint8_t v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; uint8_t v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; uint8_t v___y_3607_; lean_object* v___y_3608_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3621_; 
v_a_3371_ = lean_array_uget_borrowed(v_as_3317_, v_i_3319_);
v_span_x3f_3372_ = lean_ctor_get(v_a_3371_, 1);
v___x_3373_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_3556_ = l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_;
if (lean_obj_tag(v_span_x3f_3372_) == 0)
{
lean_inc(v_ref_3316_);
v___y_3621_ = v_ref_3316_;
goto v___jp_3620_;
}
else
{
lean_object* v_val_3642_; 
v_val_3642_ = lean_ctor_get(v_span_x3f_3372_, 0);
lean_inc(v_val_3642_);
v___y_3621_ = v_val_3642_;
goto v___jp_3620_;
}
v___jp_3374_:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___f_3395_; 
lean_inc_ref(v___y_3376_);
v___x_3381_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson(v___y_3376_);
v___x_3382_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__9));
v___x_3383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3382_);
lean_ctor_set(v___x_3383_, 1, v___x_3381_);
v___x_3384_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3385_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3385_, 0, v___y_3377_);
v___x_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3384_);
lean_ctor_set(v___x_3386_, 1, v___x_3385_);
v___x_3387_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3388_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3380_);
v___x_3389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3387_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
v___x_3390_ = lean_box(0);
v___x_3391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3389_);
lean_ctor_set(v___x_3391_, 1, v___x_3390_);
v___x_3392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3386_);
lean_ctor_set(v___x_3392_, 1, v___x_3391_);
v___x_3393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3383_);
lean_ctor_set(v___x_3393_, 1, v___x_3392_);
v___x_3394_ = l_Lean_Json_mkObj(v___x_3393_);
v___f_3395_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3395_, 0, v___x_3394_);
if (v___y_3375_ == 0)
{
lean_object* v___x_3396_; 
v___x_3396_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString(v___y_3376_);
v___y_3349_ = v___y_3379_;
v___y_3350_ = v___y_3378_;
v___y_3351_ = v___f_3395_;
v___y_3352_ = v___x_3396_;
goto v___jp_3348_;
}
else
{
lean_object* v___x_3397_; lean_object* v___x_3398_; uint8_t v___x_3399_; 
v___x_3397_ = lean_unsigned_to_nat(0u);
v___x_3398_ = lean_array_get_size(v___y_3376_);
v___x_3399_ = lean_nat_dec_lt(v___x_3397_, v___x_3398_);
if (v___x_3399_ == 0)
{
lean_dec_ref(v___y_3376_);
v___y_3349_ = v___y_3379_;
v___y_3350_ = v___y_3378_;
v___y_3351_ = v___f_3395_;
v___y_3352_ = v___x_3373_;
goto v___jp_3348_;
}
else
{
uint8_t v___x_3400_; 
v___x_3400_ = lean_nat_dec_le(v___x_3398_, v___x_3398_);
if (v___x_3400_ == 0)
{
if (v___x_3399_ == 0)
{
lean_dec_ref(v___y_3376_);
v___y_3349_ = v___y_3379_;
v___y_3350_ = v___y_3378_;
v___y_3351_ = v___f_3395_;
v___y_3352_ = v___x_3373_;
goto v___jp_3348_;
}
else
{
size_t v___x_3401_; size_t v___x_3402_; lean_object* v___x_3403_; 
v___x_3401_ = ((size_t)0ULL);
v___x_3402_ = lean_usize_of_nat(v___x_3398_);
v___x_3403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3376_, v___x_3401_, v___x_3402_, v___x_3373_);
lean_dec_ref(v___y_3376_);
v___y_3349_ = v___y_3379_;
v___y_3350_ = v___y_3378_;
v___y_3351_ = v___f_3395_;
v___y_3352_ = v___x_3403_;
goto v___jp_3348_;
}
}
else
{
size_t v___x_3404_; size_t v___x_3405_; lean_object* v___x_3406_; 
v___x_3404_ = ((size_t)0ULL);
v___x_3405_ = lean_usize_of_nat(v___x_3398_);
v___x_3406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3376_, v___x_3404_, v___x_3405_, v___x_3373_);
lean_dec_ref(v___y_3376_);
v___y_3349_ = v___y_3379_;
v___y_3350_ = v___y_3378_;
v___y_3351_ = v___f_3395_;
v___y_3352_ = v___x_3406_;
goto v___jp_3348_;
}
}
}
}
v___jp_3407_:
{
if (lean_obj_tag(v___y_3414_) == 0)
{
lean_object* v___x_3416_; uint64_t v_javascriptHash_3417_; lean_object* v_suggestion_3418_; lean_object* v_messageData_x3f_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___f_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
lean_dec_ref(v___y_3409_);
v___x_3416_ = l_Lean_Meta_Hint_textInsertionWidget;
v_javascriptHash_3417_ = lean_ctor_get_uint64(v___x_3416_, sizeof(void*)*1);
v_suggestion_3418_ = lean_ctor_get(v___y_3413_, 0);
lean_inc_ref(v_suggestion_3418_);
v_messageData_x3f_3419_ = lean_ctor_get(v___y_3413_, 4);
lean_inc(v_messageData_x3f_3419_);
lean_dec_ref(v___y_3413_);
v___x_3420_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18));
v___x_3421_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3422_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3415_);
v___x_3423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3421_);
lean_ctor_set(v___x_3423_, 1, v___x_3422_);
v___x_3424_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3425_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3425_, 0, v___y_3410_);
v___x_3426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3424_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31);
v___x_3428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3428_, 0, v___x_3426_);
lean_ctor_set(v___x_3428_, 1, v___x_3427_);
v___x_3429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3423_);
lean_ctor_set(v___x_3429_, 1, v___x_3428_);
v___x_3430_ = l_Lean_Json_mkObj(v___x_3429_);
v___f_3431_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3431_, 0, v___x_3430_);
v___x_3432_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3432_, 0, v___x_3420_);
lean_ctor_set(v___x_3432_, 1, v___f_3431_);
lean_ctor_set_uint64(v___x_3432_, sizeof(void*)*2, v_javascriptHash_3417_);
v___x_3433_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33);
v___x_3434_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3432_);
lean_ctor_set(v___x_3434_, 1, v___x_3433_);
v___x_3435_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
lean_ctor_set(v___x_3436_, 1, v___x_3434_);
v___x_3437_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35);
v___x_3438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3436_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
v___x_3439_ = l_Lean_stringToMessageData(v___y_3412_);
v___x_3440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3440_, 0, v___x_3438_);
lean_ctor_set(v___x_3440_, 1, v___x_3439_);
if (lean_obj_tag(v_messageData_x3f_3419_) == 0)
{
if (lean_obj_tag(v_suggestion_3418_) == 0)
{
lean_object* v_a_3441_; lean_object* v___x_3442_; 
v_a_3441_ = lean_ctor_get(v_suggestion_3418_, 1);
lean_inc(v_a_3441_);
lean_dec_ref(v_suggestion_3418_);
v___x_3442_ = l_Lean_MessageData_ofSyntax(v_a_3441_);
v___y_3334_ = v___x_3440_;
v___y_3335_ = v___y_3411_;
v___y_3336_ = v___x_3442_;
goto v___jp_3333_;
}
else
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3451_; 
v_a_3443_ = lean_ctor_get(v_suggestion_3418_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v_suggestion_3418_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3445_ = v_suggestion_3418_;
v_isShared_3446_ = v_isSharedCheck_3451_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v_suggestion_3418_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3451_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3448_; 
if (v_isShared_3446_ == 0)
{
lean_ctor_set_tag(v___x_3445_, 3);
v___x_3448_ = v___x_3445_;
goto v_reusejp_3447_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3443_);
v___x_3448_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3447_;
}
v_reusejp_3447_:
{
lean_object* v___x_3449_; 
v___x_3449_ = l_Lean_MessageData_ofFormat(v___x_3448_);
v___y_3334_ = v___x_3440_;
v___y_3335_ = v___y_3411_;
v___y_3336_ = v___x_3449_;
goto v___jp_3333_;
}
}
}
}
else
{
lean_object* v_val_3452_; 
lean_dec_ref(v_suggestion_3418_);
v_val_3452_ = lean_ctor_get(v_messageData_x3f_3419_, 0);
lean_inc(v_val_3452_);
lean_dec_ref(v_messageData_x3f_3419_);
v___y_3334_ = v___x_3440_;
v___y_3335_ = v___y_3411_;
v___y_3336_ = v_val_3452_;
goto v___jp_3333_;
}
}
else
{
lean_dec_ref(v___y_3414_);
lean_dec_ref(v___y_3413_);
v___y_3375_ = v___y_3408_;
v___y_3376_ = v___y_3409_;
v___y_3377_ = v___y_3410_;
v___y_3378_ = v___y_3411_;
v___y_3379_ = v___y_3412_;
v___y_3380_ = v___y_3415_;
goto v___jp_3374_;
}
}
v___jp_3453_:
{
if (v___y_3461_ == 0)
{
lean_object* v_messageData_x3f_3462_; 
v_messageData_x3f_3462_ = lean_ctor_get(v___y_3459_, 4);
if (lean_obj_tag(v_messageData_x3f_3462_) == 0)
{
lean_dec_ref(v___y_3459_);
lean_dec(v___y_3458_);
v___y_3375_ = v___y_3461_;
v___y_3376_ = v___y_3454_;
v___y_3377_ = v___y_3455_;
v___y_3378_ = v___y_3456_;
v___y_3379_ = v___y_3457_;
v___y_3380_ = v___y_3460_;
goto v___jp_3374_;
}
else
{
v___y_3408_ = v___y_3461_;
v___y_3409_ = v___y_3454_;
v___y_3410_ = v___y_3455_;
v___y_3411_ = v___y_3456_;
v___y_3412_ = v___y_3457_;
v___y_3413_ = v___y_3459_;
v___y_3414_ = v___y_3458_;
v___y_3415_ = v___y_3460_;
goto v___jp_3407_;
}
}
else
{
v___y_3408_ = v___y_3461_;
v___y_3409_ = v___y_3454_;
v___y_3410_ = v___y_3455_;
v___y_3411_ = v___y_3456_;
v___y_3412_ = v___y_3457_;
v___y_3413_ = v___y_3459_;
v___y_3414_ = v___y_3458_;
v___y_3415_ = v___y_3460_;
goto v___jp_3407_;
}
}
v___jp_3463_:
{
if (v___y_3467_ == 4)
{
v___y_3454_ = v___y_3465_;
v___y_3455_ = v___y_3466_;
v___y_3456_ = v___y_3472_;
v___y_3457_ = v___y_3468_;
v___y_3458_ = v___y_3470_;
v___y_3459_ = v___y_3469_;
v___y_3460_ = v___y_3471_;
v___y_3461_ = v___x_3369_;
goto v___jp_3453_;
}
else
{
v___y_3454_ = v___y_3465_;
v___y_3455_ = v___y_3466_;
v___y_3456_ = v___y_3472_;
v___y_3457_ = v___y_3468_;
v___y_3458_ = v___y_3470_;
v___y_3459_ = v___y_3469_;
v___y_3460_ = v___y_3471_;
v___y_3461_ = v___y_3464_;
goto v___jp_3453_;
}
}
v___jp_3473_:
{
if (lean_obj_tag(v_postInfo_x3f_3480_) == 0)
{
v___y_3464_ = v___y_3474_;
v___y_3465_ = v___y_3475_;
v___y_3466_ = v___y_3476_;
v___y_3467_ = v___y_3477_;
v___y_3468_ = v___y_3482_;
v___y_3469_ = v___y_3479_;
v___y_3470_ = v___y_3478_;
v___y_3471_ = v___y_3481_;
v___y_3472_ = v___x_3373_;
goto v___jp_3463_;
}
else
{
lean_object* v_val_3483_; 
v_val_3483_ = lean_ctor_get(v_postInfo_x3f_3480_, 0);
lean_inc(v_val_3483_);
lean_dec_ref(v_postInfo_x3f_3480_);
v___y_3464_ = v___y_3474_;
v___y_3465_ = v___y_3475_;
v___y_3466_ = v___y_3476_;
v___y_3467_ = v___y_3477_;
v___y_3468_ = v___y_3482_;
v___y_3469_ = v___y_3479_;
v___y_3470_ = v___y_3478_;
v___y_3471_ = v___y_3481_;
v___y_3472_ = v_val_3483_;
goto v___jp_3463_;
}
}
v___jp_3484_:
{
lean_object* v_preInfo_x3f_3492_; 
v_preInfo_x3f_3492_ = lean_ctor_get(v___y_3488_, 1);
if (lean_obj_tag(v_preInfo_x3f_3492_) == 0)
{
lean_object* v_postInfo_x3f_3493_; 
v_postInfo_x3f_3493_ = lean_ctor_get(v___y_3488_, 2);
lean_inc(v_postInfo_x3f_3493_);
v___y_3474_ = v___y_3485_;
v___y_3475_ = v_edits_3491_;
v___y_3476_ = v___y_3486_;
v___y_3477_ = v___y_3487_;
v___y_3478_ = v___y_3489_;
v___y_3479_ = v___y_3488_;
v_postInfo_x3f_3480_ = v_postInfo_x3f_3493_;
v___y_3481_ = v___y_3490_;
v___y_3482_ = v___x_3373_;
goto v___jp_3473_;
}
else
{
lean_object* v_postInfo_x3f_3494_; lean_object* v_val_3495_; 
v_postInfo_x3f_3494_ = lean_ctor_get(v___y_3488_, 2);
lean_inc(v_postInfo_x3f_3494_);
v_val_3495_ = lean_ctor_get(v_preInfo_x3f_3492_, 0);
lean_inc(v_val_3495_);
v___y_3474_ = v___y_3485_;
v___y_3475_ = v_edits_3491_;
v___y_3476_ = v___y_3486_;
v___y_3477_ = v___y_3487_;
v___y_3478_ = v___y_3489_;
v___y_3479_ = v___y_3488_;
v_postInfo_x3f_3480_ = v_postInfo_x3f_3494_;
v___y_3481_ = v___y_3490_;
v___y_3482_ = v_val_3495_;
goto v___jp_3473_;
}
}
v___jp_3496_:
{
uint8_t v___x_3507_; 
v___x_3507_ = lean_nat_dec_lt(v___y_3499_, v_stop_3501_);
if (v___x_3507_ == 0)
{
lean_dec(v_stop_3501_);
lean_dec(v___y_3499_);
lean_dec_ref(v___y_3498_);
v___y_3485_ = v___y_3497_;
v___y_3486_ = v___y_3500_;
v___y_3487_ = v___y_3502_;
v___y_3488_ = v___y_3504_;
v___y_3489_ = v___y_3503_;
v___y_3490_ = v___y_3505_;
v_edits_3491_ = v_edits_3506_;
goto v___jp_3484_;
}
else
{
lean_object* v_source_3508_; lean_object* v___x_3510_; uint8_t v_isShared_3511_; uint8_t v_isSharedCheck_3519_; 
v_source_3508_ = lean_ctor_get(v___y_3498_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___y_3498_);
if (v_isSharedCheck_3519_ == 0)
{
lean_object* v_unused_3520_; 
v_unused_3520_ = lean_ctor_get(v___y_3498_, 1);
lean_dec(v_unused_3520_);
v___x_3510_ = v___y_3498_;
v_isShared_3511_ = v_isSharedCheck_3519_;
goto v_resetjp_3509_;
}
else
{
lean_inc(v_source_3508_);
lean_dec(v___y_3498_);
v___x_3510_ = lean_box(0);
v_isShared_3511_ = v_isSharedCheck_3519_;
goto v_resetjp_3509_;
}
v_resetjp_3509_:
{
uint8_t v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3516_; 
v___x_3512_ = 2;
v___x_3513_ = lean_string_utf8_extract(v_source_3508_, v___y_3499_, v_stop_3501_);
lean_dec(v_stop_3501_);
lean_dec(v___y_3499_);
lean_dec_ref(v_source_3508_);
v___x_3514_ = lean_box(v___x_3512_);
if (v_isShared_3511_ == 0)
{
lean_ctor_set(v___x_3510_, 1, v___x_3513_);
lean_ctor_set(v___x_3510_, 0, v___x_3514_);
v___x_3516_ = v___x_3510_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v___x_3514_);
lean_ctor_set(v_reuseFailAlloc_3518_, 1, v___x_3513_);
v___x_3516_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
lean_object* v___x_3517_; 
v___x_3517_ = lean_array_push(v_edits_3506_, v___x_3516_);
v___y_3485_ = v___y_3497_;
v___y_3486_ = v___y_3500_;
v___y_3487_ = v___y_3502_;
v___y_3488_ = v___y_3504_;
v___y_3489_ = v___y_3503_;
v___y_3490_ = v___y_3505_;
v_edits_3491_ = v___x_3517_;
goto v___jp_3484_;
}
}
}
}
v___jp_3521_:
{
if (lean_obj_tag(v___y_3529_) == 0)
{
lean_dec_ref(v___y_3532_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec(v___y_3522_);
v___y_3485_ = v___y_3523_;
v___y_3486_ = v___y_3526_;
v___y_3487_ = v___y_3527_;
v___y_3488_ = v___y_3528_;
v___y_3489_ = v___y_3529_;
v___y_3490_ = v___y_3530_;
v_edits_3491_ = v_edits_3531_;
goto v___jp_3484_;
}
else
{
lean_object* v_val_3533_; lean_object* v___x_3534_; 
v_val_3533_ = lean_ctor_get(v___y_3529_, 0);
v___x_3534_ = l_Lean_Syntax_getRange_x3f(v_val_3533_, v___y_3523_);
if (lean_obj_tag(v___x_3534_) == 1)
{
lean_object* v_val_3535_; uint8_t v___x_3536_; 
v_val_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_val_3535_);
lean_dec_ref(v___x_3534_);
v___x_3536_ = l_Lean_Syntax_Range_includes(v_val_3535_, v___y_3525_, v___y_3523_, v___y_3523_);
lean_dec_ref(v___y_3525_);
if (v___x_3536_ == 0)
{
lean_dec(v_val_3535_);
lean_dec_ref(v___y_3532_);
lean_dec(v___y_3524_);
lean_dec(v___y_3522_);
v___y_3485_ = v___y_3523_;
v___y_3486_ = v___y_3526_;
v___y_3487_ = v___y_3527_;
v___y_3488_ = v___y_3528_;
v___y_3489_ = v___y_3529_;
v___y_3490_ = v___y_3530_;
v_edits_3491_ = v_edits_3531_;
goto v___jp_3484_;
}
else
{
lean_object* v_fileMap_3537_; lean_object* v_start_3538_; lean_object* v_stop_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3555_; 
v_fileMap_3537_ = lean_ctor_get(v___y_3532_, 1);
lean_inc_ref(v_fileMap_3537_);
lean_dec_ref(v___y_3532_);
v_start_3538_ = lean_ctor_get(v_val_3535_, 0);
v_stop_3539_ = lean_ctor_get(v_val_3535_, 1);
v_isSharedCheck_3555_ = !lean_is_exclusive(v_val_3535_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3541_ = v_val_3535_;
v_isShared_3542_ = v_isSharedCheck_3555_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_stop_3539_);
lean_inc(v_start_3538_);
lean_dec(v_val_3535_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3555_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
uint8_t v___x_3543_; 
v___x_3543_ = lean_nat_dec_lt(v_start_3538_, v___y_3522_);
if (v___x_3543_ == 0)
{
lean_del_object(v___x_3541_);
lean_dec(v_start_3538_);
lean_dec(v___y_3522_);
v___y_3497_ = v___y_3523_;
v___y_3498_ = v_fileMap_3537_;
v___y_3499_ = v___y_3524_;
v___y_3500_ = v___y_3526_;
v_stop_3501_ = v_stop_3539_;
v___y_3502_ = v___y_3527_;
v___y_3503_ = v___y_3529_;
v___y_3504_ = v___y_3528_;
v___y_3505_ = v___y_3530_;
v_edits_3506_ = v_edits_3531_;
goto v___jp_3496_;
}
else
{
lean_object* v_source_3544_; uint8_t v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3549_; 
v_source_3544_ = lean_ctor_get(v_fileMap_3537_, 0);
v___x_3545_ = 2;
v___x_3546_ = lean_string_utf8_extract(v_source_3544_, v_start_3538_, v___y_3522_);
lean_dec(v___y_3522_);
lean_dec(v_start_3538_);
v___x_3547_ = lean_box(v___x_3545_);
if (v_isShared_3542_ == 0)
{
lean_ctor_set(v___x_3541_, 1, v___x_3546_);
lean_ctor_set(v___x_3541_, 0, v___x_3547_);
v___x_3549_ = v___x_3541_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v___x_3547_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v___x_3546_);
v___x_3549_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v___x_3550_ = lean_unsigned_to_nat(1u);
v___x_3551_ = lean_mk_empty_array_with_capacity(v___x_3550_);
v___x_3552_ = lean_array_push(v___x_3551_, v___x_3549_);
v___x_3553_ = l_Array_append___redArg(v___x_3552_, v_edits_3531_);
lean_dec_ref(v_edits_3531_);
v___y_3497_ = v___y_3523_;
v___y_3498_ = v_fileMap_3537_;
v___y_3499_ = v___y_3524_;
v___y_3500_ = v___y_3526_;
v_stop_3501_ = v_stop_3539_;
v___y_3502_ = v___y_3527_;
v___y_3503_ = v___y_3529_;
v___y_3504_ = v___y_3528_;
v___y_3505_ = v___y_3530_;
v_edits_3506_ = v___x_3553_;
goto v___jp_3496_;
}
}
}
}
}
else
{
lean_dec(v___x_3534_);
lean_dec_ref(v___y_3532_);
lean_dec_ref(v___y_3525_);
lean_dec(v___y_3524_);
lean_dec(v___y_3522_);
v___y_3485_ = v___y_3523_;
v___y_3486_ = v___y_3526_;
v___y_3487_ = v___y_3527_;
v___y_3488_ = v___y_3528_;
v___y_3489_ = v___y_3529_;
v___y_3490_ = v___y_3530_;
v_edits_3491_ = v_edits_3531_;
goto v___jp_3484_;
}
}
}
v___jp_3557_:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
lean_inc_ref(v___y_3565_);
v___x_3568_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3568_, 0, v___y_3562_);
lean_ctor_set(v___x_3568_, 1, v___y_3567_);
lean_ctor_set(v___x_3568_, 2, v___y_3565_);
v___x_3569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3556_);
lean_ctor_set(v___x_3569_, 1, v___x_3568_);
v___x_3570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3570_, 0, v___y_3558_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
v___x_3571_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3570_);
v___x_3572_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v___x_3571_, v___y_3321_, v___y_3322_);
if (lean_obj_tag(v___x_3572_) == 0)
{
lean_object* v_messageData_x3f_3573_; 
lean_dec_ref(v___x_3572_);
v_messageData_x3f_3573_ = lean_ctor_get(v___y_3565_, 4);
if (lean_obj_tag(v_messageData_x3f_3573_) == 1)
{
lean_object* v_start_3574_; lean_object* v_stop_3575_; lean_object* v_val_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; uint8_t v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; 
v_start_3574_ = lean_ctor_get(v___y_3560_, 0);
lean_inc(v_start_3574_);
v_stop_3575_ = lean_ctor_get(v___y_3560_, 1);
lean_inc(v_stop_3575_);
v_val_3576_ = lean_ctor_get(v_messageData_x3f_3573_, 0);
v___x_3577_ = lean_box(0);
lean_inc(v_val_3576_);
v___x_3578_ = l_Lean_MessageData_format(v_val_3576_, v___x_3577_);
v___x_3579_ = 0;
v___x_3580_ = l_Std_Format_defWidth;
v___x_3581_ = lean_unsigned_to_nat(0u);
v___x_3582_ = l_Std_Format_pretty(v___x_3578_, v___x_3580_, v___x_3581_, v___x_3581_);
v___x_3583_ = lean_box(v___x_3579_);
v___x_3584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3583_);
lean_ctor_set(v___x_3584_, 1, v___x_3582_);
v___x_3585_ = lean_unsigned_to_nat(1u);
v___x_3586_ = lean_mk_empty_array_with_capacity(v___x_3585_);
v___x_3587_ = lean_array_push(v___x_3586_, v___x_3584_);
lean_inc_ref(v___y_3321_);
v___y_3522_ = v_start_3574_;
v___y_3523_ = v___y_3559_;
v___y_3524_ = v_stop_3575_;
v___y_3525_ = v___y_3560_;
v___y_3526_ = v___y_3561_;
v___y_3527_ = v___y_3563_;
v___y_3528_ = v___y_3565_;
v___y_3529_ = v___y_3564_;
v___y_3530_ = v___y_3566_;
v_edits_3531_ = v___x_3587_;
v___y_3532_ = v___y_3321_;
goto v___jp_3521_;
}
else
{
lean_object* v_fileMap_3588_; lean_object* v_start_3589_; lean_object* v_stop_3590_; lean_object* v_source_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
v_fileMap_3588_ = lean_ctor_get(v___y_3321_, 1);
v_start_3589_ = lean_ctor_get(v___y_3560_, 0);
lean_inc(v_start_3589_);
v_stop_3590_ = lean_ctor_get(v___y_3560_, 1);
lean_inc(v_stop_3590_);
v_source_3591_ = lean_ctor_get(v_fileMap_3588_, 0);
v___x_3592_ = lean_string_utf8_extract(v_source_3591_, v_start_3589_, v_stop_3590_);
lean_inc_ref(v___y_3561_);
v___x_3593_ = l_Lean_Meta_Hint_readableDiff(v___x_3592_, v___y_3561_, v___y_3563_);
lean_inc_ref(v___y_3321_);
v___y_3522_ = v_start_3589_;
v___y_3523_ = v___y_3559_;
v___y_3524_ = v_stop_3590_;
v___y_3525_ = v___y_3560_;
v___y_3526_ = v___y_3561_;
v___y_3527_ = v___y_3563_;
v___y_3528_ = v___y_3565_;
v___y_3529_ = v___y_3564_;
v___y_3530_ = v___y_3566_;
v_edits_3531_ = v___x_3593_;
v___y_3532_ = v___y_3321_;
goto v___jp_3521_;
}
}
else
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
lean_dec_ref(v___y_3566_);
lean_dec_ref(v___y_3565_);
lean_dec(v___y_3564_);
lean_dec_ref(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec_ref(v_b_3320_);
lean_dec(v_ref_3316_);
lean_dec(v_codeActionPrefix_x3f_3315_);
v_a_3594_ = lean_ctor_get(v___x_3572_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3572_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3572_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3572_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
v___jp_3602_:
{
lean_object* v_toCodeActionTitle_x3f_3612_; lean_object* v___x_3613_; 
v_toCodeActionTitle_x3f_3612_ = lean_ctor_get(v___y_3609_, 5);
v___x_3613_ = l_Lean_Syntax_ofRange(v___y_3611_, v___x_3369_);
if (lean_obj_tag(v_toCodeActionTitle_x3f_3612_) == 0)
{
if (lean_obj_tag(v_codeActionPrefix_x3f_3315_) == 0)
{
lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3614_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__36));
v___x_3615_ = lean_string_append(v___x_3614_, v___y_3605_);
v___y_3558_ = v___x_3613_;
v___y_3559_ = v___y_3603_;
v___y_3560_ = v___y_3604_;
v___y_3561_ = v___y_3605_;
v___y_3562_ = v___y_3606_;
v___y_3563_ = v___y_3607_;
v___y_3564_ = v___y_3608_;
v___y_3565_ = v___y_3609_;
v___y_3566_ = v___y_3610_;
v___y_3567_ = v___x_3615_;
goto v___jp_3557_;
}
else
{
lean_object* v_val_3616_; lean_object* v___x_3617_; 
v_val_3616_ = lean_ctor_get(v_codeActionPrefix_x3f_3315_, 0);
lean_inc(v_val_3616_);
v___x_3617_ = lean_string_append(v_val_3616_, v___y_3605_);
v___y_3558_ = v___x_3613_;
v___y_3559_ = v___y_3603_;
v___y_3560_ = v___y_3604_;
v___y_3561_ = v___y_3605_;
v___y_3562_ = v___y_3606_;
v___y_3563_ = v___y_3607_;
v___y_3564_ = v___y_3608_;
v___y_3565_ = v___y_3609_;
v___y_3566_ = v___y_3610_;
v___y_3567_ = v___x_3617_;
goto v___jp_3557_;
}
}
else
{
lean_object* v_val_3618_; lean_object* v___x_3619_; 
v_val_3618_ = lean_ctor_get(v_toCodeActionTitle_x3f_3612_, 0);
lean_inc(v_val_3618_);
lean_inc_ref(v___y_3605_);
v___x_3619_ = lean_apply_1(v_val_3618_, v___y_3605_);
v___y_3558_ = v___x_3613_;
v___y_3559_ = v___y_3603_;
v___y_3560_ = v___y_3604_;
v___y_3561_ = v___y_3605_;
v___y_3562_ = v___y_3606_;
v___y_3563_ = v___y_3607_;
v___y_3564_ = v___y_3608_;
v___y_3565_ = v___y_3609_;
v___y_3566_ = v___y_3610_;
v___y_3567_ = v___x_3619_;
goto v___jp_3557_;
}
}
v___jp_3620_:
{
uint8_t v___x_3622_; lean_object* v___x_3623_; 
v___x_3622_ = 0;
v___x_3623_ = l_Lean_Syntax_getRange_x3f(v___y_3621_, v___x_3622_);
lean_dec(v___y_3621_);
if (lean_obj_tag(v___x_3623_) == 1)
{
lean_object* v_val_3624_; lean_object* v_toTryThisSuggestion_3625_; lean_object* v_previewSpan_x3f_3626_; uint8_t v_diffGranularity_3627_; lean_object* v___x_3628_; 
v_val_3624_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_val_3624_);
lean_dec_ref(v___x_3623_);
v_toTryThisSuggestion_3625_ = lean_ctor_get(v_a_3371_, 0);
v_previewSpan_x3f_3626_ = lean_ctor_get(v_a_3371_, 2);
v_diffGranularity_3627_ = lean_ctor_get_uint8(v_a_3371_, sizeof(void*)*3);
lean_inc(v___y_3322_);
lean_inc_ref(v___y_3321_);
lean_inc(v_val_3624_);
lean_inc_ref(v_toTryThisSuggestion_3625_);
v___x_3628_ = l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(v_toTryThisSuggestion_3625_, v_val_3624_, v___y_3321_, v___y_3322_);
if (lean_obj_tag(v___x_3628_) == 0)
{
lean_object* v_a_3629_; lean_object* v_range_3630_; lean_object* v_newText_3631_; lean_object* v___x_3632_; 
v_a_3629_ = lean_ctor_get(v___x_3628_, 0);
lean_inc(v_a_3629_);
lean_dec_ref(v___x_3628_);
v_range_3630_ = lean_ctor_get(v_a_3629_, 0);
lean_inc_ref(v_range_3630_);
v_newText_3631_ = lean_ctor_get(v_a_3629_, 1);
lean_inc_ref(v_newText_3631_);
v___x_3632_ = l_Lean_Syntax_getRange_x3f(v_ref_3316_, v___x_3622_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_inc_ref(v_toTryThisSuggestion_3625_);
lean_inc(v_previewSpan_x3f_3626_);
lean_inc(v_val_3624_);
v___y_3603_ = v___x_3622_;
v___y_3604_ = v_val_3624_;
v___y_3605_ = v_newText_3631_;
v___y_3606_ = v_a_3629_;
v___y_3607_ = v_diffGranularity_3627_;
v___y_3608_ = v_previewSpan_x3f_3626_;
v___y_3609_ = v_toTryThisSuggestion_3625_;
v___y_3610_ = v_range_3630_;
v___y_3611_ = v_val_3624_;
goto v___jp_3602_;
}
else
{
lean_object* v_val_3633_; 
v_val_3633_ = lean_ctor_get(v___x_3632_, 0);
lean_inc(v_val_3633_);
lean_dec_ref(v___x_3632_);
lean_inc_ref(v_toTryThisSuggestion_3625_);
lean_inc(v_previewSpan_x3f_3626_);
v___y_3603_ = v___x_3622_;
v___y_3604_ = v_val_3624_;
v___y_3605_ = v_newText_3631_;
v___y_3606_ = v_a_3629_;
v___y_3607_ = v_diffGranularity_3627_;
v___y_3608_ = v_previewSpan_x3f_3626_;
v___y_3609_ = v_toTryThisSuggestion_3625_;
v___y_3610_ = v_range_3630_;
v___y_3611_ = v_val_3633_;
goto v___jp_3602_;
}
}
else
{
lean_object* v_a_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3641_; 
lean_dec(v_val_3624_);
lean_dec(v___y_3322_);
lean_dec_ref(v___y_3321_);
lean_dec_ref(v_b_3320_);
lean_dec(v_ref_3316_);
lean_dec(v_codeActionPrefix_x3f_3315_);
v_a_3634_ = lean_ctor_get(v___x_3628_, 0);
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3628_);
if (v_isSharedCheck_3641_ == 0)
{
v___x_3636_ = v___x_3628_;
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_a_3634_);
lean_dec(v___x_3628_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3639_; 
if (v_isShared_3637_ == 0)
{
v___x_3639_ = v___x_3636_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_a_3634_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
}
}
else
{
lean_dec(v___x_3623_);
v_a_3325_ = v_b_3320_;
goto v___jp_3324_;
}
}
}
v___jp_3324_:
{
size_t v___x_3326_; size_t v___x_3327_; 
v___x_3326_ = ((size_t)1ULL);
v___x_3327_ = lean_usize_add(v_i_3319_, v___x_3326_);
v_i_3319_ = v___x_3327_;
v_b_3320_ = v_a_3325_;
goto _start;
}
v___jp_3329_:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3331_ = l_Lean_MessageData_nestD(v___y_3330_);
v___x_3332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3332_, 0, v_b_3320_);
lean_ctor_set(v___x_3332_, 1, v___x_3331_);
v_a_3325_ = v___x_3332_;
goto v___jp_3324_;
}
v___jp_3333_:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3337_, 0, v___y_3334_);
lean_ctor_set(v___x_3337_, 1, v___y_3336_);
v___x_3338_ = l_Lean_stringToMessageData(v___y_3335_);
v___x_3339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3337_);
lean_ctor_set(v___x_3339_, 1, v___x_3338_);
v___y_3330_ = v___x_3339_;
goto v___jp_3329_;
}
v___jp_3340_:
{
lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3342_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3343_ = lean_unsigned_to_nat(2u);
v___x_3344_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3);
v___x_3345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3344_);
lean_ctor_set(v___x_3345_, 1, v___y_3341_);
v___x_3346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3343_);
lean_ctor_set(v___x_3346_, 1, v___x_3345_);
v___x_3347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3342_);
lean_ctor_set(v___x_3347_, 1, v___x_3346_);
v___y_3330_ = v___x_3347_;
goto v___jp_3329_;
}
v___jp_3348_:
{
lean_object* v___x_3353_; uint64_t v_javascriptHash_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; uint8_t v___x_3366_; 
v___x_3353_ = l_Lean_Meta_Hint_tryThisDiffWidget;
v_javascriptHash_3354_ = lean_ctor_get_uint64(v___x_3353_, sizeof(void*)*1);
v___x_3355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8));
v___x_3356_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3356_, 0, v___x_3355_);
lean_ctor_set(v___x_3356_, 1, v___y_3351_);
lean_ctor_set_uint64(v___x_3356_, sizeof(void*)*2, v_javascriptHash_3354_);
v___x_3357_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3357_, 0, v___y_3352_);
v___x_3358_ = l_Lean_MessageData_ofFormat(v___x_3357_);
v___x_3359_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3356_);
lean_ctor_set(v___x_3359_, 1, v___x_3358_);
v___x_3360_ = l_Lean_stringToMessageData(v___y_3349_);
v___x_3361_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3360_);
lean_ctor_set(v___x_3361_, 1, v___x_3359_);
v___x_3362_ = l_Lean_stringToMessageData(v___y_3350_);
v___x_3363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3361_);
lean_ctor_set(v___x_3363_, 1, v___x_3362_);
v___x_3364_ = lean_array_get_size(v_suggestions_3313_);
v___x_3365_ = lean_unsigned_to_nat(1u);
v___x_3366_ = lean_nat_dec_eq(v___x_3364_, v___x_3365_);
if (v___x_3366_ == 0)
{
v___y_3341_ = v___x_3363_;
goto v___jp_3340_;
}
else
{
if (v_forceList_3314_ == 0)
{
if (v___x_3366_ == 0)
{
v___y_3341_ = v___x_3363_;
goto v___jp_3340_;
}
else
{
lean_object* v___x_3367_; lean_object* v___x_3368_; 
v___x_3367_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3367_);
lean_ctor_set(v___x_3368_, 1, v___x_3363_);
v___y_3330_ = v___x_3368_;
goto v___jp_3329_;
}
}
else
{
v___y_3341_ = v___x_3363_;
goto v___jp_3340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___boxed(lean_object* v_suggestions_3643_, lean_object* v_forceList_3644_, lean_object* v_codeActionPrefix_x3f_3645_, lean_object* v_ref_3646_, lean_object* v_as_3647_, lean_object* v_sz_3648_, lean_object* v_i_3649_, lean_object* v_b_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
uint8_t v_forceList_boxed_3654_; size_t v_sz_boxed_3655_; size_t v_i_boxed_3656_; lean_object* v_res_3657_; 
v_forceList_boxed_3654_ = lean_unbox(v_forceList_3644_);
v_sz_boxed_3655_ = lean_unbox_usize(v_sz_3648_);
lean_dec(v_sz_3648_);
v_i_boxed_3656_ = lean_unbox_usize(v_i_3649_);
lean_dec(v_i_3649_);
v_res_3657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3643_, v_forceList_boxed_3654_, v_codeActionPrefix_x3f_3645_, v_ref_3646_, v_as_3647_, v_sz_boxed_3655_, v_i_boxed_3656_, v_b_3650_, v___y_3651_, v___y_3652_);
lean_dec_ref(v_as_3647_);
lean_dec_ref(v_suggestions_3643_);
return v_res_3657_;
}
}
static lean_object* _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0(void){
_start:
{
lean_object* v___x_3658_; lean_object* v_msg_3659_; 
v___x_3658_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v_msg_3659_ = l_Lean_stringToMessageData(v___x_3658_);
return v_msg_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage(lean_object* v_suggestions_3660_, lean_object* v_ref_3661_, lean_object* v_codeActionPrefix_x3f_3662_, uint8_t v_forceList_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_){
_start:
{
lean_object* v_msg_3667_; size_t v_sz_3668_; size_t v___x_3669_; lean_object* v___x_3670_; 
v_msg_3667_ = lean_obj_once(&l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0, &l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0_once, _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0);
v_sz_3668_ = lean_array_size(v_suggestions_3660_);
v___x_3669_ = ((size_t)0ULL);
v___x_3670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3660_, v_forceList_3663_, v_codeActionPrefix_x3f_3662_, v_ref_3661_, v_suggestions_3660_, v_sz_3668_, v___x_3669_, v_msg_3667_, v_a_3664_, v_a_3665_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage___boxed(lean_object* v_suggestions_3671_, lean_object* v_ref_3672_, lean_object* v_codeActionPrefix_x3f_3673_, lean_object* v_forceList_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_){
_start:
{
uint8_t v_forceList_boxed_3678_; lean_object* v_res_3679_; 
v_forceList_boxed_3678_ = lean_unbox(v_forceList_3674_);
v_res_3679_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3671_, v_ref_3672_, v_codeActionPrefix_x3f_3673_, v_forceList_boxed_3678_, v_a_3675_, v_a_3676_);
lean_dec_ref(v_suggestions_3671_);
return v_res_3679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(lean_object* v_t_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_){
_start:
{
lean_object* v___x_3684_; 
v___x_3684_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3680_, v___y_3682_);
return v___x_3684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___boxed(lean_object* v_t_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
lean_object* v_res_3689_; 
v_res_3689_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(v_t_3685_, v___y_3686_, v___y_3687_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
return v_res_3689_;
}
}
static lean_object* _init_l_Lean_MessageData_hint___closed__3(void){
_start:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3694_ = ((lean_object*)(l_Lean_MessageData_hint___closed__2));
v___x_3695_ = l_Lean_stringToMessageData(v___x_3694_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint(lean_object* v_hint_3696_, lean_object* v_suggestions_3697_, lean_object* v_ref_x3f_3698_, lean_object* v_codeActionPrefix_x3f_3699_, uint8_t v_forceList_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_){
_start:
{
lean_object* v___y_3705_; 
if (lean_obj_tag(v_ref_x3f_3698_) == 0)
{
lean_object* v_ref_3720_; 
v_ref_3720_ = lean_ctor_get(v_a_3701_, 5);
lean_inc(v_ref_3720_);
v___y_3705_ = v_ref_3720_;
goto v___jp_3704_;
}
else
{
lean_object* v_val_3721_; 
v_val_3721_ = lean_ctor_get(v_ref_x3f_3698_, 0);
lean_inc(v_val_3721_);
lean_dec_ref(v_ref_x3f_3698_);
v___y_3705_ = v_val_3721_;
goto v___jp_3704_;
}
v___jp_3704_:
{
lean_object* v___x_3706_; 
v___x_3706_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3697_, v___y_3705_, v_codeActionPrefix_x3f_3699_, v_forceList_3700_, v_a_3701_, v_a_3702_);
if (lean_obj_tag(v___x_3706_) == 0)
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3719_; 
v_a_3707_ = lean_ctor_get(v___x_3706_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3709_ = v___x_3706_;
v_isShared_3710_ = v_isSharedCheck_3719_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v___x_3706_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3719_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3717_; 
v___x_3711_ = ((lean_object*)(l_Lean_MessageData_hint___closed__1));
v___x_3712_ = lean_obj_once(&l_Lean_MessageData_hint___closed__3, &l_Lean_MessageData_hint___closed__3_once, _init_l_Lean_MessageData_hint___closed__3);
v___x_3713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
lean_ctor_set(v___x_3713_, 1, v_hint_3696_);
v___x_3714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3713_);
lean_ctor_set(v___x_3714_, 1, v_a_3707_);
v___x_3715_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3711_);
lean_ctor_set(v___x_3715_, 1, v___x_3714_);
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 0, v___x_3715_);
v___x_3717_ = v___x_3709_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3715_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
else
{
lean_dec_ref(v_hint_3696_);
return v___x_3706_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint___boxed(lean_object* v_hint_3722_, lean_object* v_suggestions_3723_, lean_object* v_ref_x3f_3724_, lean_object* v_codeActionPrefix_x3f_3725_, lean_object* v_forceList_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_){
_start:
{
uint8_t v_forceList_boxed_3730_; lean_object* v_res_3731_; 
v_forceList_boxed_3730_ = lean_unbox(v_forceList_3726_);
v_res_3731_ = l_Lean_MessageData_hint(v_hint_3722_, v_suggestions_3723_, v_ref_x3f_3724_, v_codeActionPrefix_x3f_3725_, v_forceList_boxed_3730_, v_a_3727_, v_a_3728_);
lean_dec_ref(v_suggestions_3723_);
return v_res_3731_;
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
