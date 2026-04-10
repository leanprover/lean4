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
lean_dec_ref(v_leftIndex_782_);
lean_dec(v_rightIndex_783_);
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
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed__const__1(void){
_start:
{
uint32_t v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = 65;
v___x_1130_ = lean_box_uint32(v___x_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(lean_object* v_edited_1131_, lean_object* v___x_1132_, uint32_t v_a_1133_, lean_object* v_b_1134_){
_start:
{
lean_object* v_fst_1135_; lean_object* v_snd_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1163_; 
v_fst_1135_ = lean_ctor_get(v_b_1134_, 0);
v_snd_1136_ = lean_ctor_get(v_b_1134_, 1);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_b_1134_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1138_ = v_b_1134_;
v_isShared_1139_ = v_isSharedCheck_1163_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_snd_1136_);
lean_inc(v_fst_1135_);
lean_dec(v_b_1134_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1163_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
uint8_t v___y_1141_; uint8_t v___x_1157_; 
v___x_1157_ = lean_nat_dec_lt(v_snd_1136_, v___x_1132_);
if (v___x_1157_ == 0)
{
v___y_1141_ = v___x_1157_;
goto v___jp_1140_;
}
else
{
lean_object* v___x_1158_; lean_object* v___x_1159_; uint32_t v___x_1160_; uint8_t v___x_1161_; 
v___x_1158_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed__const__1;
v___x_1159_ = lean_array_get_borrowed(v___x_1158_, v_edited_1131_, v_snd_1136_);
v___x_1160_ = lean_unbox_uint32(v___x_1159_);
v___x_1161_ = lean_uint32_dec_eq(v___x_1160_, v_a_1133_);
if (v___x_1161_ == 0)
{
v___y_1141_ = v___x_1157_;
goto v___jp_1140_;
}
else
{
lean_object* v___x_1162_; 
lean_del_object(v___x_1138_);
v___x_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1162_, 0, v_fst_1135_);
lean_ctor_set(v___x_1162_, 1, v_snd_1136_);
return v___x_1162_;
}
}
v___jp_1140_:
{
if (v___y_1141_ == 0)
{
lean_object* v___x_1143_; 
if (v_isShared_1139_ == 0)
{
v___x_1143_ = v___x_1138_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_fst_1135_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_snd_1136_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
else
{
uint8_t v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1150_; 
v___x_1145_ = 0;
v___x_1146_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed__const__1;
v___x_1147_ = lean_array_get_borrowed(v___x_1146_, v_edited_1131_, v_snd_1136_);
v___x_1148_ = lean_box(v___x_1145_);
lean_inc(v___x_1147_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 1, v___x_1147_);
lean_ctor_set(v___x_1138_, 0, v___x_1148_);
v___x_1150_ = v___x_1138_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1148_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v___x_1147_);
v___x_1150_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1151_ = lean_array_push(v_fst_1135_, v___x_1150_);
v___x_1152_ = lean_unsigned_to_nat(1u);
v___x_1153_ = lean_nat_add(v_snd_1136_, v___x_1152_);
lean_dec(v_snd_1136_);
v___x_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1151_);
lean_ctor_set(v___x_1154_, 1, v___x_1153_);
v_b_1134_ = v___x_1154_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed(lean_object* v_edited_1164_, lean_object* v___x_1165_, lean_object* v_a_1166_, lean_object* v_b_1167_){
_start:
{
uint32_t v_a_boxed_1168_; lean_object* v_res_1169_; 
v_a_boxed_1168_ = lean_unbox_uint32(v_a_1166_);
lean_dec(v_a_1166_);
v_res_1169_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v_edited_1164_, v___x_1165_, v_a_boxed_1168_, v_b_1167_);
lean_dec(v___x_1165_);
lean_dec_ref(v_edited_1164_);
return v_res_1169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(lean_object* v_original_1170_, lean_object* v___x_1171_, uint32_t v_a_1172_, lean_object* v_b_1173_){
_start:
{
lean_object* v_fst_1174_; lean_object* v_snd_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1202_; 
v_fst_1174_ = lean_ctor_get(v_b_1173_, 0);
v_snd_1175_ = lean_ctor_get(v_b_1173_, 1);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_b_1173_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1177_ = v_b_1173_;
v_isShared_1178_ = v_isSharedCheck_1202_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_snd_1175_);
lean_inc(v_fst_1174_);
lean_dec(v_b_1173_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1202_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
uint8_t v___y_1180_; uint8_t v___x_1196_; 
v___x_1196_ = lean_nat_dec_lt(v_snd_1175_, v___x_1171_);
if (v___x_1196_ == 0)
{
v___y_1180_ = v___x_1196_;
goto v___jp_1179_;
}
else
{
lean_object* v___x_1197_; lean_object* v___x_1198_; uint32_t v___x_1199_; uint8_t v___x_1200_; 
v___x_1197_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed__const__1;
v___x_1198_ = lean_array_get_borrowed(v___x_1197_, v_original_1170_, v_snd_1175_);
v___x_1199_ = lean_unbox_uint32(v___x_1198_);
v___x_1200_ = lean_uint32_dec_eq(v___x_1199_, v_a_1172_);
if (v___x_1200_ == 0)
{
v___y_1180_ = v___x_1196_;
goto v___jp_1179_;
}
else
{
lean_object* v___x_1201_; 
lean_del_object(v___x_1177_);
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v_fst_1174_);
lean_ctor_set(v___x_1201_, 1, v_snd_1175_);
return v___x_1201_;
}
}
v___jp_1179_:
{
if (v___y_1180_ == 0)
{
lean_object* v___x_1182_; 
if (v_isShared_1178_ == 0)
{
v___x_1182_ = v___x_1177_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_fst_1174_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_snd_1175_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
else
{
uint8_t v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1189_; 
v___x_1184_ = 1;
v___x_1185_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed__const__1;
v___x_1186_ = lean_array_get_borrowed(v___x_1185_, v_original_1170_, v_snd_1175_);
v___x_1187_ = lean_box(v___x_1184_);
lean_inc(v___x_1186_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v___x_1186_);
lean_ctor_set(v___x_1177_, 0, v___x_1187_);
v___x_1189_ = v___x_1177_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1187_);
lean_ctor_set(v_reuseFailAlloc_1195_, 1, v___x_1186_);
v___x_1189_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1190_ = lean_array_push(v_fst_1174_, v___x_1189_);
v___x_1191_ = lean_unsigned_to_nat(1u);
v___x_1192_ = lean_nat_add(v_snd_1175_, v___x_1191_);
lean_dec(v_snd_1175_);
v___x_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1190_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v_b_1173_ = v___x_1193_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___boxed(lean_object* v_original_1203_, lean_object* v___x_1204_, lean_object* v_a_1205_, lean_object* v_b_1206_){
_start:
{
uint32_t v_a_boxed_1207_; lean_object* v_res_1208_; 
v_a_boxed_1207_ = lean_unbox_uint32(v_a_1205_);
lean_dec(v_a_1205_);
v_res_1208_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(v_original_1203_, v___x_1204_, v_a_boxed_1207_, v_b_1206_);
lean_dec(v___x_1204_);
lean_dec_ref(v_original_1203_);
return v_res_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(lean_object* v_original_1209_, lean_object* v___x_1210_, lean_object* v_edited_1211_, lean_object* v___x_1212_, lean_object* v_as_1213_, size_t v_sz_1214_, size_t v_i_1215_, lean_object* v_b_1216_){
_start:
{
uint8_t v___x_1217_; 
v___x_1217_ = lean_usize_dec_lt(v_i_1215_, v_sz_1214_);
if (v___x_1217_ == 0)
{
return v_b_1216_;
}
else
{
lean_object* v_snd_1218_; lean_object* v_fst_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1268_; 
v_snd_1218_ = lean_ctor_get(v_b_1216_, 1);
v_fst_1219_ = lean_ctor_get(v_b_1216_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_b_1216_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1221_ = v_b_1216_;
v_isShared_1222_ = v_isSharedCheck_1268_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_snd_1218_);
lean_inc(v_fst_1219_);
lean_dec(v_b_1216_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1268_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v_fst_1223_; lean_object* v_snd_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1267_; 
v_fst_1223_ = lean_ctor_get(v_snd_1218_, 0);
v_snd_1224_ = lean_ctor_get(v_snd_1218_, 1);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_snd_1218_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1226_ = v_snd_1218_;
v_isShared_1227_ = v_isSharedCheck_1267_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_snd_1224_);
lean_inc(v_fst_1223_);
lean_dec(v_snd_1218_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1267_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v_a_1228_; lean_object* v___x_1230_; 
v_a_1228_ = lean_array_uget_borrowed(v_as_1213_, v_i_1215_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 1, v_fst_1223_);
lean_ctor_set(v___x_1226_, 0, v_fst_1219_);
v___x_1230_ = v___x_1226_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_fst_1219_);
lean_ctor_set(v_reuseFailAlloc_1266_, 1, v_fst_1223_);
v___x_1230_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
uint32_t v___x_1231_; lean_object* v___x_1232_; lean_object* v_fst_1233_; lean_object* v_snd_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1265_; 
v___x_1231_ = lean_unbox_uint32(v_a_1228_);
v___x_1232_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(v_original_1209_, v___x_1210_, v___x_1231_, v___x_1230_);
v_fst_1233_ = lean_ctor_get(v___x_1232_, 0);
v_snd_1234_ = lean_ctor_get(v___x_1232_, 1);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1232_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1236_ = v___x_1232_;
v_isShared_1237_ = v_isSharedCheck_1265_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_snd_1234_);
lean_inc(v_fst_1233_);
lean_dec(v___x_1232_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1265_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 1, v_snd_1224_);
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_fst_1233_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_snd_1224_);
v___x_1239_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
uint32_t v___x_1240_; lean_object* v___x_1241_; lean_object* v_fst_1242_; lean_object* v_snd_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1263_; 
v___x_1240_ = lean_unbox_uint32(v_a_1228_);
v___x_1241_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v_edited_1211_, v___x_1212_, v___x_1240_, v___x_1239_);
v_fst_1242_ = lean_ctor_get(v___x_1241_, 0);
v_snd_1243_ = lean_ctor_get(v___x_1241_, 1);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1245_ = v___x_1241_;
v_isShared_1246_ = v_isSharedCheck_1263_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_snd_1243_);
lean_inc(v_fst_1242_);
lean_dec(v___x_1241_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1263_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
uint8_t v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1250_; 
v___x_1247_ = 2;
v___x_1248_ = lean_box(v___x_1247_);
lean_inc(v_a_1228_);
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v_a_1228_);
lean_ctor_set(v___x_1245_, 0, v___x_1248_);
v___x_1250_ = v___x_1245_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v_a_1228_);
v___x_1250_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1251_ = lean_array_push(v_fst_1242_, v___x_1250_);
v___x_1252_ = lean_unsigned_to_nat(1u);
v___x_1253_ = lean_nat_add(v_snd_1234_, v___x_1252_);
lean_dec(v_snd_1234_);
v___x_1254_ = lean_nat_add(v_snd_1243_, v___x_1252_);
lean_dec(v_snd_1243_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 1, v___x_1254_);
lean_ctor_set(v___x_1221_, 0, v___x_1253_);
v___x_1256_ = v___x_1221_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1253_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1257_; size_t v___x_1258_; size_t v___x_1259_; 
v___x_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1251_);
lean_ctor_set(v___x_1257_, 1, v___x_1256_);
v___x_1258_ = ((size_t)1ULL);
v___x_1259_ = lean_usize_add(v_i_1215_, v___x_1258_);
v_i_1215_ = v___x_1259_;
v_b_1216_ = v___x_1257_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15___boxed(lean_object* v_original_1269_, lean_object* v___x_1270_, lean_object* v_edited_1271_, lean_object* v___x_1272_, lean_object* v_as_1273_, lean_object* v_sz_1274_, lean_object* v_i_1275_, lean_object* v_b_1276_){
_start:
{
size_t v_sz_boxed_1277_; size_t v_i_boxed_1278_; lean_object* v_res_1279_; 
v_sz_boxed_1277_ = lean_unbox_usize(v_sz_1274_);
lean_dec(v_sz_1274_);
v_i_boxed_1278_ = lean_unbox_usize(v_i_1275_);
lean_dec(v_i_1275_);
v_res_1279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(v_original_1269_, v___x_1270_, v_edited_1271_, v___x_1272_, v_as_1273_, v_sz_boxed_1277_, v_i_boxed_1278_, v_b_1276_);
lean_dec_ref(v_as_1273_);
lean_dec(v___x_1272_);
lean_dec_ref(v_edited_1271_);
lean_dec(v___x_1270_);
lean_dec_ref(v_original_1269_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(lean_object* v_edited_1280_, lean_object* v___x_1281_, lean_object* v_original_1282_, lean_object* v___x_1283_, lean_object* v_as_1284_, size_t v_sz_1285_, size_t v_i_1286_, lean_object* v_b_1287_){
_start:
{
uint8_t v___x_1288_; 
v___x_1288_ = lean_usize_dec_lt(v_i_1286_, v_sz_1285_);
if (v___x_1288_ == 0)
{
return v_b_1287_;
}
else
{
lean_object* v_snd_1289_; lean_object* v_fst_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1339_; 
v_snd_1289_ = lean_ctor_get(v_b_1287_, 1);
v_fst_1290_ = lean_ctor_get(v_b_1287_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_b_1287_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1292_ = v_b_1287_;
v_isShared_1293_ = v_isSharedCheck_1339_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_snd_1289_);
lean_inc(v_fst_1290_);
lean_dec(v_b_1287_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1339_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v_fst_1294_; lean_object* v_snd_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1338_; 
v_fst_1294_ = lean_ctor_get(v_snd_1289_, 0);
v_snd_1295_ = lean_ctor_get(v_snd_1289_, 1);
v_isSharedCheck_1338_ = !lean_is_exclusive(v_snd_1289_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1297_ = v_snd_1289_;
v_isShared_1298_ = v_isSharedCheck_1338_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_snd_1295_);
lean_inc(v_fst_1294_);
lean_dec(v_snd_1289_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1338_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v_a_1299_; lean_object* v___x_1301_; 
v_a_1299_ = lean_array_uget_borrowed(v_as_1284_, v_i_1286_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 1, v_fst_1294_);
lean_ctor_set(v___x_1297_, 0, v_fst_1290_);
v___x_1301_ = v___x_1297_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_fst_1290_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v_fst_1294_);
v___x_1301_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
uint32_t v___x_1302_; lean_object* v___x_1303_; lean_object* v_fst_1304_; lean_object* v_snd_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1336_; 
v___x_1302_ = lean_unbox_uint32(v_a_1299_);
v___x_1303_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(v_original_1282_, v___x_1283_, v___x_1302_, v___x_1301_);
v_fst_1304_ = lean_ctor_get(v___x_1303_, 0);
v_snd_1305_ = lean_ctor_get(v___x_1303_, 1);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1307_ = v___x_1303_;
v_isShared_1308_ = v_isSharedCheck_1336_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_snd_1305_);
lean_inc(v_fst_1304_);
lean_dec(v___x_1303_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1336_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1310_; 
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 1, v_snd_1295_);
v___x_1310_ = v___x_1307_;
goto v_reusejp_1309_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_fst_1304_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_snd_1295_);
v___x_1310_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1309_;
}
v_reusejp_1309_:
{
uint32_t v___x_1311_; lean_object* v___x_1312_; lean_object* v_fst_1313_; lean_object* v_snd_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1334_; 
v___x_1311_ = lean_unbox_uint32(v_a_1299_);
v___x_1312_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v_edited_1280_, v___x_1281_, v___x_1311_, v___x_1310_);
v_fst_1313_ = lean_ctor_get(v___x_1312_, 0);
v_snd_1314_ = lean_ctor_get(v___x_1312_, 1);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1316_ = v___x_1312_;
v_isShared_1317_ = v_isSharedCheck_1334_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_snd_1314_);
lean_inc(v_fst_1313_);
lean_dec(v___x_1312_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1334_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
uint8_t v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1318_ = 2;
v___x_1319_ = lean_box(v___x_1318_);
lean_inc(v_a_1299_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 1, v_a_1299_);
lean_ctor_set(v___x_1316_, 0, v___x_1319_);
v___x_1321_ = v___x_1316_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1319_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v_a_1299_);
v___x_1321_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; 
v___x_1322_ = lean_array_push(v_fst_1313_, v___x_1321_);
v___x_1323_ = lean_unsigned_to_nat(1u);
v___x_1324_ = lean_nat_add(v_snd_1305_, v___x_1323_);
lean_dec(v_snd_1305_);
v___x_1325_ = lean_nat_add(v_snd_1314_, v___x_1323_);
lean_dec(v_snd_1314_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 1, v___x_1325_);
lean_ctor_set(v___x_1292_, 0, v___x_1324_);
v___x_1327_ = v___x_1292_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v___x_1325_);
v___x_1327_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1328_; size_t v___x_1329_; size_t v___x_1330_; lean_object* v___x_1331_; 
v___x_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1322_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___x_1329_ = ((size_t)1ULL);
v___x_1330_ = lean_usize_add(v_i_1286_, v___x_1329_);
v___x_1331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(v_original_1282_, v___x_1283_, v_edited_1280_, v___x_1281_, v_as_1284_, v_sz_1285_, v___x_1330_, v___x_1328_);
return v___x_1331_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5___boxed(lean_object* v_edited_1340_, lean_object* v___x_1341_, lean_object* v_original_1342_, lean_object* v___x_1343_, lean_object* v_as_1344_, lean_object* v_sz_1345_, lean_object* v_i_1346_, lean_object* v_b_1347_){
_start:
{
size_t v_sz_boxed_1348_; size_t v_i_boxed_1349_; lean_object* v_res_1350_; 
v_sz_boxed_1348_ = lean_unbox_usize(v_sz_1345_);
lean_dec(v_sz_1345_);
v_i_boxed_1349_ = lean_unbox_usize(v_i_1346_);
lean_dec(v_i_1346_);
v_res_1350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v_edited_1340_, v___x_1341_, v_original_1342_, v___x_1343_, v_as_1344_, v_sz_boxed_1348_, v_i_boxed_1349_, v_b_1347_);
lean_dec_ref(v_as_1344_);
lean_dec(v___x_1343_);
lean_dec_ref(v_original_1342_);
lean_dec(v___x_1341_);
lean_dec_ref(v_edited_1340_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(lean_object* v_original_1358_, lean_object* v_edited_1359_){
_start:
{
lean_object* v_i_1360_; lean_object* v___x_1361_; uint8_t v___x_1362_; 
v_i_1360_ = lean_unsigned_to_nat(0u);
v___x_1361_ = lean_array_get_size(v_original_1358_);
v___x_1362_ = lean_nat_dec_lt(v_i_1360_, v___x_1361_);
if (v___x_1362_ == 0)
{
size_t v_sz_1363_; size_t v___x_1364_; lean_object* v___x_1365_; 
lean_dec_ref(v_original_1358_);
v_sz_1363_ = lean_array_size(v_edited_1359_);
v___x_1364_ = ((size_t)0ULL);
v___x_1365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(v_sz_1363_, v___x_1364_, v_edited_1359_);
return v___x_1365_;
}
else
{
lean_object* v___x_1366_; uint8_t v___x_1367_; 
v___x_1366_ = lean_array_get_size(v_edited_1359_);
v___x_1367_ = lean_nat_dec_lt(v_i_1360_, v___x_1366_);
if (v___x_1367_ == 0)
{
size_t v_sz_1368_; size_t v___x_1369_; lean_object* v___x_1370_; 
lean_dec_ref(v_edited_1359_);
v_sz_1368_ = lean_array_size(v_original_1358_);
v___x_1369_ = ((size_t)0ULL);
v___x_1370_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(v_sz_1368_, v___x_1369_, v_original_1358_);
return v___x_1370_;
}
else
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v_ds_1373_; lean_object* v___x_1374_; size_t v_sz_1375_; size_t v___x_1376_; lean_object* v___x_1377_; lean_object* v_snd_1378_; lean_object* v_fst_1379_; lean_object* v_fst_1380_; lean_object* v_snd_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1400_; 
lean_inc_ref(v_original_1358_);
v___x_1371_ = l_Array_toSubarray___redArg(v_original_1358_, v_i_1360_, v___x_1361_);
lean_inc_ref(v_edited_1359_);
v___x_1372_ = l_Array_toSubarray___redArg(v_edited_1359_, v_i_1360_, v___x_1366_);
v_ds_1373_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v___x_1371_, v___x_1372_);
v___x_1374_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__2));
v_sz_1375_ = lean_array_size(v_ds_1373_);
v___x_1376_ = ((size_t)0ULL);
v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v_edited_1359_, v___x_1366_, v_original_1358_, v___x_1361_, v_ds_1373_, v_sz_1375_, v___x_1376_, v___x_1374_);
lean_dec_ref(v_ds_1373_);
v_snd_1378_ = lean_ctor_get(v___x_1377_, 1);
lean_inc(v_snd_1378_);
v_fst_1379_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_fst_1379_);
lean_dec_ref(v___x_1377_);
v_fst_1380_ = lean_ctor_get(v_snd_1378_, 0);
v_snd_1381_ = lean_ctor_get(v_snd_1378_, 1);
v_isSharedCheck_1400_ = !lean_is_exclusive(v_snd_1378_);
if (v_isSharedCheck_1400_ == 0)
{
v___x_1383_ = v_snd_1378_;
v_isShared_1384_ = v_isSharedCheck_1400_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_snd_1381_);
lean_inc(v_fst_1380_);
lean_dec(v_snd_1378_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1400_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 1, v_fst_1380_);
lean_ctor_set(v___x_1383_, 0, v_fst_1379_);
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v_fst_1379_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_fst_1380_);
v___x_1386_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
lean_object* v___x_1387_; lean_object* v_fst_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1397_; 
v___x_1387_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(v___x_1361_, v_original_1358_, v___x_1386_);
lean_dec_ref(v_original_1358_);
v_fst_1388_ = lean_ctor_get(v___x_1387_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1387_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; 
v_unused_1398_ = lean_ctor_get(v___x_1387_, 1);
lean_dec(v_unused_1398_);
v___x_1390_ = v___x_1387_;
v_isShared_1391_ = v_isSharedCheck_1397_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_fst_1388_);
lean_dec(v___x_1387_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1397_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
lean_ctor_set(v___x_1390_, 1, v_snd_1381_);
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_fst_1388_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_snd_1381_);
v___x_1393_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v___x_1394_; lean_object* v_fst_1395_; 
v___x_1394_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(v___x_1366_, v_edited_1359_, v___x_1393_);
lean_dec_ref(v_edited_1359_);
v_fst_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_fst_1395_);
lean_dec_ref(v___x_1394_);
return v_fst_1395_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(lean_object* v_s_1401_, lean_object* v_a_1402_, uint8_t v_b_1403_){
_start:
{
lean_object* v_str_1404_; lean_object* v_startInclusive_1405_; lean_object* v_endExclusive_1406_; lean_object* v___x_1407_; uint8_t v___x_1408_; 
v_str_1404_ = lean_ctor_get(v_s_1401_, 0);
v_startInclusive_1405_ = lean_ctor_get(v_s_1401_, 1);
v_endExclusive_1406_ = lean_ctor_get(v_s_1401_, 2);
v___x_1407_ = lean_nat_sub(v_endExclusive_1406_, v_startInclusive_1405_);
v___x_1408_ = lean_nat_dec_eq(v_a_1402_, v___x_1407_);
lean_dec(v___x_1407_);
if (v___x_1408_ == 0)
{
lean_object* v___x_1409_; uint32_t v___x_1410_; uint32_t v___x_1411_; uint8_t v___x_1412_; 
v___x_1409_ = lean_nat_add(v_startInclusive_1405_, v_a_1402_);
lean_dec(v_a_1402_);
v___x_1410_ = lean_string_utf8_get_fast(v_str_1404_, v___x_1409_);
v___x_1411_ = 10;
v___x_1412_ = lean_uint32_dec_eq(v___x_1410_, v___x_1411_);
if (v___x_1412_ == 0)
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = lean_string_utf8_next_fast(v_str_1404_, v___x_1409_);
lean_dec(v___x_1409_);
v___x_1414_ = lean_nat_sub(v___x_1413_, v_startInclusive_1405_);
v_a_1402_ = v___x_1414_;
v_b_1403_ = v___x_1412_;
goto _start;
}
else
{
lean_dec(v___x_1409_);
return v___x_1412_;
}
}
else
{
lean_dec(v_a_1402_);
return v_b_1403_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg___boxed(lean_object* v_s_1416_, lean_object* v_a_1417_, lean_object* v_b_1418_){
_start:
{
uint8_t v_b_boxed_1419_; uint8_t v_res_1420_; lean_object* v_r_1421_; 
v_b_boxed_1419_ = lean_unbox(v_b_1418_);
v_res_1420_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1416_, v_a_1417_, v_b_boxed_1419_);
lean_dec_ref(v_s_1416_);
v_r_1421_ = lean_box(v_res_1420_);
return v_r_1421_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(lean_object* v_s_1422_){
_start:
{
lean_object* v_searcher_1423_; uint8_t v___x_1424_; uint8_t v___x_1425_; 
v_searcher_1423_ = lean_unsigned_to_nat(0u);
v___x_1424_ = 0;
v___x_1425_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1422_, v_searcher_1423_, v___x_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0___boxed(lean_object* v_s_1426_){
_start:
{
uint8_t v_res_1427_; lean_object* v_r_1428_; 
v_res_1427_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v_s_1426_);
lean_dec_ref(v_s_1426_);
v_r_1428_ = lean_box(v_res_1427_);
return v_r_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(lean_object* v_oldWs_1429_, lean_object* v_newWs_1430_){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; uint8_t v___x_1434_; 
v___x_1431_ = lean_unsigned_to_nat(0u);
v___x_1432_ = lean_string_utf8_byte_size(v_oldWs_1429_);
lean_inc_ref(v_oldWs_1429_);
v___x_1433_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1433_, 0, v_oldWs_1429_);
lean_ctor_set(v___x_1433_, 1, v___x_1431_);
lean_ctor_set(v___x_1433_, 2, v___x_1432_);
v___x_1434_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_1433_);
lean_dec_ref(v___x_1433_);
if (v___x_1434_ == 0)
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1435_ = lean_string_data(v_oldWs_1429_);
v___x_1436_ = lean_array_mk(v___x_1435_);
v___x_1437_ = lean_string_data(v_newWs_1430_);
v___x_1438_ = lean_array_mk(v___x_1437_);
v___x_1439_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_1436_, v___x_1438_);
v___x_1440_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_1439_);
lean_dec_ref(v___x_1439_);
return v___x_1440_;
}
else
{
uint8_t v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_dec_ref(v_oldWs_1429_);
v___x_1441_ = 2;
v___x_1442_ = lean_box(v___x_1441_);
v___x_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
lean_ctor_set(v___x_1443_, 1, v_newWs_1430_);
v___x_1444_ = lean_unsigned_to_nat(1u);
v___x_1445_ = lean_mk_empty_array_with_capacity(v___x_1444_);
v___x_1446_ = lean_array_push(v___x_1445_, v___x_1443_);
return v___x_1446_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(lean_object* v_s_1447_, lean_object* v_inst_1448_, lean_object* v_R_1449_, lean_object* v_a_1450_, uint8_t v_b_1451_, lean_object* v_c_1452_){
_start:
{
uint8_t v___x_1453_; 
v___x_1453_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1447_, v_a_1450_, v_b_1451_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___boxed(lean_object* v_s_1454_, lean_object* v_inst_1455_, lean_object* v_R_1456_, lean_object* v_a_1457_, lean_object* v_b_1458_, lean_object* v_c_1459_){
_start:
{
uint8_t v_b_boxed_1460_; uint8_t v_res_1461_; lean_object* v_r_1462_; 
v_b_boxed_1460_ = lean_unbox(v_b_1458_);
v_res_1461_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(v_s_1454_, v_inst_1455_, v_R_1456_, v_a_1457_, v_b_boxed_1460_, v_c_1459_);
lean_dec_ref(v_s_1454_);
v_r_1462_ = lean_box(v_res_1461_);
return v_r_1462_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5(lean_object* v_as_1463_, lean_object* v_as_x27_1464_, lean_object* v_b_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg(v_as_x27_1464_, v_b_1465_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___boxed(lean_object* v_as_1468_, lean_object* v_as_x27_1469_, lean_object* v_b_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5(v_as_1468_, v_as_x27_1469_, v_b_1470_, v_a_1471_);
lean_dec(v_as_1468_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8(lean_object* v_lsize_1473_, lean_object* v_rsize_1474_, lean_object* v_histogram_1475_, lean_object* v_index_1476_, uint32_t v_val_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(v_histogram_1475_, v_index_1476_, v_val_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___boxed(lean_object* v_lsize_1479_, lean_object* v_rsize_1480_, lean_object* v_histogram_1481_, lean_object* v_index_1482_, lean_object* v_val_1483_){
_start:
{
uint32_t v_val_boxed_1484_; lean_object* v_res_1485_; 
v_val_boxed_1484_ = lean_unbox_uint32(v_val_1483_);
lean_dec(v_val_1483_);
v_res_1485_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8(v_lsize_1479_, v_rsize_1480_, v_histogram_1481_, v_index_1482_, v_val_boxed_1484_);
lean_dec(v_rsize_1480_);
lean_dec(v_lsize_1479_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9(lean_object* v_upperBound_1486_, lean_object* v___x_1487_, lean_object* v_fst_1488_, lean_object* v___x_1489_, lean_object* v_inst_1490_, lean_object* v_R_1491_, lean_object* v_a_1492_, lean_object* v_b_1493_, lean_object* v_c_1494_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(v_upperBound_1486_, v___x_1487_, v_fst_1488_, v___x_1489_, v_a_1492_, v_b_1493_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___boxed(lean_object* v_upperBound_1496_, lean_object* v___x_1497_, lean_object* v_fst_1498_, lean_object* v___x_1499_, lean_object* v_inst_1500_, lean_object* v_R_1501_, lean_object* v_a_1502_, lean_object* v_b_1503_, lean_object* v_c_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9(v_upperBound_1496_, v___x_1497_, v_fst_1498_, v___x_1499_, v_inst_1500_, v_R_1501_, v_a_1502_, v_b_1503_, v_c_1504_);
lean_dec(v___x_1499_);
lean_dec_ref(v_fst_1498_);
lean_dec(v___x_1497_);
lean_dec(v_upperBound_1496_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10(lean_object* v_lsize_1506_, lean_object* v_rsize_1507_, lean_object* v_histogram_1508_, lean_object* v_index_1509_, uint32_t v_val_1510_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(v_histogram_1508_, v_index_1509_, v_val_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___boxed(lean_object* v_lsize_1512_, lean_object* v_rsize_1513_, lean_object* v_histogram_1514_, lean_object* v_index_1515_, lean_object* v_val_1516_){
_start:
{
uint32_t v_val_boxed_1517_; lean_object* v_res_1518_; 
v_val_boxed_1517_ = lean_unbox_uint32(v_val_1516_);
lean_dec(v_val_1516_);
v_res_1518_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10(v_lsize_1512_, v_rsize_1513_, v_histogram_1514_, v_index_1515_, v_val_boxed_1517_);
lean_dec(v_rsize_1513_);
lean_dec(v_lsize_1512_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11(lean_object* v_upperBound_1519_, lean_object* v_fst_1520_, lean_object* v___x_1521_, lean_object* v_fst_1522_, lean_object* v_inst_1523_, lean_object* v_R_1524_, lean_object* v_a_1525_, lean_object* v_b_1526_, lean_object* v_c_1527_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg(v_upperBound_1519_, v_fst_1520_, v___x_1521_, v_fst_1522_, v_a_1525_, v_b_1526_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___boxed(lean_object* v_upperBound_1529_, lean_object* v_fst_1530_, lean_object* v___x_1531_, lean_object* v_fst_1532_, lean_object* v_inst_1533_, lean_object* v_R_1534_, lean_object* v_a_1535_, lean_object* v_b_1536_, lean_object* v_c_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11(v_upperBound_1529_, v_fst_1530_, v___x_1531_, v_fst_1532_, v_inst_1533_, v_R_1534_, v_a_1535_, v_b_1536_, v_c_1537_);
lean_dec_ref(v_fst_1532_);
lean_dec(v___x_1531_);
lean_dec_ref(v_fst_1530_);
lean_dec(v_upperBound_1529_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11(lean_object* v_00_u03b2_1539_, lean_object* v_m_1540_, uint32_t v_a_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(v_m_1540_, v_a_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___boxed(lean_object* v_00_u03b2_1543_, lean_object* v_m_1544_, lean_object* v_a_1545_){
_start:
{
uint32_t v_a_boxed_1546_; lean_object* v_res_1547_; 
v_a_boxed_1546_ = lean_unbox_uint32(v_a_1545_);
lean_dec(v_a_1545_);
v_res_1547_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11(v_00_u03b2_1543_, v_m_1544_, v_a_boxed_1546_);
lean_dec_ref(v_m_1544_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12(lean_object* v_00_u03b2_1548_, lean_object* v_m_1549_, uint32_t v_a_1550_, lean_object* v_b_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_m_1549_, v_a_1550_, v_b_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___boxed(lean_object* v_00_u03b2_1553_, lean_object* v_m_1554_, lean_object* v_a_1555_, lean_object* v_b_1556_){
_start:
{
uint32_t v_a_boxed_1557_; lean_object* v_res_1558_; 
v_a_boxed_1557_ = lean_unbox_uint32(v_a_1555_);
lean_dec(v_a_1555_);
v_res_1558_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12(v_00_u03b2_1553_, v_m_1554_, v_a_boxed_1557_, v_b_1556_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14(lean_object* v_inst_1559_, lean_object* v_R_1560_, lean_object* v_a_1561_, lean_object* v_b_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(v_a_1561_, v_b_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20(lean_object* v_00_u03b2_1564_, uint32_t v_a_1565_, lean_object* v_x_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg(v_a_1565_, v_x_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___boxed(lean_object* v_00_u03b2_1568_, lean_object* v_a_1569_, lean_object* v_x_1570_){
_start:
{
uint32_t v_a_boxed_1571_; lean_object* v_res_1572_; 
v_a_boxed_1571_ = lean_unbox_uint32(v_a_1569_);
lean_dec(v_a_1569_);
v_res_1572_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20(v_00_u03b2_1568_, v_a_boxed_1571_, v_x_1570_);
lean_dec(v_x_1570_);
return v_res_1572_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22(lean_object* v_00_u03b2_1573_, uint32_t v_a_1574_, lean_object* v_x_1575_){
_start:
{
uint8_t v___x_1576_; 
v___x_1576_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg(v_a_1574_, v_x_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___boxed(lean_object* v_00_u03b2_1577_, lean_object* v_a_1578_, lean_object* v_x_1579_){
_start:
{
uint32_t v_a_boxed_1580_; uint8_t v_res_1581_; lean_object* v_r_1582_; 
v_a_boxed_1580_ = lean_unbox_uint32(v_a_1578_);
lean_dec(v_a_1578_);
v_res_1581_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22(v_00_u03b2_1577_, v_a_boxed_1580_, v_x_1579_);
lean_dec(v_x_1579_);
v_r_1582_ = lean_box(v_res_1581_);
return v_r_1582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23(lean_object* v_00_u03b2_1583_, lean_object* v_data_1584_){
_start:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23___redArg(v_data_1584_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24(lean_object* v_00_u03b2_1586_, uint32_t v_a_1587_, lean_object* v_b_1588_, lean_object* v_x_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(v_a_1587_, v_b_1588_, v_x_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___boxed(lean_object* v_00_u03b2_1591_, lean_object* v_a_1592_, lean_object* v_b_1593_, lean_object* v_x_1594_){
_start:
{
uint32_t v_a_boxed_1595_; lean_object* v_res_1596_; 
v_a_boxed_1595_ = lean_unbox_uint32(v_a_1592_);
lean_dec(v_a_1592_);
v_res_1596_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24(v_00_u03b2_1591_, v_a_boxed_1595_, v_b_1593_, v_x_1594_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28(lean_object* v_00_u03b2_1597_, lean_object* v_i_1598_, lean_object* v_source_1599_, lean_object* v_target_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28___redArg(v_i_1598_, v_source_1599_, v_target_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_1602_, lean_object* v_x_1603_, lean_object* v_x_1604_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29___redArg(v_x_1603_, v_x_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(lean_object* v_s_1606_, lean_object* v_stopPos_1607_, lean_object* v_i_1608_){
_start:
{
uint8_t v___y_1613_; uint8_t v___x_1614_; 
v___x_1614_ = lean_nat_dec_lt(v_i_1608_, v_stopPos_1607_);
if (v___x_1614_ == 0)
{
return v_i_1608_;
}
else
{
uint32_t v___x_1615_; uint8_t v___y_1617_; uint32_t v___x_1622_; uint8_t v___x_1623_; 
v___x_1615_ = lean_string_utf8_get(v_s_1606_, v_i_1608_);
v___x_1622_ = 32;
v___x_1623_ = lean_uint32_dec_eq(v___x_1615_, v___x_1622_);
if (v___x_1623_ == 0)
{
uint32_t v___x_1624_; uint8_t v___x_1625_; 
v___x_1624_ = 9;
v___x_1625_ = lean_uint32_dec_eq(v___x_1615_, v___x_1624_);
v___y_1617_ = v___x_1625_;
goto v___jp_1616_;
}
else
{
v___y_1617_ = v___x_1623_;
goto v___jp_1616_;
}
v___jp_1616_:
{
if (v___y_1617_ == 0)
{
uint32_t v___x_1618_; uint8_t v___x_1619_; 
v___x_1618_ = 13;
v___x_1619_ = lean_uint32_dec_eq(v___x_1615_, v___x_1618_);
if (v___x_1619_ == 0)
{
uint32_t v___x_1620_; uint8_t v___x_1621_; 
v___x_1620_ = 10;
v___x_1621_ = lean_uint32_dec_eq(v___x_1615_, v___x_1620_);
v___y_1613_ = v___x_1621_;
goto v___jp_1612_;
}
else
{
v___y_1613_ = v___x_1619_;
goto v___jp_1612_;
}
}
else
{
goto v___jp_1609_;
}
}
}
v___jp_1609_:
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_string_utf8_next(v_s_1606_, v_i_1608_);
lean_dec(v_i_1608_);
v_i_1608_ = v___x_1610_;
goto _start;
}
v___jp_1612_:
{
if (v___y_1613_ == 0)
{
return v_i_1608_;
}
else
{
goto v___jp_1609_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0___boxed(lean_object* v_s_1626_, lean_object* v_stopPos_1627_, lean_object* v_i_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1626_, v_stopPos_1627_, v_i_1628_);
lean_dec(v_stopPos_1627_);
lean_dec_ref(v_s_1626_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(lean_object* v_s_1630_, lean_object* v_b_1631_, lean_object* v_i_1632_, lean_object* v_r_1633_, lean_object* v_ws_1634_){
_start:
{
uint8_t v___y_1644_; uint8_t v___x_1647_; 
v___x_1647_ = lean_string_utf8_at_end(v_s_1630_, v_i_1632_);
if (v___x_1647_ == 0)
{
uint32_t v___x_1648_; uint8_t v___y_1650_; uint32_t v___x_1655_; uint8_t v___x_1656_; 
v___x_1648_ = lean_string_utf8_get(v_s_1630_, v_i_1632_);
v___x_1655_ = 32;
v___x_1656_ = lean_uint32_dec_eq(v___x_1648_, v___x_1655_);
if (v___x_1656_ == 0)
{
uint32_t v___x_1657_; uint8_t v___x_1658_; 
v___x_1657_ = 9;
v___x_1658_ = lean_uint32_dec_eq(v___x_1648_, v___x_1657_);
v___y_1650_ = v___x_1658_;
goto v___jp_1649_;
}
else
{
v___y_1650_ = v___x_1656_;
goto v___jp_1649_;
}
v___jp_1649_:
{
if (v___y_1650_ == 0)
{
uint32_t v___x_1651_; uint8_t v___x_1652_; 
v___x_1651_ = 13;
v___x_1652_ = lean_uint32_dec_eq(v___x_1648_, v___x_1651_);
if (v___x_1652_ == 0)
{
uint32_t v___x_1653_; uint8_t v___x_1654_; 
v___x_1653_ = 10;
v___x_1654_ = lean_uint32_dec_eq(v___x_1648_, v___x_1653_);
v___y_1644_ = v___x_1654_;
goto v___jp_1643_;
}
else
{
v___y_1644_ = v___x_1652_;
goto v___jp_1643_;
}
}
else
{
goto v___jp_1635_;
}
}
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = lean_string_utf8_extract(v_s_1630_, v_b_1631_, v_i_1632_);
lean_dec(v_i_1632_);
lean_dec(v_b_1631_);
v___x_1660_ = lean_array_push(v_r_1633_, v___x_1659_);
v___x_1661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
lean_ctor_set(v___x_1661_, 1, v_ws_1634_);
return v___x_1661_;
}
v___jp_1635_:
{
lean_object* v___x_1636_; lean_object* v_e_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1636_ = lean_string_utf8_byte_size(v_s_1630_);
lean_inc(v_i_1632_);
v_e_1637_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1630_, v___x_1636_, v_i_1632_);
v___x_1638_ = lean_string_utf8_extract(v_s_1630_, v_b_1631_, v_i_1632_);
lean_dec(v_b_1631_);
v___x_1639_ = lean_array_push(v_r_1633_, v___x_1638_);
v___x_1640_ = lean_string_utf8_extract(v_s_1630_, v_i_1632_, v_e_1637_);
lean_dec(v_i_1632_);
v___x_1641_ = lean_array_push(v_ws_1634_, v___x_1640_);
lean_inc(v_e_1637_);
v_b_1631_ = v_e_1637_;
v_i_1632_ = v_e_1637_;
v_r_1633_ = v___x_1639_;
v_ws_1634_ = v___x_1641_;
goto _start;
}
v___jp_1643_:
{
if (v___y_1644_ == 0)
{
lean_object* v___x_1645_; 
v___x_1645_ = lean_string_utf8_next(v_s_1630_, v_i_1632_);
lean_dec(v_i_1632_);
v_i_1632_ = v___x_1645_;
goto _start;
}
else
{
goto v___jp_1635_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux___boxed(lean_object* v_s_1662_, lean_object* v_b_1663_, lean_object* v_i_1664_, lean_object* v_r_1665_, lean_object* v_ws_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1662_, v_b_1663_, v_i_1664_, v_r_1665_, v_ws_1666_);
lean_dec_ref(v_s_1662_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(lean_object* v_s_1670_){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v___x_1671_ = lean_unsigned_to_nat(0u);
v___x_1672_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_1673_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1670_, v___x_1671_, v___x_1671_, v___x_1672_, v___x_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___boxed(lean_object* v_s_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_1674_);
lean_dec_ref(v_s_1674_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(size_t v_sz_1676_, size_t v_i_1677_, lean_object* v_bs_1678_){
_start:
{
uint8_t v___x_1679_; 
v___x_1679_ = lean_usize_dec_lt(v_i_1677_, v_sz_1676_);
if (v___x_1679_ == 0)
{
return v_bs_1678_;
}
else
{
lean_object* v_v_1680_; lean_object* v_fst_1681_; lean_object* v_snd_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1716_; 
v_v_1680_ = lean_array_uget(v_bs_1678_, v_i_1677_);
v_fst_1681_ = lean_ctor_get(v_v_1680_, 0);
v_snd_1682_ = lean_ctor_get(v_v_1680_, 1);
v_isSharedCheck_1716_ = !lean_is_exclusive(v_v_1680_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1684_ = v_v_1680_;
v_isShared_1685_ = v_isSharedCheck_1716_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_snd_1682_);
lean_inc(v_fst_1681_);
lean_dec(v_v_1680_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1716_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1686_; lean_object* v_bs_x27_1687_; lean_object* v___y_1689_; lean_object* v___x_1694_; lean_object* v___x_1695_; uint8_t v___x_1696_; 
v___x_1686_ = lean_unsigned_to_nat(0u);
v_bs_x27_1687_ = lean_array_uset(v_bs_1678_, v_i_1677_, v___x_1686_);
v___x_1694_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_1695_ = lean_array_get_size(v_snd_1682_);
v___x_1696_ = lean_nat_dec_lt(v___x_1686_, v___x_1695_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1698_; 
lean_dec(v_snd_1682_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 1, v___x_1694_);
v___x_1698_ = v___x_1684_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_fst_1681_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v___x_1694_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
v___y_1689_ = v___x_1698_;
goto v___jp_1688_;
}
}
else
{
uint8_t v___x_1700_; 
v___x_1700_ = lean_nat_dec_le(v___x_1695_, v___x_1695_);
if (v___x_1700_ == 0)
{
if (v___x_1696_ == 0)
{
lean_object* v___x_1702_; 
lean_dec(v_snd_1682_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 1, v___x_1694_);
v___x_1702_ = v___x_1684_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_fst_1681_);
lean_ctor_set(v_reuseFailAlloc_1703_, 1, v___x_1694_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
v___y_1689_ = v___x_1702_;
goto v___jp_1688_;
}
}
else
{
size_t v___x_1704_; size_t v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1704_ = ((size_t)0ULL);
v___x_1705_ = lean_usize_of_nat(v___x_1695_);
v___x_1706_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_1682_, v___x_1704_, v___x_1705_, v___x_1694_);
lean_dec(v_snd_1682_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 1, v___x_1706_);
v___x_1708_ = v___x_1684_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_fst_1681_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
v___y_1689_ = v___x_1708_;
goto v___jp_1688_;
}
}
}
else
{
size_t v___x_1710_; size_t v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1714_; 
v___x_1710_ = ((size_t)0ULL);
v___x_1711_ = lean_usize_of_nat(v___x_1695_);
v___x_1712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_1682_, v___x_1710_, v___x_1711_, v___x_1694_);
lean_dec(v_snd_1682_);
if (v_isShared_1685_ == 0)
{
lean_ctor_set(v___x_1684_, 1, v___x_1712_);
v___x_1714_ = v___x_1684_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_fst_1681_);
lean_ctor_set(v_reuseFailAlloc_1715_, 1, v___x_1712_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
v___y_1689_ = v___x_1714_;
goto v___jp_1688_;
}
}
}
v___jp_1688_:
{
size_t v___x_1690_; size_t v___x_1691_; lean_object* v___x_1692_; 
v___x_1690_ = ((size_t)1ULL);
v___x_1691_ = lean_usize_add(v_i_1677_, v___x_1690_);
v___x_1692_ = lean_array_uset(v_bs_x27_1687_, v_i_1677_, v___y_1689_);
v_i_1677_ = v___x_1691_;
v_bs_1678_ = v___x_1692_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0___boxed(lean_object* v_sz_1717_, lean_object* v_i_1718_, lean_object* v_bs_1719_){
_start:
{
size_t v_sz_boxed_1720_; size_t v_i_boxed_1721_; lean_object* v_res_1722_; 
v_sz_boxed_1720_ = lean_unbox_usize(v_sz_1717_);
lean_dec(v_sz_1717_);
v_i_boxed_1721_ = lean_unbox_usize(v_i_1718_);
lean_dec(v_i_1718_);
v_res_1722_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_boxed_1720_, v_i_boxed_1721_, v_bs_1719_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(size_t v_sz_1723_, size_t v_i_1724_, lean_object* v_bs_1725_){
_start:
{
uint8_t v___x_1726_; 
v___x_1726_ = lean_usize_dec_lt(v_i_1724_, v_sz_1723_);
if (v___x_1726_ == 0)
{
return v_bs_1725_;
}
else
{
lean_object* v_v_1727_; lean_object* v___x_1728_; lean_object* v_bs_x27_1729_; uint8_t v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; size_t v___x_1733_; size_t v___x_1734_; lean_object* v___x_1735_; 
v_v_1727_ = lean_array_uget(v_bs_1725_, v_i_1724_);
v___x_1728_ = lean_unsigned_to_nat(0u);
v_bs_x27_1729_ = lean_array_uset(v_bs_1725_, v_i_1724_, v___x_1728_);
v___x_1730_ = 0;
v___x_1731_ = lean_box(v___x_1730_);
v___x_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
lean_ctor_set(v___x_1732_, 1, v_v_1727_);
v___x_1733_ = ((size_t)1ULL);
v___x_1734_ = lean_usize_add(v_i_1724_, v___x_1733_);
v___x_1735_ = lean_array_uset(v_bs_x27_1729_, v_i_1724_, v___x_1732_);
v_i_1724_ = v___x_1734_;
v_bs_1725_ = v___x_1735_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8___boxed(lean_object* v_sz_1737_, lean_object* v_i_1738_, lean_object* v_bs_1739_){
_start:
{
size_t v_sz_boxed_1740_; size_t v_i_boxed_1741_; lean_object* v_res_1742_; 
v_sz_boxed_1740_ = lean_unbox_usize(v_sz_1737_);
lean_dec(v_sz_1737_);
v_i_boxed_1741_ = lean_unbox_usize(v_i_1738_);
lean_dec(v_i_1738_);
v_res_1742_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_boxed_1740_, v_i_boxed_1741_, v_bs_1739_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(lean_object* v_original_1743_, lean_object* v___x_1744_, lean_object* v_a_1745_, lean_object* v_b_1746_){
_start:
{
lean_object* v_fst_1747_; lean_object* v_snd_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1773_; 
v_fst_1747_ = lean_ctor_get(v_b_1746_, 0);
v_snd_1748_ = lean_ctor_get(v_b_1746_, 1);
v_isSharedCheck_1773_ = !lean_is_exclusive(v_b_1746_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1750_ = v_b_1746_;
v_isShared_1751_ = v_isSharedCheck_1773_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_snd_1748_);
lean_inc(v_fst_1747_);
lean_dec(v_b_1746_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1773_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1752_; uint8_t v___y_1754_; uint8_t v___x_1769_; 
v___x_1752_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_1769_ = lean_nat_dec_lt(v_snd_1748_, v___x_1744_);
if (v___x_1769_ == 0)
{
v___y_1754_ = v___x_1769_;
goto v___jp_1753_;
}
else
{
lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1770_ = lean_array_get_borrowed(v___x_1752_, v_original_1743_, v_snd_1748_);
v___x_1771_ = lean_string_dec_eq(v___x_1770_, v_a_1745_);
if (v___x_1771_ == 0)
{
v___y_1754_ = v___x_1769_;
goto v___jp_1753_;
}
else
{
lean_object* v___x_1772_; 
lean_del_object(v___x_1750_);
v___x_1772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1772_, 0, v_fst_1747_);
lean_ctor_set(v___x_1772_, 1, v_snd_1748_);
return v___x_1772_;
}
}
v___jp_1753_:
{
if (v___y_1754_ == 0)
{
lean_object* v___x_1756_; 
if (v_isShared_1751_ == 0)
{
v___x_1756_ = v___x_1750_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_fst_1747_);
lean_ctor_set(v_reuseFailAlloc_1757_, 1, v_snd_1748_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
else
{
uint8_t v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1762_; 
v___x_1758_ = 1;
v___x_1759_ = lean_array_get_borrowed(v___x_1752_, v_original_1743_, v_snd_1748_);
v___x_1760_ = lean_box(v___x_1758_);
lean_inc(v___x_1759_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 1, v___x_1759_);
lean_ctor_set(v___x_1750_, 0, v___x_1760_);
v___x_1762_ = v___x_1750_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1760_);
lean_ctor_set(v_reuseFailAlloc_1768_, 1, v___x_1759_);
v___x_1762_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1763_ = lean_array_push(v_fst_1747_, v___x_1762_);
v___x_1764_ = lean_unsigned_to_nat(1u);
v___x_1765_ = lean_nat_add(v_snd_1748_, v___x_1764_);
lean_dec(v_snd_1748_);
v___x_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1763_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
v_b_1746_ = v___x_1766_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___boxed(lean_object* v_original_1774_, lean_object* v___x_1775_, lean_object* v_a_1776_, lean_object* v_b_1777_){
_start:
{
lean_object* v_res_1778_; 
v_res_1778_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(v_original_1774_, v___x_1775_, v_a_1776_, v_b_1777_);
lean_dec_ref(v_a_1776_);
lean_dec(v___x_1775_);
lean_dec_ref(v_original_1774_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(lean_object* v_edited_1779_, lean_object* v___x_1780_, lean_object* v_a_1781_, lean_object* v_b_1782_){
_start:
{
lean_object* v_fst_1783_; lean_object* v_snd_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1809_; 
v_fst_1783_ = lean_ctor_get(v_b_1782_, 0);
v_snd_1784_ = lean_ctor_get(v_b_1782_, 1);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_b_1782_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1786_ = v_b_1782_;
v_isShared_1787_ = v_isSharedCheck_1809_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_snd_1784_);
lean_inc(v_fst_1783_);
lean_dec(v_b_1782_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1809_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1788_; uint8_t v___y_1790_; uint8_t v___x_1805_; 
v___x_1788_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_1805_ = lean_nat_dec_lt(v_snd_1784_, v___x_1780_);
if (v___x_1805_ == 0)
{
v___y_1790_ = v___x_1805_;
goto v___jp_1789_;
}
else
{
lean_object* v___x_1806_; uint8_t v___x_1807_; 
v___x_1806_ = lean_array_get_borrowed(v___x_1788_, v_edited_1779_, v_snd_1784_);
v___x_1807_ = lean_string_dec_eq(v___x_1806_, v_a_1781_);
if (v___x_1807_ == 0)
{
v___y_1790_ = v___x_1805_;
goto v___jp_1789_;
}
else
{
lean_object* v___x_1808_; 
lean_del_object(v___x_1786_);
v___x_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1808_, 0, v_fst_1783_);
lean_ctor_set(v___x_1808_, 1, v_snd_1784_);
return v___x_1808_;
}
}
v___jp_1789_:
{
if (v___y_1790_ == 0)
{
lean_object* v___x_1792_; 
if (v_isShared_1787_ == 0)
{
v___x_1792_ = v___x_1786_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_fst_1783_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_snd_1784_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
else
{
uint8_t v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1798_; 
v___x_1794_ = 0;
v___x_1795_ = lean_array_get_borrowed(v___x_1788_, v_edited_1779_, v_snd_1784_);
v___x_1796_ = lean_box(v___x_1794_);
lean_inc(v___x_1795_);
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 1, v___x_1795_);
lean_ctor_set(v___x_1786_, 0, v___x_1796_);
v___x_1798_ = v___x_1786_;
goto v_reusejp_1797_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1796_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v___x_1795_);
v___x_1798_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1797_;
}
v_reusejp_1797_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1799_ = lean_array_push(v_fst_1783_, v___x_1798_);
v___x_1800_ = lean_unsigned_to_nat(1u);
v___x_1801_ = lean_nat_add(v_snd_1784_, v___x_1800_);
lean_dec(v_snd_1784_);
v___x_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1802_, 0, v___x_1799_);
lean_ctor_set(v___x_1802_, 1, v___x_1801_);
v_b_1782_ = v___x_1802_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___boxed(lean_object* v_edited_1810_, lean_object* v___x_1811_, lean_object* v_a_1812_, lean_object* v_b_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v_edited_1810_, v___x_1811_, v_a_1812_, v_b_1813_);
lean_dec_ref(v_a_1812_);
lean_dec(v___x_1811_);
lean_dec_ref(v_edited_1810_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(lean_object* v_original_1815_, lean_object* v___x_1816_, lean_object* v_edited_1817_, lean_object* v___x_1818_, lean_object* v_as_1819_, size_t v_sz_1820_, size_t v_i_1821_, lean_object* v_b_1822_){
_start:
{
uint8_t v___x_1823_; 
v___x_1823_ = lean_usize_dec_lt(v_i_1821_, v_sz_1820_);
if (v___x_1823_ == 0)
{
return v_b_1822_;
}
else
{
lean_object* v_snd_1824_; lean_object* v_fst_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_1872_; 
v_snd_1824_ = lean_ctor_get(v_b_1822_, 1);
v_fst_1825_ = lean_ctor_get(v_b_1822_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v_b_1822_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1827_ = v_b_1822_;
v_isShared_1828_ = v_isSharedCheck_1872_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_snd_1824_);
lean_inc(v_fst_1825_);
lean_dec(v_b_1822_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_1872_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v_fst_1829_; lean_object* v_snd_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1871_; 
v_fst_1829_ = lean_ctor_get(v_snd_1824_, 0);
v_snd_1830_ = lean_ctor_get(v_snd_1824_, 1);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_snd_1824_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1832_ = v_snd_1824_;
v_isShared_1833_ = v_isSharedCheck_1871_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_snd_1830_);
lean_inc(v_fst_1829_);
lean_dec(v_snd_1824_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1871_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v_a_1834_; lean_object* v___x_1836_; 
v_a_1834_ = lean_array_uget_borrowed(v_as_1819_, v_i_1821_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 1, v_fst_1829_);
lean_ctor_set(v___x_1832_, 0, v_fst_1825_);
v___x_1836_ = v___x_1832_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_fst_1825_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v_fst_1829_);
v___x_1836_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
lean_object* v___x_1837_; lean_object* v_fst_1838_; lean_object* v_snd_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1869_; 
v___x_1837_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(v_original_1815_, v___x_1816_, v_a_1834_, v___x_1836_);
v_fst_1838_ = lean_ctor_get(v___x_1837_, 0);
v_snd_1839_ = lean_ctor_get(v___x_1837_, 1);
v_isSharedCheck_1869_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1869_ == 0)
{
v___x_1841_ = v___x_1837_;
v_isShared_1842_ = v_isSharedCheck_1869_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_snd_1839_);
lean_inc(v_fst_1838_);
lean_dec(v___x_1837_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1869_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 1, v_snd_1830_);
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_fst_1838_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v_snd_1830_);
v___x_1844_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1845_; lean_object* v_fst_1846_; lean_object* v_snd_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1867_; 
v___x_1845_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v_edited_1817_, v___x_1818_, v_a_1834_, v___x_1844_);
v_fst_1846_ = lean_ctor_get(v___x_1845_, 0);
v_snd_1847_ = lean_ctor_get(v___x_1845_, 1);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1849_ = v___x_1845_;
v_isShared_1850_ = v_isSharedCheck_1867_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_snd_1847_);
lean_inc(v_fst_1846_);
lean_dec(v___x_1845_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1867_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
uint8_t v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1854_; 
v___x_1851_ = 2;
v___x_1852_ = lean_box(v___x_1851_);
lean_inc(v_a_1834_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 1, v_a_1834_);
lean_ctor_set(v___x_1849_, 0, v___x_1852_);
v___x_1854_ = v___x_1849_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1852_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_a_1834_);
v___x_1854_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1860_; 
v___x_1855_ = lean_array_push(v_fst_1846_, v___x_1854_);
v___x_1856_ = lean_unsigned_to_nat(1u);
v___x_1857_ = lean_nat_add(v_snd_1839_, v___x_1856_);
lean_dec(v_snd_1839_);
v___x_1858_ = lean_nat_add(v_snd_1847_, v___x_1856_);
lean_dec(v_snd_1847_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 1, v___x_1858_);
lean_ctor_set(v___x_1827_, 0, v___x_1857_);
v___x_1860_ = v___x_1827_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1857_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v___x_1858_);
v___x_1860_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
lean_object* v___x_1861_; size_t v___x_1862_; size_t v___x_1863_; 
v___x_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1855_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = ((size_t)1ULL);
v___x_1863_ = lean_usize_add(v_i_1821_, v___x_1862_);
v_i_1821_ = v___x_1863_;
v_b_1822_ = v___x_1861_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14___boxed(lean_object* v_original_1873_, lean_object* v___x_1874_, lean_object* v_edited_1875_, lean_object* v___x_1876_, lean_object* v_as_1877_, lean_object* v_sz_1878_, lean_object* v_i_1879_, lean_object* v_b_1880_){
_start:
{
size_t v_sz_boxed_1881_; size_t v_i_boxed_1882_; lean_object* v_res_1883_; 
v_sz_boxed_1881_ = lean_unbox_usize(v_sz_1878_);
lean_dec(v_sz_1878_);
v_i_boxed_1882_ = lean_unbox_usize(v_i_1879_);
lean_dec(v_i_1879_);
v_res_1883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v_original_1873_, v___x_1874_, v_edited_1875_, v___x_1876_, v_as_1877_, v_sz_boxed_1881_, v_i_boxed_1882_, v_b_1880_);
lean_dec_ref(v_as_1877_);
lean_dec(v___x_1876_);
lean_dec_ref(v_edited_1875_);
lean_dec(v___x_1874_);
lean_dec_ref(v_original_1873_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(lean_object* v_edited_1884_, lean_object* v___x_1885_, lean_object* v_original_1886_, lean_object* v___x_1887_, lean_object* v_as_1888_, size_t v_sz_1889_, size_t v_i_1890_, lean_object* v_b_1891_){
_start:
{
uint8_t v___x_1892_; 
v___x_1892_ = lean_usize_dec_lt(v_i_1890_, v_sz_1889_);
if (v___x_1892_ == 0)
{
return v_b_1891_;
}
else
{
lean_object* v_snd_1893_; lean_object* v_fst_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1941_; 
v_snd_1893_ = lean_ctor_get(v_b_1891_, 1);
v_fst_1894_ = lean_ctor_get(v_b_1891_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_b_1891_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1896_ = v_b_1891_;
v_isShared_1897_ = v_isSharedCheck_1941_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_snd_1893_);
lean_inc(v_fst_1894_);
lean_dec(v_b_1891_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1941_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v_fst_1898_; lean_object* v_snd_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1940_; 
v_fst_1898_ = lean_ctor_get(v_snd_1893_, 0);
v_snd_1899_ = lean_ctor_get(v_snd_1893_, 1);
v_isSharedCheck_1940_ = !lean_is_exclusive(v_snd_1893_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1901_ = v_snd_1893_;
v_isShared_1902_ = v_isSharedCheck_1940_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_snd_1899_);
lean_inc(v_fst_1898_);
lean_dec(v_snd_1893_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1940_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v_a_1903_; lean_object* v___x_1905_; 
v_a_1903_ = lean_array_uget_borrowed(v_as_1888_, v_i_1890_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 1, v_fst_1898_);
lean_ctor_set(v___x_1901_, 0, v_fst_1894_);
v___x_1905_ = v___x_1901_;
goto v_reusejp_1904_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_fst_1894_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_fst_1898_);
v___x_1905_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1904_;
}
v_reusejp_1904_:
{
lean_object* v___x_1906_; lean_object* v_fst_1907_; lean_object* v_snd_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1938_; 
v___x_1906_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(v_original_1886_, v___x_1887_, v_a_1903_, v___x_1905_);
v_fst_1907_ = lean_ctor_get(v___x_1906_, 0);
v_snd_1908_ = lean_ctor_get(v___x_1906_, 1);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1910_ = v___x_1906_;
v_isShared_1911_ = v_isSharedCheck_1938_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_snd_1908_);
lean_inc(v_fst_1907_);
lean_dec(v___x_1906_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1938_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 1, v_snd_1899_);
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_fst_1907_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_snd_1899_);
v___x_1913_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
lean_object* v___x_1914_; lean_object* v_fst_1915_; lean_object* v_snd_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1936_; 
v___x_1914_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v_edited_1884_, v___x_1885_, v_a_1903_, v___x_1913_);
v_fst_1915_ = lean_ctor_get(v___x_1914_, 0);
v_snd_1916_ = lean_ctor_get(v___x_1914_, 1);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1914_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1918_ = v___x_1914_;
v_isShared_1919_ = v_isSharedCheck_1936_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_snd_1916_);
lean_inc(v_fst_1915_);
lean_dec(v___x_1914_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1936_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
uint8_t v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1920_ = 2;
v___x_1921_ = lean_box(v___x_1920_);
lean_inc(v_a_1903_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 1, v_a_1903_);
lean_ctor_set(v___x_1918_, 0, v___x_1921_);
v___x_1923_ = v___x_1918_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1921_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_a_1903_);
v___x_1923_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1929_; 
v___x_1924_ = lean_array_push(v_fst_1915_, v___x_1923_);
v___x_1925_ = lean_unsigned_to_nat(1u);
v___x_1926_ = lean_nat_add(v_snd_1908_, v___x_1925_);
lean_dec(v_snd_1908_);
v___x_1927_ = lean_nat_add(v_snd_1916_, v___x_1925_);
lean_dec(v_snd_1916_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 1, v___x_1927_);
lean_ctor_set(v___x_1896_, 0, v___x_1926_);
v___x_1929_ = v___x_1896_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v___x_1926_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
lean_object* v___x_1930_; size_t v___x_1931_; size_t v___x_1932_; lean_object* v___x_1933_; 
v___x_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1924_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = ((size_t)1ULL);
v___x_1932_ = lean_usize_add(v_i_1890_, v___x_1931_);
v___x_1933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v_original_1886_, v___x_1887_, v_edited_1884_, v___x_1885_, v_as_1888_, v_sz_1889_, v___x_1932_, v___x_1930_);
return v___x_1933_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4___boxed(lean_object* v_edited_1942_, lean_object* v___x_1943_, lean_object* v_original_1944_, lean_object* v___x_1945_, lean_object* v_as_1946_, lean_object* v_sz_1947_, lean_object* v_i_1948_, lean_object* v_b_1949_){
_start:
{
size_t v_sz_boxed_1950_; size_t v_i_boxed_1951_; lean_object* v_res_1952_; 
v_sz_boxed_1950_ = lean_unbox_usize(v_sz_1947_);
lean_dec(v_sz_1947_);
v_i_boxed_1951_ = lean_unbox_usize(v_i_1948_);
lean_dec(v_i_1948_);
v_res_1952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v_edited_1942_, v___x_1943_, v_original_1944_, v___x_1945_, v_as_1946_, v_sz_boxed_1950_, v_i_boxed_1951_, v_b_1949_);
lean_dec_ref(v_as_1946_);
lean_dec(v___x_1945_);
lean_dec_ref(v_original_1944_);
lean_dec(v___x_1943_);
lean_dec_ref(v_edited_1942_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(lean_object* v_a_1953_, lean_object* v_b_1954_){
_start:
{
lean_object* v_array_1955_; lean_object* v_start_1956_; lean_object* v_stop_1957_; lean_object* v___x_1959_; uint8_t v_isShared_1960_; uint8_t v_isSharedCheck_1970_; 
v_array_1955_ = lean_ctor_get(v_a_1953_, 0);
v_start_1956_ = lean_ctor_get(v_a_1953_, 1);
v_stop_1957_ = lean_ctor_get(v_a_1953_, 2);
v_isSharedCheck_1970_ = !lean_is_exclusive(v_a_1953_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1959_ = v_a_1953_;
v_isShared_1960_ = v_isSharedCheck_1970_;
goto v_resetjp_1958_;
}
else
{
lean_inc(v_stop_1957_);
lean_inc(v_start_1956_);
lean_inc(v_array_1955_);
lean_dec(v_a_1953_);
v___x_1959_ = lean_box(0);
v_isShared_1960_ = v_isSharedCheck_1970_;
goto v_resetjp_1958_;
}
v_resetjp_1958_:
{
uint8_t v___x_1961_; 
v___x_1961_ = lean_nat_dec_lt(v_start_1956_, v_stop_1957_);
if (v___x_1961_ == 0)
{
lean_del_object(v___x_1959_);
lean_dec(v_stop_1957_);
lean_dec(v_start_1956_);
lean_dec_ref(v_array_1955_);
return v_b_1954_;
}
else
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1965_; 
v___x_1962_ = lean_unsigned_to_nat(1u);
v___x_1963_ = lean_nat_add(v_start_1956_, v___x_1962_);
lean_inc_ref(v_array_1955_);
if (v_isShared_1960_ == 0)
{
lean_ctor_set(v___x_1959_, 1, v___x_1963_);
v___x_1965_ = v___x_1959_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_array_1955_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v___x_1963_);
lean_ctor_set(v_reuseFailAlloc_1969_, 2, v_stop_1957_);
v___x_1965_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1966_ = lean_array_fget(v_array_1955_, v_start_1956_);
lean_dec(v_start_1956_);
lean_dec_ref(v_array_1955_);
v___x_1967_ = lean_array_push(v_b_1954_, v___x_1966_);
v_a_1953_ = v___x_1965_;
v_b_1954_ = v___x_1967_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6(lean_object* v_left_1971_, lean_object* v_right_1972_, lean_object* v_i_1973_){
_start:
{
lean_object* v_start_1974_; lean_object* v_stop_1975_; lean_object* v___x_1976_; uint8_t v___x_1990_; 
v_start_1974_ = lean_ctor_get(v_left_1971_, 1);
v_stop_1975_ = lean_ctor_get(v_left_1971_, 2);
v___x_1976_ = lean_nat_sub(v_stop_1975_, v_start_1974_);
v___x_1990_ = lean_nat_dec_lt(v_i_1973_, v___x_1976_);
if (v___x_1990_ == 0)
{
goto v___jp_1977_;
}
else
{
lean_object* v_start_1991_; lean_object* v_stop_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v_start_1991_ = lean_ctor_get(v_right_1972_, 1);
v_stop_1992_ = lean_ctor_get(v_right_1972_, 2);
v___x_1993_ = lean_nat_sub(v_stop_1992_, v_start_1991_);
v___x_1994_ = lean_nat_dec_lt(v_i_1973_, v___x_1993_);
if (v___x_1994_ == 0)
{
lean_dec(v___x_1993_);
goto v___jp_1977_;
}
else
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; uint8_t v___x_2002_; 
v___x_1995_ = lean_nat_sub(v___x_1976_, v_i_1973_);
lean_dec(v___x_1976_);
v___x_1996_ = lean_unsigned_to_nat(1u);
v___x_1997_ = lean_nat_sub(v___x_1995_, v___x_1996_);
v___x_1998_ = l_Subarray_get___redArg(v_left_1971_, v___x_1997_);
lean_dec(v___x_1997_);
v___x_1999_ = lean_nat_sub(v___x_1993_, v_i_1973_);
lean_dec(v___x_1993_);
v___x_2000_ = lean_nat_sub(v___x_1999_, v___x_1996_);
v___x_2001_ = l_Subarray_get___redArg(v_right_1972_, v___x_2000_);
lean_dec(v___x_2000_);
v___x_2002_ = lean_string_dec_eq(v___x_1998_, v___x_2001_);
lean_dec(v___x_2001_);
lean_dec(v___x_1998_);
if (v___x_2002_ == 0)
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
lean_dec(v_i_1973_);
lean_inc_ref(v_left_1971_);
v___x_2003_ = l_Subarray_take___redArg(v_left_1971_, v___x_1995_);
v___x_2004_ = l_Subarray_take___redArg(v_right_1972_, v___x_1999_);
lean_dec(v___x_1999_);
v___x_2005_ = l_Subarray_drop___redArg(v_left_1971_, v___x_1995_);
lean_dec(v___x_1995_);
v___x_2006_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2007_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v___x_2005_, v___x_2006_);
v___x_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2004_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
v___x_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2003_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
return v___x_2009_;
}
else
{
lean_object* v___x_2010_; 
lean_dec(v___x_1999_);
lean_dec(v___x_1995_);
v___x_2010_ = lean_nat_add(v_i_1973_, v___x_1996_);
lean_dec(v_i_1973_);
v_i_1973_ = v___x_2010_;
goto _start;
}
}
}
v___jp_1977_:
{
lean_object* v_start_1978_; lean_object* v_stop_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v_start_1978_ = lean_ctor_get(v_right_1972_, 1);
v_stop_1979_ = lean_ctor_get(v_right_1972_, 2);
v___x_1980_ = lean_nat_sub(v___x_1976_, v_i_1973_);
lean_dec(v___x_1976_);
lean_inc_ref(v_left_1971_);
v___x_1981_ = l_Subarray_take___redArg(v_left_1971_, v___x_1980_);
v___x_1982_ = lean_nat_sub(v_stop_1979_, v_start_1978_);
v___x_1983_ = lean_nat_sub(v___x_1982_, v_i_1973_);
lean_dec(v_i_1973_);
lean_dec(v___x_1982_);
v___x_1984_ = l_Subarray_take___redArg(v_right_1972_, v___x_1983_);
lean_dec(v___x_1983_);
v___x_1985_ = l_Subarray_drop___redArg(v_left_1971_, v___x_1980_);
lean_dec(v___x_1980_);
v___x_1986_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_1987_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v___x_1985_, v___x_1986_);
v___x_1988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1984_);
lean_ctor_set(v___x_1988_, 1, v___x_1987_);
v___x_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1981_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
return v___x_1989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3(lean_object* v_left_2012_, lean_object* v_right_2013_){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2014_ = lean_unsigned_to_nat(0u);
v___x_2015_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6(v_left_2012_, v_right_2013_, v___x_2014_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2_spec__4(lean_object* v_left_2016_, lean_object* v_right_2017_, lean_object* v_pref_2018_){
_start:
{
lean_object* v_start_2019_; lean_object* v_stop_2020_; lean_object* v_i_2021_; lean_object* v___x_2027_; uint8_t v___x_2028_; 
v_start_2019_ = lean_ctor_get(v_left_2016_, 1);
v_stop_2020_ = lean_ctor_get(v_left_2016_, 2);
v_i_2021_ = lean_array_get_size(v_pref_2018_);
v___x_2027_ = lean_nat_sub(v_stop_2020_, v_start_2019_);
v___x_2028_ = lean_nat_dec_lt(v_i_2021_, v___x_2027_);
lean_dec(v___x_2027_);
if (v___x_2028_ == 0)
{
goto v___jp_2022_;
}
else
{
lean_object* v_start_2029_; lean_object* v_stop_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; 
v_start_2029_ = lean_ctor_get(v_right_2017_, 1);
v_stop_2030_ = lean_ctor_get(v_right_2017_, 2);
v___x_2031_ = lean_nat_sub(v_stop_2030_, v_start_2029_);
v___x_2032_ = lean_nat_dec_lt(v_i_2021_, v___x_2031_);
lean_dec(v___x_2031_);
if (v___x_2032_ == 0)
{
goto v___jp_2022_;
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; 
v___x_2033_ = l_Subarray_get___redArg(v_left_2016_, v_i_2021_);
v___x_2034_ = l_Subarray_get___redArg(v_right_2017_, v_i_2021_);
v___x_2035_ = lean_string_dec_eq(v___x_2033_, v___x_2034_);
lean_dec(v___x_2034_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
lean_dec(v___x_2033_);
v___x_2036_ = l_Subarray_drop___redArg(v_left_2016_, v_i_2021_);
v___x_2037_ = l_Subarray_drop___redArg(v_right_2017_, v_i_2021_);
v___x_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2036_);
lean_ctor_set(v___x_2038_, 1, v___x_2037_);
v___x_2039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2039_, 0, v_pref_2018_);
lean_ctor_set(v___x_2039_, 1, v___x_2038_);
return v___x_2039_;
}
else
{
lean_object* v___x_2040_; 
v___x_2040_ = lean_array_push(v_pref_2018_, v___x_2033_);
v_pref_2018_ = v___x_2040_;
goto _start;
}
}
}
v___jp_2022_:
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2023_ = l_Subarray_drop___redArg(v_left_2016_, v_i_2021_);
v___x_2024_ = l_Subarray_drop___redArg(v_right_2017_, v_i_2021_);
v___x_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2023_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
v___x_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2026_, 0, v_pref_2018_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
return v___x_2026_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2(lean_object* v_left_2042_, lean_object* v_right_2043_){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2044_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2045_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2_spec__4(v_left_2042_, v_right_2043_, v___x_2044_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(lean_object* v_as_x27_2046_, lean_object* v_b_2047_){
_start:
{
if (lean_obj_tag(v_as_x27_2046_) == 0)
{
return v_b_2047_;
}
else
{
lean_object* v_head_2048_; lean_object* v_snd_2049_; lean_object* v_leftIndex_2050_; 
v_head_2048_ = lean_ctor_get(v_as_x27_2046_, 0);
lean_inc(v_head_2048_);
v_snd_2049_ = lean_ctor_get(v_head_2048_, 1);
lean_inc(v_snd_2049_);
v_leftIndex_2050_ = lean_ctor_get(v_snd_2049_, 1);
lean_inc(v_leftIndex_2050_);
if (lean_obj_tag(v_leftIndex_2050_) == 1)
{
lean_object* v_rightIndex_2051_; 
v_rightIndex_2051_ = lean_ctor_get(v_snd_2049_, 3);
lean_inc(v_rightIndex_2051_);
if (lean_obj_tag(v_rightIndex_2051_) == 1)
{
if (lean_obj_tag(v_b_2047_) == 0)
{
lean_object* v_tail_2052_; lean_object* v___x_2054_; uint8_t v_isShared_2055_; uint8_t v_isSharedCheck_2082_; 
v_tail_2052_ = lean_ctor_get(v_as_x27_2046_, 1);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_as_x27_2046_);
if (v_isSharedCheck_2082_ == 0)
{
lean_object* v_unused_2083_; 
v_unused_2083_ = lean_ctor_get(v_as_x27_2046_, 0);
lean_dec(v_unused_2083_);
v___x_2054_ = v_as_x27_2046_;
v_isShared_2055_ = v_isSharedCheck_2082_;
goto v_resetjp_2053_;
}
else
{
lean_inc(v_tail_2052_);
lean_dec(v_as_x27_2046_);
v___x_2054_ = lean_box(0);
v_isShared_2055_ = v_isSharedCheck_2082_;
goto v_resetjp_2053_;
}
v_resetjp_2053_:
{
lean_object* v_fst_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2080_; 
v_fst_2056_ = lean_ctor_get(v_head_2048_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v_head_2048_);
if (v_isSharedCheck_2080_ == 0)
{
lean_object* v_unused_2081_; 
v_unused_2081_ = lean_ctor_get(v_head_2048_, 1);
lean_dec(v_unused_2081_);
v___x_2058_ = v_head_2048_;
v_isShared_2059_ = v_isSharedCheck_2080_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_fst_2056_);
lean_dec(v_head_2048_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2080_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v_leftCount_2060_; lean_object* v_rightCount_2061_; lean_object* v_val_2062_; lean_object* v_val_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2079_; 
v_leftCount_2060_ = lean_ctor_get(v_snd_2049_, 0);
lean_inc(v_leftCount_2060_);
v_rightCount_2061_ = lean_ctor_get(v_snd_2049_, 2);
lean_inc(v_rightCount_2061_);
lean_dec(v_snd_2049_);
v_val_2062_ = lean_ctor_get(v_leftIndex_2050_, 0);
lean_inc(v_val_2062_);
lean_dec_ref(v_leftIndex_2050_);
v_val_2063_ = lean_ctor_get(v_rightIndex_2051_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_rightIndex_2051_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2065_ = v_rightIndex_2051_;
v_isShared_2066_ = v_isSharedCheck_2079_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_val_2063_);
lean_dec(v_rightIndex_2051_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2079_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2069_; 
v___x_2067_ = lean_nat_add(v_leftCount_2060_, v_rightCount_2061_);
lean_dec(v_rightCount_2061_);
lean_dec(v_leftCount_2060_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 1, v_val_2063_);
lean_ctor_set(v___x_2058_, 0, v_val_2062_);
v___x_2069_ = v___x_2058_;
goto v_reusejp_2068_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_val_2062_);
lean_ctor_set(v_reuseFailAlloc_2078_, 1, v_val_2063_);
v___x_2069_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2068_;
}
v_reusejp_2068_:
{
lean_object* v___x_2071_; 
if (v_isShared_2055_ == 0)
{
lean_ctor_set_tag(v___x_2054_, 0);
lean_ctor_set(v___x_2054_, 1, v___x_2069_);
lean_ctor_set(v___x_2054_, 0, v_fst_2056_);
v___x_2071_ = v___x_2054_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_fst_2056_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v___x_2069_);
v___x_2071_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
lean_object* v___x_2072_; lean_object* v___x_2074_; 
v___x_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2072_, 0, v___x_2067_);
lean_ctor_set(v___x_2072_, 1, v___x_2071_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2072_);
v___x_2074_ = v___x_2065_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2072_);
v___x_2074_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
v_as_x27_2046_ = v_tail_2052_;
v_b_2047_ = v___x_2074_;
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
lean_object* v_val_2084_; lean_object* v_tail_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2126_; 
v_val_2084_ = lean_ctor_get(v_b_2047_, 0);
lean_inc(v_val_2084_);
v_tail_2085_ = lean_ctor_get(v_as_x27_2046_, 1);
v_isSharedCheck_2126_ = !lean_is_exclusive(v_as_x27_2046_);
if (v_isSharedCheck_2126_ == 0)
{
lean_object* v_unused_2127_; 
v_unused_2127_ = lean_ctor_get(v_as_x27_2046_, 0);
lean_dec(v_unused_2127_);
v___x_2087_ = v_as_x27_2046_;
v_isShared_2088_ = v_isSharedCheck_2126_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_tail_2085_);
lean_dec(v_as_x27_2046_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2126_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v_fst_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2124_; 
v_fst_2089_ = lean_ctor_get(v_head_2048_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v_head_2048_);
if (v_isSharedCheck_2124_ == 0)
{
lean_object* v_unused_2125_; 
v_unused_2125_ = lean_ctor_get(v_head_2048_, 1);
lean_dec(v_unused_2125_);
v___x_2091_ = v_head_2048_;
v_isShared_2092_ = v_isSharedCheck_2124_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_fst_2089_);
lean_dec(v_head_2048_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2124_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v_leftCount_2093_; lean_object* v_rightCount_2094_; lean_object* v_val_2095_; lean_object* v_val_2096_; lean_object* v_fst_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2122_; 
v_leftCount_2093_ = lean_ctor_get(v_snd_2049_, 0);
lean_inc(v_leftCount_2093_);
v_rightCount_2094_ = lean_ctor_get(v_snd_2049_, 2);
lean_inc(v_rightCount_2094_);
lean_dec(v_snd_2049_);
v_val_2095_ = lean_ctor_get(v_leftIndex_2050_, 0);
lean_inc(v_val_2095_);
lean_dec_ref(v_leftIndex_2050_);
v_val_2096_ = lean_ctor_get(v_rightIndex_2051_, 0);
lean_inc(v_val_2096_);
lean_dec_ref(v_rightIndex_2051_);
v_fst_2097_ = lean_ctor_get(v_val_2084_, 0);
v_isSharedCheck_2122_ = !lean_is_exclusive(v_val_2084_);
if (v_isSharedCheck_2122_ == 0)
{
lean_object* v_unused_2123_; 
v_unused_2123_ = lean_ctor_get(v_val_2084_, 1);
lean_dec(v_unused_2123_);
v___x_2099_ = v_val_2084_;
v_isShared_2100_ = v_isSharedCheck_2122_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_fst_2097_);
lean_dec(v_val_2084_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2122_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2101_; uint8_t v___x_2102_; 
v___x_2101_ = lean_nat_add(v_leftCount_2093_, v_rightCount_2094_);
lean_dec(v_rightCount_2094_);
lean_dec(v_leftCount_2093_);
v___x_2102_ = lean_nat_dec_lt(v___x_2101_, v_fst_2097_);
lean_dec(v_fst_2097_);
if (v___x_2102_ == 0)
{
lean_dec(v___x_2101_);
lean_del_object(v___x_2099_);
lean_dec(v_val_2096_);
lean_dec(v_val_2095_);
lean_del_object(v___x_2091_);
lean_dec(v_fst_2089_);
lean_del_object(v___x_2087_);
v_as_x27_2046_ = v_tail_2085_;
goto _start;
}
else
{
lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2120_; 
v_isSharedCheck_2120_ = !lean_is_exclusive(v_b_2047_);
if (v_isSharedCheck_2120_ == 0)
{
lean_object* v_unused_2121_; 
v_unused_2121_ = lean_ctor_get(v_b_2047_, 0);
lean_dec(v_unused_2121_);
v___x_2105_ = v_b_2047_;
v_isShared_2106_ = v_isSharedCheck_2120_;
goto v_resetjp_2104_;
}
else
{
lean_dec(v_b_2047_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2120_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 1, v_val_2096_);
lean_ctor_set(v___x_2099_, 0, v_val_2095_);
v___x_2108_ = v___x_2099_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_val_2095_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v_val_2096_);
v___x_2108_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2110_; 
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 1, v___x_2108_);
v___x_2110_ = v___x_2091_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v_fst_2089_);
lean_ctor_set(v_reuseFailAlloc_2118_, 1, v___x_2108_);
v___x_2110_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2112_; 
if (v_isShared_2088_ == 0)
{
lean_ctor_set_tag(v___x_2087_, 0);
lean_ctor_set(v___x_2087_, 1, v___x_2110_);
lean_ctor_set(v___x_2087_, 0, v___x_2101_);
v___x_2112_ = v___x_2087_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v___x_2101_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2114_; 
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 0, v___x_2112_);
v___x_2114_ = v___x_2105_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v___x_2112_);
v___x_2114_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
v_as_x27_2046_ = v_tail_2085_;
v_b_2047_ = v___x_2114_;
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
lean_object* v_tail_2128_; 
lean_dec_ref(v_leftIndex_2050_);
lean_dec(v_rightIndex_2051_);
lean_dec(v_snd_2049_);
lean_dec(v_head_2048_);
v_tail_2128_ = lean_ctor_get(v_as_x27_2046_, 1);
lean_inc(v_tail_2128_);
lean_dec_ref(v_as_x27_2046_);
v_as_x27_2046_ = v_tail_2128_;
goto _start;
}
}
else
{
lean_object* v_tail_2130_; 
lean_dec(v_leftIndex_2050_);
lean_dec(v_snd_2049_);
lean_dec(v_head_2048_);
v_tail_2130_ = lean_ctor_get(v_as_x27_2046_, 1);
lean_inc(v_tail_2130_);
lean_dec_ref(v_as_x27_2046_);
v_as_x27_2046_ = v_tail_2130_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(lean_object* v_a_2132_, lean_object* v_b_2133_, lean_object* v_x_2134_){
_start:
{
if (lean_obj_tag(v_x_2134_) == 0)
{
lean_dec(v_b_2133_);
lean_dec_ref(v_a_2132_);
return v_x_2134_;
}
else
{
lean_object* v_key_2135_; lean_object* v_value_2136_; lean_object* v_tail_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2149_; 
v_key_2135_ = lean_ctor_get(v_x_2134_, 0);
v_value_2136_ = lean_ctor_get(v_x_2134_, 1);
v_tail_2137_ = lean_ctor_get(v_x_2134_, 2);
v_isSharedCheck_2149_ = !lean_is_exclusive(v_x_2134_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2139_ = v_x_2134_;
v_isShared_2140_ = v_isSharedCheck_2149_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_tail_2137_);
lean_inc(v_value_2136_);
lean_inc(v_key_2135_);
lean_dec(v_x_2134_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2149_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
uint8_t v___x_2141_; 
v___x_2141_ = lean_string_dec_eq(v_key_2135_, v_a_2132_);
if (v___x_2141_ == 0)
{
lean_object* v___x_2142_; lean_object* v___x_2144_; 
v___x_2142_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(v_a_2132_, v_b_2133_, v_tail_2137_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 2, v___x_2142_);
v___x_2144_ = v___x_2139_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_key_2135_);
lean_ctor_set(v_reuseFailAlloc_2145_, 1, v_value_2136_);
lean_ctor_set(v_reuseFailAlloc_2145_, 2, v___x_2142_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
else
{
lean_object* v___x_2147_; 
lean_dec(v_value_2136_);
lean_dec(v_key_2135_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 1, v_b_2133_);
lean_ctor_set(v___x_2139_, 0, v_a_2132_);
v___x_2147_ = v___x_2139_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2132_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_b_2133_);
lean_ctor_set(v_reuseFailAlloc_2148_, 2, v_tail_2137_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(lean_object* v_a_2150_, lean_object* v_x_2151_){
_start:
{
if (lean_obj_tag(v_x_2151_) == 0)
{
uint8_t v___x_2152_; 
v___x_2152_ = 0;
return v___x_2152_;
}
else
{
lean_object* v_key_2153_; lean_object* v_tail_2154_; uint8_t v___x_2155_; 
v_key_2153_ = lean_ctor_get(v_x_2151_, 0);
v_tail_2154_ = lean_ctor_get(v_x_2151_, 2);
v___x_2155_ = lean_string_dec_eq(v_key_2153_, v_a_2150_);
if (v___x_2155_ == 0)
{
v_x_2151_ = v_tail_2154_;
goto _start;
}
else
{
return v___x_2155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg___boxed(lean_object* v_a_2157_, lean_object* v_x_2158_){
_start:
{
uint8_t v_res_2159_; lean_object* v_r_2160_; 
v_res_2159_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(v_a_2157_, v_x_2158_);
lean_dec(v_x_2158_);
lean_dec_ref(v_a_2157_);
v_r_2160_ = lean_box(v_res_2159_);
return v_r_2160_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29___redArg(lean_object* v_x_2161_, lean_object* v_x_2162_){
_start:
{
if (lean_obj_tag(v_x_2162_) == 0)
{
return v_x_2161_;
}
else
{
lean_object* v_key_2163_; lean_object* v_value_2164_; lean_object* v_tail_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2188_; 
v_key_2163_ = lean_ctor_get(v_x_2162_, 0);
v_value_2164_ = lean_ctor_get(v_x_2162_, 1);
v_tail_2165_ = lean_ctor_get(v_x_2162_, 2);
v_isSharedCheck_2188_ = !lean_is_exclusive(v_x_2162_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2167_ = v_x_2162_;
v_isShared_2168_ = v_isSharedCheck_2188_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_tail_2165_);
lean_inc(v_value_2164_);
lean_inc(v_key_2163_);
lean_dec(v_x_2162_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2188_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; uint64_t v___x_2170_; uint64_t v___x_2171_; uint64_t v___x_2172_; uint64_t v_fold_2173_; uint64_t v___x_2174_; uint64_t v___x_2175_; uint64_t v___x_2176_; size_t v___x_2177_; size_t v___x_2178_; size_t v___x_2179_; size_t v___x_2180_; size_t v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2184_; 
v___x_2169_ = lean_array_get_size(v_x_2161_);
v___x_2170_ = lean_string_hash(v_key_2163_);
v___x_2171_ = 32ULL;
v___x_2172_ = lean_uint64_shift_right(v___x_2170_, v___x_2171_);
v_fold_2173_ = lean_uint64_xor(v___x_2170_, v___x_2172_);
v___x_2174_ = 16ULL;
v___x_2175_ = lean_uint64_shift_right(v_fold_2173_, v___x_2174_);
v___x_2176_ = lean_uint64_xor(v_fold_2173_, v___x_2175_);
v___x_2177_ = lean_uint64_to_usize(v___x_2176_);
v___x_2178_ = lean_usize_of_nat(v___x_2169_);
v___x_2179_ = ((size_t)1ULL);
v___x_2180_ = lean_usize_sub(v___x_2178_, v___x_2179_);
v___x_2181_ = lean_usize_land(v___x_2177_, v___x_2180_);
v___x_2182_ = lean_array_uget_borrowed(v_x_2161_, v___x_2181_);
lean_inc(v___x_2182_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 2, v___x_2182_);
v___x_2184_ = v___x_2167_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_key_2163_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_value_2164_);
lean_ctor_set(v_reuseFailAlloc_2187_, 2, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2185_; 
v___x_2185_ = lean_array_uset(v_x_2161_, v___x_2181_, v___x_2184_);
v_x_2161_ = v___x_2185_;
v_x_2162_ = v_tail_2165_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28___redArg(lean_object* v_i_2189_, lean_object* v_source_2190_, lean_object* v_target_2191_){
_start:
{
lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2192_ = lean_array_get_size(v_source_2190_);
v___x_2193_ = lean_nat_dec_lt(v_i_2189_, v___x_2192_);
if (v___x_2193_ == 0)
{
lean_dec_ref(v_source_2190_);
lean_dec(v_i_2189_);
return v_target_2191_;
}
else
{
lean_object* v_es_2194_; lean_object* v___x_2195_; lean_object* v_source_2196_; lean_object* v_target_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v_es_2194_ = lean_array_fget(v_source_2190_, v_i_2189_);
v___x_2195_ = lean_box(0);
v_source_2196_ = lean_array_fset(v_source_2190_, v_i_2189_, v___x_2195_);
v_target_2197_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29___redArg(v_target_2191_, v_es_2194_);
v___x_2198_ = lean_unsigned_to_nat(1u);
v___x_2199_ = lean_nat_add(v_i_2189_, v___x_2198_);
lean_dec(v_i_2189_);
v_i_2189_ = v___x_2199_;
v_source_2190_ = v_source_2196_;
v_target_2191_ = v_target_2197_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23___redArg(lean_object* v_data_2201_){
_start:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v_nbuckets_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2202_ = lean_array_get_size(v_data_2201_);
v___x_2203_ = lean_unsigned_to_nat(2u);
v_nbuckets_2204_ = lean_nat_mul(v___x_2202_, v___x_2203_);
v___x_2205_ = lean_unsigned_to_nat(0u);
v___x_2206_ = lean_box(0);
v___x_2207_ = lean_mk_array(v_nbuckets_2204_, v___x_2206_);
v___x_2208_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28___redArg(v___x_2205_, v_data_2201_, v___x_2207_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(lean_object* v_m_2209_, lean_object* v_a_2210_, lean_object* v_b_2211_){
_start:
{
lean_object* v_size_2212_; lean_object* v_buckets_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2256_; 
v_size_2212_ = lean_ctor_get(v_m_2209_, 0);
v_buckets_2213_ = lean_ctor_get(v_m_2209_, 1);
v_isSharedCheck_2256_ = !lean_is_exclusive(v_m_2209_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2215_ = v_m_2209_;
v_isShared_2216_ = v_isSharedCheck_2256_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_buckets_2213_);
lean_inc(v_size_2212_);
lean_dec(v_m_2209_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2256_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2217_; uint64_t v___x_2218_; uint64_t v___x_2219_; uint64_t v___x_2220_; uint64_t v_fold_2221_; uint64_t v___x_2222_; uint64_t v___x_2223_; uint64_t v___x_2224_; size_t v___x_2225_; size_t v___x_2226_; size_t v___x_2227_; size_t v___x_2228_; size_t v___x_2229_; lean_object* v_bkt_2230_; uint8_t v___x_2231_; 
v___x_2217_ = lean_array_get_size(v_buckets_2213_);
v___x_2218_ = lean_string_hash(v_a_2210_);
v___x_2219_ = 32ULL;
v___x_2220_ = lean_uint64_shift_right(v___x_2218_, v___x_2219_);
v_fold_2221_ = lean_uint64_xor(v___x_2218_, v___x_2220_);
v___x_2222_ = 16ULL;
v___x_2223_ = lean_uint64_shift_right(v_fold_2221_, v___x_2222_);
v___x_2224_ = lean_uint64_xor(v_fold_2221_, v___x_2223_);
v___x_2225_ = lean_uint64_to_usize(v___x_2224_);
v___x_2226_ = lean_usize_of_nat(v___x_2217_);
v___x_2227_ = ((size_t)1ULL);
v___x_2228_ = lean_usize_sub(v___x_2226_, v___x_2227_);
v___x_2229_ = lean_usize_land(v___x_2225_, v___x_2228_);
v_bkt_2230_ = lean_array_uget_borrowed(v_buckets_2213_, v___x_2229_);
v___x_2231_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(v_a_2210_, v_bkt_2230_);
if (v___x_2231_ == 0)
{
lean_object* v___x_2232_; lean_object* v_size_x27_2233_; lean_object* v___x_2234_; lean_object* v_buckets_x27_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; uint8_t v___x_2241_; 
v___x_2232_ = lean_unsigned_to_nat(1u);
v_size_x27_2233_ = lean_nat_add(v_size_2212_, v___x_2232_);
lean_dec(v_size_2212_);
lean_inc(v_bkt_2230_);
v___x_2234_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2234_, 0, v_a_2210_);
lean_ctor_set(v___x_2234_, 1, v_b_2211_);
lean_ctor_set(v___x_2234_, 2, v_bkt_2230_);
v_buckets_x27_2235_ = lean_array_uset(v_buckets_2213_, v___x_2229_, v___x_2234_);
v___x_2236_ = lean_unsigned_to_nat(4u);
v___x_2237_ = lean_nat_mul(v_size_x27_2233_, v___x_2236_);
v___x_2238_ = lean_unsigned_to_nat(3u);
v___x_2239_ = lean_nat_div(v___x_2237_, v___x_2238_);
lean_dec(v___x_2237_);
v___x_2240_ = lean_array_get_size(v_buckets_x27_2235_);
v___x_2241_ = lean_nat_dec_le(v___x_2239_, v___x_2240_);
lean_dec(v___x_2239_);
if (v___x_2241_ == 0)
{
lean_object* v_val_2242_; lean_object* v___x_2244_; 
v_val_2242_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23___redArg(v_buckets_x27_2235_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 1, v_val_2242_);
lean_ctor_set(v___x_2215_, 0, v_size_x27_2233_);
v___x_2244_ = v___x_2215_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_size_x27_2233_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_val_2242_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
else
{
lean_object* v___x_2247_; 
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 1, v_buckets_x27_2235_);
lean_ctor_set(v___x_2215_, 0, v_size_x27_2233_);
v___x_2247_ = v___x_2215_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_size_x27_2233_);
lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_buckets_x27_2235_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
else
{
lean_object* v___x_2249_; lean_object* v_buckets_x27_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2254_; 
lean_inc(v_bkt_2230_);
v___x_2249_ = lean_box(0);
v_buckets_x27_2250_ = lean_array_uset(v_buckets_2213_, v___x_2229_, v___x_2249_);
v___x_2251_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(v_a_2210_, v_b_2211_, v_bkt_2230_);
v___x_2252_ = lean_array_uset(v_buckets_x27_2250_, v___x_2229_, v___x_2251_);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 1, v___x_2252_);
v___x_2254_ = v___x_2215_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_size_2212_);
lean_ctor_set(v_reuseFailAlloc_2255_, 1, v___x_2252_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(lean_object* v_a_2257_, lean_object* v_x_2258_){
_start:
{
if (lean_obj_tag(v_x_2258_) == 0)
{
lean_object* v___x_2259_; 
v___x_2259_ = lean_box(0);
return v___x_2259_;
}
else
{
lean_object* v_key_2260_; lean_object* v_value_2261_; lean_object* v_tail_2262_; uint8_t v___x_2263_; 
v_key_2260_ = lean_ctor_get(v_x_2258_, 0);
v_value_2261_ = lean_ctor_get(v_x_2258_, 1);
v_tail_2262_ = lean_ctor_get(v_x_2258_, 2);
v___x_2263_ = lean_string_dec_eq(v_key_2260_, v_a_2257_);
if (v___x_2263_ == 0)
{
v_x_2258_ = v_tail_2262_;
goto _start;
}
else
{
lean_object* v___x_2265_; 
lean_inc(v_value_2261_);
v___x_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2265_, 0, v_value_2261_);
return v___x_2265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg___boxed(lean_object* v_a_2266_, lean_object* v_x_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(v_a_2266_, v_x_2267_);
lean_dec(v_x_2267_);
lean_dec_ref(v_a_2266_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(lean_object* v_m_2269_, lean_object* v_a_2270_){
_start:
{
lean_object* v_buckets_2271_; lean_object* v___x_2272_; uint64_t v___x_2273_; uint64_t v___x_2274_; uint64_t v___x_2275_; uint64_t v_fold_2276_; uint64_t v___x_2277_; uint64_t v___x_2278_; uint64_t v___x_2279_; size_t v___x_2280_; size_t v___x_2281_; size_t v___x_2282_; size_t v___x_2283_; size_t v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v_buckets_2271_ = lean_ctor_get(v_m_2269_, 1);
v___x_2272_ = lean_array_get_size(v_buckets_2271_);
v___x_2273_ = lean_string_hash(v_a_2270_);
v___x_2274_ = 32ULL;
v___x_2275_ = lean_uint64_shift_right(v___x_2273_, v___x_2274_);
v_fold_2276_ = lean_uint64_xor(v___x_2273_, v___x_2275_);
v___x_2277_ = 16ULL;
v___x_2278_ = lean_uint64_shift_right(v_fold_2276_, v___x_2277_);
v___x_2279_ = lean_uint64_xor(v_fold_2276_, v___x_2278_);
v___x_2280_ = lean_uint64_to_usize(v___x_2279_);
v___x_2281_ = lean_usize_of_nat(v___x_2272_);
v___x_2282_ = ((size_t)1ULL);
v___x_2283_ = lean_usize_sub(v___x_2281_, v___x_2282_);
v___x_2284_ = lean_usize_land(v___x_2280_, v___x_2283_);
v___x_2285_ = lean_array_uget_borrowed(v_buckets_2271_, v___x_2284_);
v___x_2286_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(v_a_2270_, v___x_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg___boxed(lean_object* v_m_2287_, lean_object* v_a_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_m_2287_, v_a_2288_);
lean_dec_ref(v_a_2288_);
lean_dec_ref(v_m_2287_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(lean_object* v_histogram_2290_, lean_object* v_index_2291_, lean_object* v_val_2292_){
_start:
{
lean_object* v___x_2293_; 
v___x_2293_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_histogram_2290_, v_val_2292_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2294_ = lean_unsigned_to_nat(1u);
v___x_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2295_, 0, v_index_2291_);
v___x_2296_ = lean_unsigned_to_nat(0u);
v___x_2297_ = lean_box(0);
v___x_2298_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2294_);
lean_ctor_set(v___x_2298_, 1, v___x_2295_);
lean_ctor_set(v___x_2298_, 2, v___x_2296_);
lean_ctor_set(v___x_2298_, 3, v___x_2297_);
v___x_2299_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2290_, v_val_2292_, v___x_2298_);
return v___x_2299_;
}
else
{
lean_object* v_val_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2321_; 
v_val_2300_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2302_ = v___x_2293_;
v_isShared_2303_ = v_isSharedCheck_2321_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_val_2300_);
lean_dec(v___x_2293_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2321_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v_leftCount_2304_; lean_object* v_rightCount_2305_; lean_object* v_rightIndex_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2319_; 
v_leftCount_2304_ = lean_ctor_get(v_val_2300_, 0);
v_rightCount_2305_ = lean_ctor_get(v_val_2300_, 2);
v_rightIndex_2306_ = lean_ctor_get(v_val_2300_, 3);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_val_2300_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; 
v_unused_2320_ = lean_ctor_get(v_val_2300_, 1);
lean_dec(v_unused_2320_);
v___x_2308_ = v_val_2300_;
v_isShared_2309_ = v_isSharedCheck_2319_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_rightIndex_2306_);
lean_inc(v_rightCount_2305_);
lean_inc(v_leftCount_2304_);
lean_dec(v_val_2300_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2319_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2310_ = lean_unsigned_to_nat(1u);
v___x_2311_ = lean_nat_add(v_leftCount_2304_, v___x_2310_);
lean_dec(v_leftCount_2304_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v_index_2291_);
v___x_2313_ = v___x_2302_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_index_2291_);
v___x_2313_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
lean_object* v___x_2315_; 
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 1, v___x_2313_);
lean_ctor_set(v___x_2308_, 0, v___x_2311_);
v___x_2315_ = v___x_2308_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v___x_2311_);
lean_ctor_set(v_reuseFailAlloc_2317_, 1, v___x_2313_);
lean_ctor_set(v_reuseFailAlloc_2317_, 2, v_rightCount_2305_);
lean_ctor_set(v_reuseFailAlloc_2317_, 3, v_rightIndex_2306_);
v___x_2315_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2290_, v_val_2292_, v___x_2315_);
return v___x_2316_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(lean_object* v_upperBound_2322_, lean_object* v_fst_2323_, lean_object* v___x_2324_, lean_object* v_fst_2325_, lean_object* v_a_2326_, lean_object* v_b_2327_){
_start:
{
uint8_t v___x_2328_; 
v___x_2328_ = lean_nat_dec_lt(v_a_2326_, v_upperBound_2322_);
if (v___x_2328_ == 0)
{
lean_dec(v_a_2326_);
return v_b_2327_;
}
else
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2329_ = l_Subarray_get___redArg(v_fst_2325_, v_a_2326_);
lean_inc(v_a_2326_);
v___x_2330_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(v_b_2327_, v_a_2326_, v___x_2329_);
v___x_2331_ = lean_unsigned_to_nat(1u);
v___x_2332_ = lean_nat_add(v_a_2326_, v___x_2331_);
lean_dec(v_a_2326_);
v_a_2326_ = v___x_2332_;
v_b_2327_ = v___x_2330_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_upperBound_2334_, lean_object* v_fst_2335_, lean_object* v___x_2336_, lean_object* v_fst_2337_, lean_object* v_a_2338_, lean_object* v_b_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(v_upperBound_2334_, v_fst_2335_, v___x_2336_, v_fst_2337_, v_a_2338_, v_b_2339_);
lean_dec_ref(v_fst_2337_);
lean_dec(v___x_2336_);
lean_dec_ref(v_fst_2335_);
lean_dec(v_upperBound_2334_);
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(lean_object* v_x_2341_, lean_object* v_x_2342_){
_start:
{
if (lean_obj_tag(v_x_2342_) == 0)
{
lean_inc(v_x_2341_);
return v_x_2341_;
}
else
{
lean_object* v_key_2343_; lean_object* v_value_2344_; lean_object* v_tail_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v_key_2343_ = lean_ctor_get(v_x_2342_, 0);
v_value_2344_ = lean_ctor_get(v_x_2342_, 1);
v_tail_2345_ = lean_ctor_get(v_x_2342_, 2);
v___x_2346_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(v_x_2341_, v_tail_2345_);
lean_inc(v_value_2344_);
lean_inc(v_key_2343_);
v___x_2347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2347_, 0, v_key_2343_);
lean_ctor_set(v___x_2347_, 1, v_value_2344_);
v___x_2348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2347_);
lean_ctor_set(v___x_2348_, 1, v___x_2346_);
return v___x_2348_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5___boxed(lean_object* v_x_2349_, lean_object* v_x_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(v_x_2349_, v_x_2350_);
lean_dec(v_x_2350_);
lean_dec(v_x_2349_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(lean_object* v_as_2352_, size_t v_i_2353_, size_t v_stop_2354_, lean_object* v_b_2355_){
_start:
{
uint8_t v___x_2356_; 
v___x_2356_ = lean_usize_dec_eq(v_i_2353_, v_stop_2354_);
if (v___x_2356_ == 0)
{
size_t v___x_2357_; size_t v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2357_ = ((size_t)1ULL);
v___x_2358_ = lean_usize_sub(v_i_2353_, v___x_2357_);
v___x_2359_ = lean_array_uget_borrowed(v_as_2352_, v___x_2358_);
v___x_2360_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(v_b_2355_, v___x_2359_);
lean_dec(v_b_2355_);
v_i_2353_ = v___x_2358_;
v_b_2355_ = v___x_2360_;
goto _start;
}
else
{
return v_b_2355_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6___boxed(lean_object* v_as_2362_, lean_object* v_i_2363_, lean_object* v_stop_2364_, lean_object* v_b_2365_){
_start:
{
size_t v_i_boxed_2366_; size_t v_stop_boxed_2367_; lean_object* v_res_2368_; 
v_i_boxed_2366_ = lean_unbox_usize(v_i_2363_);
lean_dec(v_i_2363_);
v_stop_boxed_2367_ = lean_unbox_usize(v_stop_2364_);
lean_dec(v_stop_2364_);
v_res_2368_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(v_as_2362_, v_i_boxed_2366_, v_stop_boxed_2367_, v_b_2365_);
lean_dec_ref(v_as_2362_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(lean_object* v_histogram_2369_, lean_object* v_index_2370_, lean_object* v_val_2371_){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_histogram_2369_, v_val_2371_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2373_ = lean_unsigned_to_nat(0u);
v___x_2374_ = lean_box(0);
v___x_2375_ = lean_unsigned_to_nat(1u);
v___x_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2376_, 0, v_index_2370_);
v___x_2377_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2373_);
lean_ctor_set(v___x_2377_, 1, v___x_2374_);
lean_ctor_set(v___x_2377_, 2, v___x_2375_);
lean_ctor_set(v___x_2377_, 3, v___x_2376_);
v___x_2378_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2369_, v_val_2371_, v___x_2377_);
return v___x_2378_;
}
else
{
lean_object* v_val_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2400_; 
v_val_2379_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2381_ = v___x_2372_;
v_isShared_2382_ = v_isSharedCheck_2400_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_val_2379_);
lean_dec(v___x_2372_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2400_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v_leftCount_2383_; lean_object* v_leftIndex_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2397_; 
v_leftCount_2383_ = lean_ctor_get(v_val_2379_, 0);
v_leftIndex_2384_ = lean_ctor_get(v_val_2379_, 1);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_val_2379_);
if (v_isSharedCheck_2397_ == 0)
{
lean_object* v_unused_2398_; lean_object* v_unused_2399_; 
v_unused_2398_ = lean_ctor_get(v_val_2379_, 3);
lean_dec(v_unused_2398_);
v_unused_2399_ = lean_ctor_get(v_val_2379_, 2);
lean_dec(v_unused_2399_);
v___x_2386_ = v_val_2379_;
v_isShared_2387_ = v_isSharedCheck_2397_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_leftIndex_2384_);
lean_inc(v_leftCount_2383_);
lean_dec(v_val_2379_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2397_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2391_; 
v___x_2388_ = lean_unsigned_to_nat(1u);
v___x_2389_ = lean_nat_add(v_leftCount_2383_, v___x_2388_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 0, v_index_2370_);
v___x_2391_ = v___x_2381_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_index_2370_);
v___x_2391_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
lean_object* v___x_2393_; 
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 3, v___x_2391_);
lean_ctor_set(v___x_2386_, 2, v___x_2389_);
v___x_2393_ = v___x_2386_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_leftCount_2383_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_leftIndex_2384_);
lean_ctor_set(v_reuseFailAlloc_2395_, 2, v___x_2389_);
lean_ctor_set(v_reuseFailAlloc_2395_, 3, v___x_2391_);
v___x_2393_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2369_, v_val_2371_, v___x_2393_);
return v___x_2394_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(lean_object* v_upperBound_2401_, lean_object* v___x_2402_, lean_object* v_fst_2403_, lean_object* v___x_2404_, lean_object* v_a_2405_, lean_object* v_b_2406_){
_start:
{
uint8_t v___x_2407_; 
v___x_2407_ = lean_nat_dec_lt(v_a_2405_, v_upperBound_2401_);
if (v___x_2407_ == 0)
{
lean_dec(v_a_2405_);
return v_b_2406_;
}
else
{
lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2408_ = l_Subarray_get___redArg(v_fst_2403_, v_a_2405_);
lean_inc(v_a_2405_);
v___x_2409_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(v_b_2406_, v_a_2405_, v___x_2408_);
v___x_2410_ = lean_unsigned_to_nat(1u);
v___x_2411_ = lean_nat_add(v_a_2405_, v___x_2410_);
lean_dec(v_a_2405_);
v_a_2405_ = v___x_2411_;
v_b_2406_ = v___x_2409_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg___boxed(lean_object* v_upperBound_2413_, lean_object* v___x_2414_, lean_object* v_fst_2415_, lean_object* v___x_2416_, lean_object* v_a_2417_, lean_object* v_b_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(v_upperBound_2413_, v___x_2414_, v_fst_2415_, v___x_2416_, v_a_2417_, v_b_2418_);
lean_dec(v___x_2416_);
lean_dec_ref(v_fst_2415_);
lean_dec(v___x_2414_);
lean_dec(v_upperBound_2413_);
return v_res_2419_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2420_ = lean_box(0);
v___x_2421_ = lean_unsigned_to_nat(16u);
v___x_2422_ = lean_mk_array(v___x_2421_, v___x_2420_);
return v___x_2422_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v_hist_2425_; 
v___x_2423_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0);
v___x_2424_ = lean_unsigned_to_nat(0u);
v_hist_2425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_2425_, 0, v___x_2424_);
lean_ctor_set(v_hist_2425_, 1, v___x_2423_);
return v_hist_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(lean_object* v_left_2426_, lean_object* v_right_2427_){
_start:
{
lean_object* v___x_2428_; lean_object* v_snd_2429_; lean_object* v_fst_2430_; lean_object* v_fst_2431_; lean_object* v_snd_2432_; lean_object* v___x_2433_; lean_object* v_snd_2434_; lean_object* v_fst_2435_; lean_object* v_fst_2436_; lean_object* v_snd_2437_; lean_object* v_start_2438_; lean_object* v_stop_2439_; lean_object* v___x_2440_; lean_object* v_hist_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v_start_2444_; lean_object* v_stop_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v_buckets_2448_; lean_object* v___x_2449_; lean_object* v___y_2451_; lean_object* v___x_2477_; lean_object* v___x_2478_; uint8_t v___x_2479_; 
v___x_2428_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2(v_left_2426_, v_right_2427_);
v_snd_2429_ = lean_ctor_get(v___x_2428_, 1);
lean_inc(v_snd_2429_);
v_fst_2430_ = lean_ctor_get(v___x_2428_, 0);
lean_inc(v_fst_2430_);
lean_dec_ref(v___x_2428_);
v_fst_2431_ = lean_ctor_get(v_snd_2429_, 0);
lean_inc(v_fst_2431_);
v_snd_2432_ = lean_ctor_get(v_snd_2429_, 1);
lean_inc(v_snd_2432_);
lean_dec(v_snd_2429_);
v___x_2433_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3(v_fst_2431_, v_snd_2432_);
v_snd_2434_ = lean_ctor_get(v___x_2433_, 1);
lean_inc(v_snd_2434_);
v_fst_2435_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_fst_2435_);
lean_dec_ref(v___x_2433_);
v_fst_2436_ = lean_ctor_get(v_snd_2434_, 0);
lean_inc(v_fst_2436_);
v_snd_2437_ = lean_ctor_get(v_snd_2434_, 1);
lean_inc(v_snd_2437_);
lean_dec(v_snd_2434_);
v_start_2438_ = lean_ctor_get(v_fst_2435_, 1);
v_stop_2439_ = lean_ctor_get(v_fst_2435_, 2);
v___x_2440_ = lean_unsigned_to_nat(0u);
v_hist_2441_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1);
v___x_2442_ = lean_nat_sub(v_stop_2439_, v_start_2438_);
v___x_2443_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(v___x_2442_, v_fst_2436_, v___x_2442_, v_fst_2435_, v___x_2440_, v_hist_2441_);
v_start_2444_ = lean_ctor_get(v_fst_2436_, 1);
v_stop_2445_ = lean_ctor_get(v_fst_2436_, 2);
v___x_2446_ = lean_nat_sub(v_stop_2445_, v_start_2444_);
v___x_2447_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(v___x_2446_, v___x_2446_, v_fst_2436_, v___x_2442_, v___x_2440_, v___x_2443_);
lean_dec(v___x_2442_);
lean_dec(v___x_2446_);
v_buckets_2448_ = lean_ctor_get(v___x_2447_, 1);
lean_inc_ref(v_buckets_2448_);
lean_dec_ref(v___x_2447_);
v___x_2449_ = lean_box(0);
v___x_2477_ = lean_box(0);
v___x_2478_ = lean_array_get_size(v_buckets_2448_);
v___x_2479_ = lean_nat_dec_lt(v___x_2440_, v___x_2478_);
if (v___x_2479_ == 0)
{
lean_dec_ref(v_buckets_2448_);
v___y_2451_ = v___x_2477_;
goto v___jp_2450_;
}
else
{
size_t v___x_2480_; size_t v___x_2481_; lean_object* v___x_2482_; 
v___x_2480_ = lean_usize_of_nat(v___x_2478_);
v___x_2481_ = ((size_t)0ULL);
v___x_2482_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(v_buckets_2448_, v___x_2480_, v___x_2481_, v___x_2477_);
lean_dec_ref(v_buckets_2448_);
v___y_2451_ = v___x_2482_;
goto v___jp_2450_;
}
v___jp_2450_:
{
lean_object* v___x_2452_; 
v___x_2452_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(v___y_2451_, v___x_2449_);
if (lean_obj_tag(v___x_2452_) == 1)
{
lean_object* v_val_2453_; lean_object* v_snd_2454_; lean_object* v_snd_2455_; lean_object* v_fst_2456_; lean_object* v_fst_2457_; lean_object* v_snd_2458_; lean_object* v___x_2459_; lean_object* v_fst_2460_; lean_object* v_snd_2461_; lean_object* v___x_2462_; lean_object* v_fst_2463_; lean_object* v_snd_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v_val_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_val_2453_);
lean_dec_ref(v___x_2452_);
v_snd_2454_ = lean_ctor_get(v_val_2453_, 1);
lean_inc(v_snd_2454_);
lean_dec(v_val_2453_);
v_snd_2455_ = lean_ctor_get(v_snd_2454_, 1);
lean_inc(v_snd_2455_);
v_fst_2456_ = lean_ctor_get(v_snd_2454_, 0);
lean_inc(v_fst_2456_);
lean_dec(v_snd_2454_);
v_fst_2457_ = lean_ctor_get(v_snd_2455_, 0);
lean_inc(v_fst_2457_);
v_snd_2458_ = lean_ctor_get(v_snd_2455_, 1);
lean_inc(v_snd_2458_);
lean_dec(v_snd_2455_);
v___x_2459_ = l_Subarray_split___redArg(v_fst_2435_, v_fst_2457_);
lean_dec(v_fst_2457_);
v_fst_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_fst_2460_);
v_snd_2461_ = lean_ctor_get(v___x_2459_, 1);
lean_inc(v_snd_2461_);
lean_dec_ref(v___x_2459_);
v___x_2462_ = l_Subarray_split___redArg(v_fst_2436_, v_snd_2458_);
lean_dec(v_snd_2458_);
v_fst_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_fst_2463_);
v_snd_2464_ = lean_ctor_get(v___x_2462_, 1);
lean_inc(v_snd_2464_);
lean_dec_ref(v___x_2462_);
v___x_2465_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v_fst_2460_, v_fst_2463_);
v___x_2466_ = l_Array_append___redArg(v_fst_2430_, v___x_2465_);
lean_dec_ref(v___x_2465_);
v___x_2467_ = lean_unsigned_to_nat(1u);
v___x_2468_ = lean_mk_empty_array_with_capacity(v___x_2467_);
v___x_2469_ = lean_array_push(v___x_2468_, v_fst_2456_);
v___x_2470_ = l_Array_append___redArg(v___x_2466_, v___x_2469_);
lean_dec_ref(v___x_2469_);
v___x_2471_ = l_Subarray_drop___redArg(v_snd_2461_, v___x_2467_);
v___x_2472_ = l_Subarray_drop___redArg(v_snd_2464_, v___x_2467_);
v___x_2473_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v___x_2471_, v___x_2472_);
v___x_2474_ = l_Array_append___redArg(v___x_2470_, v___x_2473_);
lean_dec_ref(v___x_2473_);
v___x_2475_ = l_Array_append___redArg(v___x_2474_, v_snd_2437_);
lean_dec(v_snd_2437_);
return v___x_2475_;
}
else
{
lean_object* v___x_2476_; 
lean_dec(v___x_2452_);
lean_dec(v_fst_2436_);
lean_dec(v_fst_2435_);
v___x_2476_ = l_Array_append___redArg(v_fst_2430_, v_snd_2437_);
lean_dec(v_snd_2437_);
return v___x_2476_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(lean_object* v___x_2483_, lean_object* v_edited_2484_, lean_object* v_b_2485_){
_start:
{
lean_object* v_fst_2486_; lean_object* v_snd_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2506_; 
v_fst_2486_ = lean_ctor_get(v_b_2485_, 0);
v_snd_2487_ = lean_ctor_get(v_b_2485_, 1);
v_isSharedCheck_2506_ = !lean_is_exclusive(v_b_2485_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2489_ = v_b_2485_;
v_isShared_2490_ = v_isSharedCheck_2506_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_snd_2487_);
lean_inc(v_fst_2486_);
lean_dec(v_b_2485_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2506_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
uint8_t v___x_2491_; 
v___x_2491_ = lean_nat_dec_lt(v_snd_2487_, v___x_2483_);
if (v___x_2491_ == 0)
{
lean_object* v___x_2493_; 
if (v_isShared_2490_ == 0)
{
v___x_2493_ = v___x_2489_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_fst_2486_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v_snd_2487_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
else
{
uint8_t v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2499_; 
v___x_2495_ = 0;
v___x_2496_ = lean_array_fget_borrowed(v_edited_2484_, v_snd_2487_);
v___x_2497_ = lean_box(v___x_2495_);
lean_inc(v___x_2496_);
if (v_isShared_2490_ == 0)
{
lean_ctor_set(v___x_2489_, 1, v___x_2496_);
lean_ctor_set(v___x_2489_, 0, v___x_2497_);
v___x_2499_ = v___x_2489_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v___x_2497_);
lean_ctor_set(v_reuseFailAlloc_2505_, 1, v___x_2496_);
v___x_2499_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2500_ = lean_array_push(v_fst_2486_, v___x_2499_);
v___x_2501_ = lean_unsigned_to_nat(1u);
v___x_2502_ = lean_nat_add(v_snd_2487_, v___x_2501_);
lean_dec(v_snd_2487_);
v___x_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2500_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v_b_2485_ = v___x_2503_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___boxed(lean_object* v___x_2507_, lean_object* v_edited_2508_, lean_object* v_b_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(v___x_2507_, v_edited_2508_, v_b_2509_);
lean_dec_ref(v_edited_2508_);
lean_dec(v___x_2507_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(size_t v_sz_2511_, size_t v_i_2512_, lean_object* v_bs_2513_){
_start:
{
uint8_t v___x_2514_; 
v___x_2514_ = lean_usize_dec_lt(v_i_2512_, v_sz_2511_);
if (v___x_2514_ == 0)
{
return v_bs_2513_;
}
else
{
lean_object* v_v_2515_; lean_object* v___x_2516_; lean_object* v_bs_x27_2517_; uint8_t v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; size_t v___x_2521_; size_t v___x_2522_; lean_object* v___x_2523_; 
v_v_2515_ = lean_array_uget(v_bs_2513_, v_i_2512_);
v___x_2516_ = lean_unsigned_to_nat(0u);
v_bs_x27_2517_ = lean_array_uset(v_bs_2513_, v_i_2512_, v___x_2516_);
v___x_2518_ = 1;
v___x_2519_ = lean_box(v___x_2518_);
v___x_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2519_);
lean_ctor_set(v___x_2520_, 1, v_v_2515_);
v___x_2521_ = ((size_t)1ULL);
v___x_2522_ = lean_usize_add(v_i_2512_, v___x_2521_);
v___x_2523_ = lean_array_uset(v_bs_x27_2517_, v_i_2512_, v___x_2520_);
v_i_2512_ = v___x_2522_;
v_bs_2513_ = v___x_2523_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7___boxed(lean_object* v_sz_2525_, lean_object* v_i_2526_, lean_object* v_bs_2527_){
_start:
{
size_t v_sz_boxed_2528_; size_t v_i_boxed_2529_; lean_object* v_res_2530_; 
v_sz_boxed_2528_ = lean_unbox_usize(v_sz_2525_);
lean_dec(v_sz_2525_);
v_i_boxed_2529_ = lean_unbox_usize(v_i_2526_);
lean_dec(v_i_2526_);
v_res_2530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_boxed_2528_, v_i_boxed_2529_, v_bs_2527_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(lean_object* v___x_2531_, lean_object* v_original_2532_, lean_object* v_b_2533_){
_start:
{
lean_object* v_fst_2534_; lean_object* v_snd_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2554_; 
v_fst_2534_ = lean_ctor_get(v_b_2533_, 0);
v_snd_2535_ = lean_ctor_get(v_b_2533_, 1);
v_isSharedCheck_2554_ = !lean_is_exclusive(v_b_2533_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2537_ = v_b_2533_;
v_isShared_2538_ = v_isSharedCheck_2554_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_snd_2535_);
lean_inc(v_fst_2534_);
lean_dec(v_b_2533_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2554_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
uint8_t v___x_2539_; 
v___x_2539_ = lean_nat_dec_lt(v_snd_2535_, v___x_2531_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2541_; 
if (v_isShared_2538_ == 0)
{
v___x_2541_ = v___x_2537_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_fst_2534_);
lean_ctor_set(v_reuseFailAlloc_2542_, 1, v_snd_2535_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
else
{
uint8_t v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2547_; 
v___x_2543_ = 1;
v___x_2544_ = lean_array_fget_borrowed(v_original_2532_, v_snd_2535_);
v___x_2545_ = lean_box(v___x_2543_);
lean_inc(v___x_2544_);
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 1, v___x_2544_);
lean_ctor_set(v___x_2537_, 0, v___x_2545_);
v___x_2547_ = v___x_2537_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2545_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v___x_2544_);
v___x_2547_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2548_ = lean_array_push(v_fst_2534_, v___x_2547_);
v___x_2549_ = lean_unsigned_to_nat(1u);
v___x_2550_ = lean_nat_add(v_snd_2535_, v___x_2549_);
lean_dec(v_snd_2535_);
v___x_2551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2548_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
v_b_2533_ = v___x_2551_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___boxed(lean_object* v___x_2555_, lean_object* v_original_2556_, lean_object* v_b_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(v___x_2555_, v_original_2556_, v_b_2557_);
lean_dec_ref(v_original_2556_);
lean_dec(v___x_2555_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(lean_object* v_original_2564_, lean_object* v_edited_2565_){
_start:
{
lean_object* v_i_2566_; lean_object* v___x_2567_; uint8_t v___x_2568_; 
v_i_2566_ = lean_unsigned_to_nat(0u);
v___x_2567_ = lean_array_get_size(v_original_2564_);
v___x_2568_ = lean_nat_dec_lt(v_i_2566_, v___x_2567_);
if (v___x_2568_ == 0)
{
size_t v_sz_2569_; size_t v___x_2570_; lean_object* v___x_2571_; 
lean_dec_ref(v_original_2564_);
v_sz_2569_ = lean_array_size(v_edited_2565_);
v___x_2570_ = ((size_t)0ULL);
v___x_2571_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_2569_, v___x_2570_, v_edited_2565_);
return v___x_2571_;
}
else
{
lean_object* v___x_2572_; uint8_t v___x_2573_; 
v___x_2572_ = lean_array_get_size(v_edited_2565_);
v___x_2573_ = lean_nat_dec_lt(v_i_2566_, v___x_2572_);
if (v___x_2573_ == 0)
{
size_t v_sz_2574_; size_t v___x_2575_; lean_object* v___x_2576_; 
lean_dec_ref(v_edited_2565_);
v_sz_2574_ = lean_array_size(v_original_2564_);
v___x_2575_ = ((size_t)0ULL);
v___x_2576_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_2574_, v___x_2575_, v_original_2564_);
return v___x_2576_;
}
else
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v_ds_2579_; lean_object* v___x_2580_; size_t v_sz_2581_; size_t v___x_2582_; lean_object* v___x_2583_; lean_object* v_snd_2584_; lean_object* v_fst_2585_; lean_object* v_fst_2586_; lean_object* v_snd_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2606_; 
lean_inc_ref(v_original_2564_);
v___x_2577_ = l_Array_toSubarray___redArg(v_original_2564_, v_i_2566_, v___x_2567_);
lean_inc_ref(v_edited_2565_);
v___x_2578_ = l_Array_toSubarray___redArg(v_edited_2565_, v_i_2566_, v___x_2572_);
v_ds_2579_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v___x_2577_, v___x_2578_);
v___x_2580_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__1));
v_sz_2581_ = lean_array_size(v_ds_2579_);
v___x_2582_ = ((size_t)0ULL);
v___x_2583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v_edited_2565_, v___x_2572_, v_original_2564_, v___x_2567_, v_ds_2579_, v_sz_2581_, v___x_2582_, v___x_2580_);
lean_dec_ref(v_ds_2579_);
v_snd_2584_ = lean_ctor_get(v___x_2583_, 1);
lean_inc(v_snd_2584_);
v_fst_2585_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_fst_2585_);
lean_dec_ref(v___x_2583_);
v_fst_2586_ = lean_ctor_get(v_snd_2584_, 0);
v_snd_2587_ = lean_ctor_get(v_snd_2584_, 1);
v_isSharedCheck_2606_ = !lean_is_exclusive(v_snd_2584_);
if (v_isSharedCheck_2606_ == 0)
{
v___x_2589_ = v_snd_2584_;
v_isShared_2590_ = v_isSharedCheck_2606_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_snd_2587_);
lean_inc(v_fst_2586_);
lean_dec(v_snd_2584_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2606_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 1, v_fst_2586_);
lean_ctor_set(v___x_2589_, 0, v_fst_2585_);
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v_fst_2585_);
lean_ctor_set(v_reuseFailAlloc_2605_, 1, v_fst_2586_);
v___x_2592_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
lean_object* v___x_2593_; lean_object* v_fst_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2603_; 
v___x_2593_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(v___x_2567_, v_original_2564_, v___x_2592_);
lean_dec_ref(v_original_2564_);
v_fst_2594_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2603_ == 0)
{
lean_object* v_unused_2604_; 
v_unused_2604_ = lean_ctor_get(v___x_2593_, 1);
lean_dec(v_unused_2604_);
v___x_2596_ = v___x_2593_;
v_isShared_2597_ = v_isSharedCheck_2603_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_fst_2594_);
lean_dec(v___x_2593_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2603_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 1, v_snd_2587_);
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_fst_2594_);
lean_ctor_set(v_reuseFailAlloc_2602_, 1, v_snd_2587_);
v___x_2599_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
lean_object* v___x_2600_; lean_object* v_fst_2601_; 
v___x_2600_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(v___x_2572_, v_edited_2565_, v___x_2599_);
lean_dec_ref(v_edited_2565_);
v_fst_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_fst_2601_);
lean_dec_ref(v___x_2600_);
return v_fst_2601_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(lean_object* v___x_2607_, uint8_t v_inSubst_2608_, lean_object* v___x_2609_, lean_object* v_____r_2610_, lean_object* v_wssIdx_2611_){
_start:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2612_ = lean_box(v_inSubst_2608_);
v___x_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2607_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
v___x_2614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2614_, 0, v_wssIdx_2611_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
v___x_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___x_2609_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v___x_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2615_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1___boxed(lean_object* v___x_2617_, lean_object* v_inSubst_2618_, lean_object* v___x_2619_, lean_object* v_____r_2620_, lean_object* v_wssIdx_2621_){
_start:
{
uint8_t v_inSubst_boxed_2622_; lean_object* v_res_2623_; 
v_inSubst_boxed_2622_ = lean_unbox(v_inSubst_2618_);
v_res_2623_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2617_, v_inSubst_boxed_2622_, v___x_2619_, v_____r_2620_, v_wssIdx_2621_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(lean_object* v_fst_2624_, uint8_t v___x_2625_, lean_object* v_fst_2626_, lean_object* v___x_2627_, lean_object* v_00___2628_){
_start:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2629_ = lean_box(v___x_2625_);
v___x_2630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2630_, 0, v_fst_2624_);
lean_ctor_set(v___x_2630_, 1, v___x_2629_);
v___x_2631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2631_, 0, v_fst_2626_);
lean_ctor_set(v___x_2631_, 1, v___x_2630_);
v___x_2632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2627_);
lean_ctor_set(v___x_2632_, 1, v___x_2631_);
v___x_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0___boxed(lean_object* v_fst_2634_, lean_object* v___x_2635_, lean_object* v_fst_2636_, lean_object* v___x_2637_, lean_object* v_00___2638_){
_start:
{
uint8_t v___x_9258__boxed_2639_; lean_object* v_res_2640_; 
v___x_9258__boxed_2639_ = lean_unbox(v___x_2635_);
v_res_2640_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2634_, v___x_9258__boxed_2639_, v_fst_2636_, v___x_2637_, v_00___2638_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(uint8_t v_inSubst_2641_, lean_object* v_snd_2642_, lean_object* v_fst_2643_, lean_object* v_____r_2644_, lean_object* v_withWs_2645_, lean_object* v_wssIdx_2646_){
_start:
{
lean_object* v_wss_x27Idx_2648_; uint8_t v___x_2654_; 
v___x_2654_ = lean_unbox(v_snd_2642_);
if (v___x_2654_ == 0)
{
v_wss_x27Idx_2648_ = v_fst_2643_;
goto v___jp_2647_;
}
else
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2655_ = lean_unsigned_to_nat(1u);
v___x_2656_ = lean_nat_add(v_fst_2643_, v___x_2655_);
lean_dec(v_fst_2643_);
v_wss_x27Idx_2648_ = v___x_2656_;
goto v___jp_2647_;
}
v___jp_2647_:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2649_ = lean_box(v_inSubst_2641_);
v___x_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2650_, 0, v_wss_x27Idx_2648_);
lean_ctor_set(v___x_2650_, 1, v___x_2649_);
v___x_2651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2651_, 0, v_wssIdx_2646_);
lean_ctor_set(v___x_2651_, 1, v___x_2650_);
v___x_2652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2652_, 0, v_withWs_2645_);
lean_ctor_set(v___x_2652_, 1, v___x_2651_);
v___x_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2653_, 0, v___x_2652_);
return v___x_2653_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2___boxed(lean_object* v_inSubst_2657_, lean_object* v_snd_2658_, lean_object* v_fst_2659_, lean_object* v_____r_2660_, lean_object* v_withWs_2661_, lean_object* v_wssIdx_2662_){
_start:
{
uint8_t v_inSubst_boxed_2663_; lean_object* v_res_2664_; 
v_inSubst_boxed_2663_ = lean_unbox(v_inSubst_2657_);
v_res_2664_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_boxed_2663_, v_snd_2658_, v_fst_2659_, v_____r_2660_, v_withWs_2661_, v_wssIdx_2662_);
lean_dec(v_snd_2658_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(lean_object* v_upperBound_2665_, lean_object* v_diff_2666_, lean_object* v_snd_2667_, lean_object* v_snd_2668_, lean_object* v_a_2669_, lean_object* v_b_2670_){
_start:
{
lean_object* v_a_2672_; lean_object* v___y_2677_; uint8_t v___x_2680_; 
v___x_2680_ = lean_nat_dec_lt(v_a_2669_, v_upperBound_2665_);
if (v___x_2680_ == 0)
{
lean_dec(v_a_2669_);
return v_b_2670_;
}
else
{
lean_object* v___x_2681_; lean_object* v_snd_2682_; lean_object* v_snd_2683_; lean_object* v_fst_2684_; lean_object* v_fst_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2825_; 
v___x_2681_ = lean_array_fget_borrowed(v_diff_2666_, v_a_2669_);
v_snd_2682_ = lean_ctor_get(v_b_2670_, 1);
lean_inc(v_snd_2682_);
v_snd_2683_ = lean_ctor_get(v_snd_2682_, 1);
lean_inc(v_snd_2683_);
v_fst_2684_ = lean_ctor_get(v___x_2681_, 0);
v_fst_2685_ = lean_ctor_get(v_b_2670_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v_b_2670_);
if (v_isSharedCheck_2825_ == 0)
{
lean_object* v_unused_2826_; 
v_unused_2826_ = lean_ctor_get(v_b_2670_, 1);
lean_dec(v_unused_2826_);
v___x_2687_ = v_b_2670_;
v_isShared_2688_ = v_isSharedCheck_2825_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_fst_2685_);
lean_dec(v_b_2670_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2825_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v_fst_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2823_; 
v_fst_2689_ = lean_ctor_get(v_snd_2682_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v_snd_2682_);
if (v_isSharedCheck_2823_ == 0)
{
lean_object* v_unused_2824_; 
v_unused_2824_ = lean_ctor_get(v_snd_2682_, 1);
lean_dec(v_unused_2824_);
v___x_2691_ = v_snd_2682_;
v_isShared_2692_ = v_isSharedCheck_2823_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_fst_2689_);
lean_dec(v_snd_2682_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2823_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v_fst_2693_; lean_object* v_snd_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2822_; 
v_fst_2693_ = lean_ctor_get(v_snd_2683_, 0);
v_snd_2694_ = lean_ctor_get(v_snd_2683_, 1);
v_isSharedCheck_2822_ = !lean_is_exclusive(v_snd_2683_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2696_ = v_snd_2683_;
v_isShared_2697_ = v_isSharedCheck_2822_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_snd_2694_);
lean_inc(v_fst_2693_);
lean_dec(v_snd_2683_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2822_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2698_; lean_object* v___y_2700_; lean_object* v___y_2715_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; uint8_t v___x_2726_; 
lean_inc(v___x_2681_);
v___x_2698_ = lean_array_push(v_fst_2685_, v___x_2681_);
v___x_2723_ = lean_unsigned_to_nat(1u);
v___x_2724_ = lean_nat_add(v_a_2669_, v___x_2723_);
v___x_2725_ = lean_array_get_size(v_diff_2666_);
v___x_2726_ = lean_nat_dec_lt(v___x_2724_, v___x_2725_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
lean_dec(v___x_2724_);
lean_del_object(v___x_2696_);
lean_del_object(v___x_2691_);
lean_del_object(v___x_2687_);
v___x_2727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2727_, 0, v_fst_2693_);
lean_ctor_set(v___x_2727_, 1, v_snd_2694_);
v___x_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2728_, 0, v_fst_2689_);
lean_ctor_set(v___x_2728_, 1, v___x_2727_);
v___x_2729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2698_);
lean_ctor_set(v___x_2729_, 1, v___x_2728_);
v_a_2672_ = v___x_2729_;
goto v___jp_2671_;
}
else
{
lean_object* v___x_2730_; lean_object* v_fst_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2820_; 
v___x_2730_ = lean_array_fget(v_diff_2666_, v___x_2724_);
lean_dec(v___x_2724_);
v_fst_2731_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2820_ == 0)
{
lean_object* v_unused_2821_; 
v_unused_2821_ = lean_ctor_get(v___x_2730_, 1);
lean_dec(v_unused_2821_);
v___x_2733_ = v___x_2730_;
v_isShared_2734_ = v_isSharedCheck_2820_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_fst_2731_);
lean_dec(v___x_2730_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2820_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
uint8_t v_inSubst_2735_; lean_object* v___y_2737_; lean_object* v___x_2746_; uint8_t v___x_2747_; 
v_inSubst_2735_ = 0;
v___x_2746_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2747_ = lean_unbox(v_fst_2684_);
switch(v___x_2747_)
{
case 0:
{
uint8_t v___x_2748_; 
lean_del_object(v___x_2696_);
lean_del_object(v___x_2691_);
lean_del_object(v___x_2687_);
v___x_2748_ = lean_unbox(v_fst_2731_);
switch(v___x_2748_)
{
case 0:
{
lean_object* v___x_2749_; lean_object* v___x_2751_; 
v___x_2749_ = lean_array_get_borrowed(v___x_2746_, v_snd_2667_, v_fst_2693_);
lean_inc(v___x_2749_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 1, v___x_2749_);
v___x_2751_ = v___x_2733_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v_fst_2731_);
lean_ctor_set(v_reuseFailAlloc_2757_, 1, v___x_2749_);
v___x_2751_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2752_ = lean_array_push(v___x_2698_, v___x_2751_);
v___x_2753_ = lean_nat_add(v_fst_2693_, v___x_2723_);
lean_dec(v_fst_2693_);
v___x_2754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2753_);
lean_ctor_set(v___x_2754_, 1, v_snd_2694_);
v___x_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2755_, 0, v_fst_2689_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
v___x_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2752_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
v_a_2672_ = v___x_2756_;
goto v___jp_2671_;
}
}
case 1:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
lean_del_object(v___x_2733_);
lean_dec(v_fst_2731_);
lean_dec(v_snd_2694_);
v___x_2758_ = lean_box(0);
v___x_2759_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2693_, v___x_2680_, v_fst_2689_, v___x_2698_, v___x_2758_);
v___y_2677_ = v___x_2759_;
goto v___jp_2676_;
}
default: 
{
lean_object* v___x_2760_; uint8_t v___x_2761_; 
lean_dec(v_fst_2731_);
v___x_2760_ = lean_array_get_borrowed(v___x_2746_, v_snd_2667_, v_fst_2693_);
v___x_2761_ = lean_unbox(v_snd_2694_);
if (v___x_2761_ == 0)
{
lean_object* v___x_2763_; 
lean_inc(v___x_2760_);
lean_inc(v_fst_2684_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 1, v___x_2760_);
lean_ctor_set(v___x_2733_, 0, v_fst_2684_);
v___x_2763_ = v___x_2733_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_fst_2684_);
lean_ctor_set(v_reuseFailAlloc_2766_, 1, v___x_2760_);
v___x_2763_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2764_ = lean_mk_empty_array_with_capacity(v___x_2723_);
v___x_2765_ = lean_array_push(v___x_2764_, v___x_2763_);
v___y_2737_ = v___x_2765_;
goto v___jp_2736_;
}
}
else
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
lean_del_object(v___x_2733_);
v___x_2767_ = lean_array_get_borrowed(v___x_2746_, v_snd_2668_, v_fst_2689_);
lean_inc(v___x_2760_);
lean_inc(v___x_2767_);
v___x_2768_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2767_, v___x_2760_);
v___y_2737_ = v___x_2768_;
goto v___jp_2736_;
}
}
}
}
case 1:
{
uint8_t v___x_2769_; 
lean_del_object(v___x_2696_);
lean_del_object(v___x_2691_);
lean_del_object(v___x_2687_);
v___x_2769_ = lean_unbox(v_fst_2731_);
switch(v___x_2769_)
{
case 0:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
lean_del_object(v___x_2733_);
lean_dec(v_fst_2731_);
lean_dec(v_snd_2694_);
v___x_2770_ = lean_box(0);
v___x_2771_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2693_, v___x_2680_, v_fst_2689_, v___x_2698_, v___x_2770_);
v___y_2677_ = v___x_2771_;
goto v___jp_2676_;
}
case 1:
{
lean_object* v___x_2772_; lean_object* v___x_2774_; 
v___x_2772_ = lean_array_get_borrowed(v___x_2746_, v_snd_2668_, v_fst_2689_);
lean_inc(v___x_2772_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 1, v___x_2772_);
v___x_2774_ = v___x_2733_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_fst_2731_);
lean_ctor_set(v_reuseFailAlloc_2780_, 1, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2775_ = lean_array_push(v___x_2698_, v___x_2774_);
v___x_2776_ = lean_nat_add(v_fst_2689_, v___x_2723_);
lean_dec(v_fst_2689_);
v___x_2777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2777_, 0, v_fst_2693_);
lean_ctor_set(v___x_2777_, 1, v_snd_2694_);
v___x_2778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2778_, 0, v___x_2776_);
lean_ctor_set(v___x_2778_, 1, v___x_2777_);
v___x_2779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2775_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
v_a_2672_ = v___x_2779_;
goto v___jp_2671_;
}
}
default: 
{
uint8_t v___x_2784_; 
lean_dec(v_fst_2731_);
v___x_2784_ = lean_unbox(v_snd_2694_);
if (v___x_2784_ == 0)
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; uint8_t v___x_2789_; 
v___x_2785_ = lean_array_get_borrowed(v___x_2746_, v_snd_2668_, v_fst_2689_);
v___x_2786_ = lean_unsigned_to_nat(0u);
v___x_2787_ = lean_string_utf8_byte_size(v___x_2785_);
lean_inc(v___x_2785_);
v___x_2788_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2785_);
lean_ctor_set(v___x_2788_, 1, v___x_2786_);
lean_ctor_set(v___x_2788_, 2, v___x_2787_);
v___x_2789_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_2788_);
lean_dec_ref(v___x_2788_);
if (v___x_2789_ == 0)
{
lean_object* v___x_2791_; 
lean_inc(v___x_2785_);
lean_inc(v_fst_2684_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 1, v___x_2785_);
lean_ctor_set(v___x_2733_, 0, v_fst_2684_);
v___x_2791_ = v___x_2733_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_fst_2684_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v___x_2785_);
v___x_2791_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2792_ = lean_array_push(v___x_2698_, v___x_2791_);
v___x_2793_ = lean_nat_add(v_fst_2689_, v___x_2723_);
lean_dec(v_fst_2689_);
v___x_2794_ = lean_box(0);
v___x_2795_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2735_, v_snd_2694_, v_fst_2693_, v___x_2794_, v___x_2792_, v___x_2793_);
lean_dec(v_snd_2694_);
v___y_2677_ = v___x_2795_;
goto v___jp_2676_;
}
}
else
{
lean_del_object(v___x_2733_);
goto v___jp_2781_;
}
}
else
{
lean_del_object(v___x_2733_);
goto v___jp_2781_;
}
v___jp_2781_:
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2782_ = lean_box(0);
v___x_2783_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2735_, v_snd_2694_, v_fst_2693_, v___x_2782_, v___x_2698_, v_fst_2689_);
lean_dec(v_snd_2694_);
v___y_2677_ = v___x_2783_;
goto v___jp_2676_;
}
}
}
}
default: 
{
uint8_t v___x_2797_; 
v___x_2797_ = lean_unbox(v_fst_2731_);
if (v___x_2797_ == 1)
{
lean_object* v___x_2798_; lean_object* v___x_2799_; uint8_t v___x_2800_; 
v___x_2798_ = lean_array_get_borrowed(v___x_2746_, v_snd_2668_, v_fst_2689_);
v___x_2799_ = lean_array_get_size(v_snd_2667_);
v___x_2800_ = lean_nat_dec_lt(v_fst_2693_, v___x_2799_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2802_; 
lean_inc(v___x_2798_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 1, v___x_2798_);
v___x_2802_ = v___x_2733_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_fst_2731_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v___x_2798_);
v___x_2802_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
v___x_2803_ = lean_mk_empty_array_with_capacity(v___x_2723_);
v___x_2804_ = lean_array_push(v___x_2803_, v___x_2802_);
v___y_2700_ = v___x_2804_;
goto v___jp_2699_;
}
}
else
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
lean_del_object(v___x_2733_);
lean_dec(v_fst_2731_);
v___x_2806_ = lean_array_fget_borrowed(v_snd_2667_, v_fst_2693_);
lean_inc(v___x_2806_);
lean_inc(v___x_2798_);
v___x_2807_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2798_, v___x_2806_);
v___y_2700_ = v___x_2807_;
goto v___jp_2699_;
}
}
else
{
lean_object* v___x_2808_; lean_object* v___x_2809_; uint8_t v___x_2810_; 
lean_dec(v_fst_2731_);
lean_del_object(v___x_2696_);
lean_del_object(v___x_2691_);
lean_del_object(v___x_2687_);
v___x_2808_ = lean_array_get_borrowed(v___x_2746_, v_snd_2667_, v_fst_2693_);
v___x_2809_ = lean_array_get_size(v_snd_2668_);
v___x_2810_ = lean_nat_dec_lt(v_fst_2689_, v___x_2809_);
if (v___x_2810_ == 0)
{
uint8_t v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2814_; 
v___x_2811_ = 0;
v___x_2812_ = lean_box(v___x_2811_);
lean_inc(v___x_2808_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 1, v___x_2808_);
lean_ctor_set(v___x_2733_, 0, v___x_2812_);
v___x_2814_ = v___x_2733_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v___x_2812_);
lean_ctor_set(v_reuseFailAlloc_2817_, 1, v___x_2808_);
v___x_2814_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2815_ = lean_mk_empty_array_with_capacity(v___x_2723_);
v___x_2816_ = lean_array_push(v___x_2815_, v___x_2814_);
v___y_2715_ = v___x_2816_;
goto v___jp_2714_;
}
}
else
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
lean_del_object(v___x_2733_);
v___x_2818_ = lean_array_fget_borrowed(v_snd_2668_, v_fst_2689_);
lean_inc(v___x_2808_);
lean_inc(v___x_2818_);
v___x_2819_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2818_, v___x_2808_);
v___y_2715_ = v___x_2819_;
goto v___jp_2714_;
}
}
}
}
v___jp_2736_:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; uint8_t v___x_2740_; 
v___x_2738_ = l_Array_append___redArg(v___x_2698_, v___y_2737_);
lean_dec_ref(v___y_2737_);
v___x_2739_ = lean_nat_add(v_fst_2693_, v___x_2723_);
lean_dec(v_fst_2693_);
v___x_2740_ = lean_unbox(v_snd_2694_);
lean_dec(v_snd_2694_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2741_ = lean_box(0);
v___x_2742_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2739_, v_inSubst_2735_, v___x_2738_, v___x_2741_, v_fst_2689_);
v___y_2677_ = v___x_2742_;
goto v___jp_2676_;
}
else
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2743_ = lean_nat_add(v_fst_2689_, v___x_2723_);
lean_dec(v_fst_2689_);
v___x_2744_ = lean_box(0);
v___x_2745_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2739_, v_inSubst_2735_, v___x_2738_, v___x_2744_, v___x_2743_);
v___y_2677_ = v___x_2745_;
goto v___jp_2676_;
}
}
}
}
v___jp_2699_:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2706_; 
v___x_2701_ = l_Array_append___redArg(v___x_2698_, v___y_2700_);
lean_dec_ref(v___y_2700_);
v___x_2702_ = lean_unsigned_to_nat(1u);
v___x_2703_ = lean_nat_add(v_fst_2689_, v___x_2702_);
lean_dec(v_fst_2689_);
v___x_2704_ = lean_nat_add(v_fst_2693_, v___x_2702_);
lean_dec(v_fst_2693_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v___x_2704_);
v___x_2706_ = v___x_2696_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2704_);
lean_ctor_set(v_reuseFailAlloc_2713_, 1, v_snd_2694_);
v___x_2706_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
lean_object* v___x_2708_; 
if (v_isShared_2692_ == 0)
{
lean_ctor_set(v___x_2691_, 1, v___x_2706_);
lean_ctor_set(v___x_2691_, 0, v___x_2703_);
v___x_2708_ = v___x_2691_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2703_);
lean_ctor_set(v_reuseFailAlloc_2712_, 1, v___x_2706_);
v___x_2708_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
lean_object* v___x_2710_; 
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 1, v___x_2708_);
lean_ctor_set(v___x_2687_, 0, v___x_2701_);
v___x_2710_ = v___x_2687_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2701_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v___x_2708_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
v_a_2672_ = v___x_2710_;
goto v___jp_2671_;
}
}
}
}
v___jp_2714_:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2716_ = l_Array_append___redArg(v___x_2698_, v___y_2715_);
lean_dec_ref(v___y_2715_);
v___x_2717_ = lean_unsigned_to_nat(1u);
v___x_2718_ = lean_nat_add(v_fst_2689_, v___x_2717_);
lean_dec(v_fst_2689_);
v___x_2719_ = lean_nat_add(v_fst_2693_, v___x_2717_);
lean_dec(v_fst_2693_);
v___x_2720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
lean_ctor_set(v___x_2720_, 1, v_snd_2694_);
v___x_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2718_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2716_);
lean_ctor_set(v___x_2722_, 1, v___x_2721_);
v_a_2672_ = v___x_2722_;
goto v___jp_2671_;
}
}
}
}
}
v___jp_2671_:
{
lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2673_ = lean_unsigned_to_nat(1u);
v___x_2674_ = lean_nat_add(v_a_2669_, v___x_2673_);
lean_dec(v_a_2669_);
v_a_2669_ = v___x_2674_;
v_b_2670_ = v_a_2672_;
goto _start;
}
v___jp_2676_:
{
if (lean_obj_tag(v___y_2677_) == 0)
{
lean_object* v_a_2678_; 
lean_dec(v_a_2669_);
v_a_2678_ = lean_ctor_get(v___y_2677_, 0);
lean_inc(v_a_2678_);
lean_dec_ref(v___y_2677_);
return v_a_2678_;
}
else
{
lean_object* v_a_2679_; 
v_a_2679_ = lean_ctor_get(v___y_2677_, 0);
lean_inc(v_a_2679_);
lean_dec_ref(v___y_2677_);
v_a_2672_ = v_a_2679_;
goto v___jp_2671_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___boxed(lean_object* v_upperBound_2827_, lean_object* v_diff_2828_, lean_object* v_snd_2829_, lean_object* v_snd_2830_, lean_object* v_a_2831_, lean_object* v_b_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2827_, v_diff_2828_, v_snd_2829_, v_snd_2830_, v_a_2831_, v_b_2832_);
lean_dec_ref(v_snd_2830_);
lean_dec_ref(v_snd_2829_);
lean_dec_ref(v_diff_2828_);
lean_dec(v_upperBound_2827_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(lean_object* v_s_2844_, lean_object* v_s_x27_2845_){
_start:
{
lean_object* v___x_2846_; lean_object* v_fst_2847_; lean_object* v_snd_2848_; lean_object* v___x_2849_; lean_object* v_fst_2850_; lean_object* v_snd_2851_; lean_object* v_diff_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v_fst_2857_; lean_object* v___x_2858_; size_t v_sz_2859_; size_t v___x_2860_; lean_object* v___x_2861_; 
v___x_2846_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_2844_);
v_fst_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_fst_2847_);
v_snd_2848_ = lean_ctor_get(v___x_2846_, 1);
lean_inc(v_snd_2848_);
lean_dec_ref(v___x_2846_);
v___x_2849_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_x27_2845_);
v_fst_2850_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_fst_2850_);
v_snd_2851_ = lean_ctor_get(v___x_2849_, 1);
lean_inc(v_snd_2851_);
lean_dec_ref(v___x_2849_);
v_diff_2852_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(v_fst_2847_, v_fst_2850_);
v___x_2853_ = lean_unsigned_to_nat(0u);
v___x_2854_ = lean_array_get_size(v_diff_2852_);
v___x_2855_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__2));
v___x_2856_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v___x_2854_, v_diff_2852_, v_snd_2851_, v_snd_2848_, v___x_2853_, v___x_2855_);
lean_dec(v_snd_2848_);
lean_dec(v_snd_2851_);
lean_dec_ref(v_diff_2852_);
v_fst_2857_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_fst_2857_);
lean_dec_ref(v___x_2856_);
v___x_2858_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_fst_2857_);
lean_dec(v_fst_2857_);
v_sz_2859_ = lean_array_size(v___x_2858_);
v___x_2860_ = ((size_t)0ULL);
v___x_2861_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_2859_, v___x_2860_, v___x_2858_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___boxed(lean_object* v_s_2862_, lean_object* v_s_x27_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_2862_, v_s_x27_2863_);
lean_dec_ref(v_s_x27_2863_);
lean_dec_ref(v_s_2862_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(lean_object* v_upperBound_2865_, lean_object* v_diff_2866_, lean_object* v_snd_2867_, lean_object* v_snd_2868_, lean_object* v_inst_2869_, lean_object* v_R_2870_, lean_object* v_a_2871_, lean_object* v_b_2872_, lean_object* v_c_2873_){
_start:
{
lean_object* v___x_2874_; 
v___x_2874_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2865_, v_diff_2866_, v_snd_2867_, v_snd_2868_, v_a_2871_, v_b_2872_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___boxed(lean_object* v_upperBound_2875_, lean_object* v_diff_2876_, lean_object* v_snd_2877_, lean_object* v_snd_2878_, lean_object* v_inst_2879_, lean_object* v_R_2880_, lean_object* v_a_2881_, lean_object* v_b_2882_, lean_object* v_c_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(v_upperBound_2875_, v_diff_2876_, v_snd_2877_, v_snd_2878_, v_inst_2879_, v_R_2880_, v_a_2881_, v_b_2882_, v_c_2883_);
lean_dec_ref(v_snd_2878_);
lean_dec_ref(v_snd_2877_);
lean_dec_ref(v_diff_2876_);
lean_dec(v_upperBound_2875_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4(lean_object* v_as_2885_, lean_object* v_as_x27_2886_, lean_object* v_b_2887_, lean_object* v_a_2888_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(v_as_x27_2886_, v_b_2887_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___boxed(lean_object* v_as_2890_, lean_object* v_as_x27_2891_, lean_object* v_b_2892_, lean_object* v_a_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4(v_as_2890_, v_as_x27_2891_, v_b_2892_, v_a_2893_);
lean_dec(v_as_2890_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7(lean_object* v_lsize_2895_, lean_object* v_rsize_2896_, lean_object* v_histogram_2897_, lean_object* v_index_2898_, lean_object* v_val_2899_){
_start:
{
lean_object* v___x_2900_; 
v___x_2900_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(v_histogram_2897_, v_index_2898_, v_val_2899_);
return v___x_2900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___boxed(lean_object* v_lsize_2901_, lean_object* v_rsize_2902_, lean_object* v_histogram_2903_, lean_object* v_index_2904_, lean_object* v_val_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7(v_lsize_2901_, v_rsize_2902_, v_histogram_2903_, v_index_2904_, v_val_2905_);
lean_dec(v_rsize_2902_);
lean_dec(v_lsize_2901_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8(lean_object* v_upperBound_2907_, lean_object* v___x_2908_, lean_object* v_fst_2909_, lean_object* v___x_2910_, lean_object* v_inst_2911_, lean_object* v_R_2912_, lean_object* v_a_2913_, lean_object* v_b_2914_, lean_object* v_c_2915_){
_start:
{
lean_object* v___x_2916_; 
v___x_2916_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(v_upperBound_2907_, v___x_2908_, v_fst_2909_, v___x_2910_, v_a_2913_, v_b_2914_);
return v___x_2916_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___boxed(lean_object* v_upperBound_2917_, lean_object* v___x_2918_, lean_object* v_fst_2919_, lean_object* v___x_2920_, lean_object* v_inst_2921_, lean_object* v_R_2922_, lean_object* v_a_2923_, lean_object* v_b_2924_, lean_object* v_c_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8(v_upperBound_2917_, v___x_2918_, v_fst_2919_, v___x_2920_, v_inst_2921_, v_R_2922_, v_a_2923_, v_b_2924_, v_c_2925_);
lean_dec(v___x_2920_);
lean_dec_ref(v_fst_2919_);
lean_dec(v___x_2918_);
lean_dec(v_upperBound_2917_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9(lean_object* v_lsize_2927_, lean_object* v_rsize_2928_, lean_object* v_histogram_2929_, lean_object* v_index_2930_, lean_object* v_val_2931_){
_start:
{
lean_object* v___x_2932_; 
v___x_2932_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(v_histogram_2929_, v_index_2930_, v_val_2931_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___boxed(lean_object* v_lsize_2933_, lean_object* v_rsize_2934_, lean_object* v_histogram_2935_, lean_object* v_index_2936_, lean_object* v_val_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9(v_lsize_2933_, v_rsize_2934_, v_histogram_2935_, v_index_2936_, v_val_2937_);
lean_dec(v_rsize_2934_);
lean_dec(v_lsize_2933_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10(lean_object* v_upperBound_2939_, lean_object* v_fst_2940_, lean_object* v___x_2941_, lean_object* v_fst_2942_, lean_object* v_inst_2943_, lean_object* v_R_2944_, lean_object* v_a_2945_, lean_object* v_b_2946_, lean_object* v_c_2947_){
_start:
{
lean_object* v___x_2948_; 
v___x_2948_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(v_upperBound_2939_, v_fst_2940_, v___x_2941_, v_fst_2942_, v_a_2945_, v_b_2946_);
return v___x_2948_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___boxed(lean_object* v_upperBound_2949_, lean_object* v_fst_2950_, lean_object* v___x_2951_, lean_object* v_fst_2952_, lean_object* v_inst_2953_, lean_object* v_R_2954_, lean_object* v_a_2955_, lean_object* v_b_2956_, lean_object* v_c_2957_){
_start:
{
lean_object* v_res_2958_; 
v_res_2958_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10(v_upperBound_2949_, v_fst_2950_, v___x_2951_, v_fst_2952_, v_inst_2953_, v_R_2954_, v_a_2955_, v_b_2956_, v_c_2957_);
lean_dec_ref(v_fst_2952_);
lean_dec(v___x_2951_);
lean_dec_ref(v_fst_2950_);
lean_dec(v_upperBound_2949_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11(lean_object* v_00_u03b2_2959_, lean_object* v_m_2960_, lean_object* v_a_2961_){
_start:
{
lean_object* v___x_2962_; 
v___x_2962_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_m_2960_, v_a_2961_);
return v___x_2962_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___boxed(lean_object* v_00_u03b2_2963_, lean_object* v_m_2964_, lean_object* v_a_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11(v_00_u03b2_2963_, v_m_2964_, v_a_2965_);
lean_dec_ref(v_a_2965_);
lean_dec_ref(v_m_2964_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12(lean_object* v_00_u03b2_2967_, lean_object* v_m_2968_, lean_object* v_a_2969_, lean_object* v_b_2970_){
_start:
{
lean_object* v___x_2971_; 
v___x_2971_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_m_2968_, v_a_2969_, v_b_2970_);
return v___x_2971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14(lean_object* v_inst_2972_, lean_object* v_R_2973_, lean_object* v_a_2974_, lean_object* v_b_2975_){
_start:
{
lean_object* v___x_2976_; 
v___x_2976_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v_a_2974_, v_b_2975_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20(lean_object* v_00_u03b2_2977_, lean_object* v_a_2978_, lean_object* v_x_2979_){
_start:
{
lean_object* v___x_2980_; 
v___x_2980_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(v_a_2978_, v_x_2979_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___boxed(lean_object* v_00_u03b2_2981_, lean_object* v_a_2982_, lean_object* v_x_2983_){
_start:
{
lean_object* v_res_2984_; 
v_res_2984_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20(v_00_u03b2_2981_, v_a_2982_, v_x_2983_);
lean_dec(v_x_2983_);
lean_dec_ref(v_a_2982_);
return v_res_2984_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22(lean_object* v_00_u03b2_2985_, lean_object* v_a_2986_, lean_object* v_x_2987_){
_start:
{
uint8_t v___x_2988_; 
v___x_2988_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(v_a_2986_, v_x_2987_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___boxed(lean_object* v_00_u03b2_2989_, lean_object* v_a_2990_, lean_object* v_x_2991_){
_start:
{
uint8_t v_res_2992_; lean_object* v_r_2993_; 
v_res_2992_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22(v_00_u03b2_2989_, v_a_2990_, v_x_2991_);
lean_dec(v_x_2991_);
lean_dec_ref(v_a_2990_);
v_r_2993_ = lean_box(v_res_2992_);
return v_r_2993_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23(lean_object* v_00_u03b2_2994_, lean_object* v_data_2995_){
_start:
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23___redArg(v_data_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24(lean_object* v_00_u03b2_2997_, lean_object* v_a_2998_, lean_object* v_b_2999_, lean_object* v_x_3000_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(v_a_2998_, v_b_2999_, v_x_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28(lean_object* v_00_u03b2_3002_, lean_object* v_i_3003_, lean_object* v_source_3004_, lean_object* v_target_3005_){
_start:
{
lean_object* v___x_3006_; 
v___x_3006_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28___redArg(v_i_3003_, v_source_3004_, v_target_3005_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_3007_, lean_object* v_x_3008_, lean_object* v_x_3009_){
_start:
{
lean_object* v___x_3010_; 
v___x_3010_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29___redArg(v_x_3008_, v_x_3009_);
return v___x_3010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(lean_object* v_s_3011_){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; 
v___x_3012_ = lean_string_data(v_s_3011_);
v___x_3013_ = lean_array_mk(v___x_3012_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(lean_object* v_s_3014_, lean_object* v_s_x27_3015_){
_start:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3016_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3014_);
v___x_3017_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3015_);
v___x_3018_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3016_, v___x_3017_);
v___x_3019_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_3018_);
lean_dec_ref(v___x_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(lean_object* v_s_3020_, lean_object* v_s_x27_3021_){
_start:
{
uint8_t v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; uint8_t v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3022_ = 1;
v___x_3023_ = lean_box(v___x_3022_);
v___x_3024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3024_, 0, v___x_3023_);
lean_ctor_set(v___x_3024_, 1, v_s_3020_);
v___x_3025_ = 0;
v___x_3026_ = lean_box(v___x_3025_);
v___x_3027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3026_);
lean_ctor_set(v___x_3027_, 1, v_s_x27_3021_);
v___x_3028_ = lean_unsigned_to_nat(2u);
v___x_3029_ = lean_mk_empty_array_with_capacity(v___x_3028_);
v___x_3030_ = lean_array_push(v___x_3029_, v___x_3024_);
v___x_3031_ = lean_array_push(v___x_3030_, v___x_3027_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(lean_object* v_as_3032_, size_t v_i_3033_, size_t v_stop_3034_, lean_object* v_b_3035_){
_start:
{
lean_object* v___y_3037_; uint8_t v___x_3041_; 
v___x_3041_ = lean_usize_dec_eq(v_i_3033_, v_stop_3034_);
if (v___x_3041_ == 0)
{
lean_object* v___x_3042_; lean_object* v_fst_3043_; uint8_t v___x_3044_; uint8_t v___x_3045_; uint8_t v___x_3046_; 
v___x_3042_ = lean_array_uget_borrowed(v_as_3032_, v_i_3033_);
v_fst_3043_ = lean_ctor_get(v___x_3042_, 0);
v___x_3044_ = 2;
v___x_3045_ = lean_unbox(v_fst_3043_);
v___x_3046_ = l_Lean_Diff_instBEqAction_beq(v___x_3045_, v___x_3044_);
if (v___x_3046_ == 0)
{
lean_object* v___x_3047_; 
lean_inc(v___x_3042_);
v___x_3047_ = lean_array_push(v_b_3035_, v___x_3042_);
v___y_3037_ = v___x_3047_;
goto v___jp_3036_;
}
else
{
v___y_3037_ = v_b_3035_;
goto v___jp_3036_;
}
}
else
{
return v_b_3035_;
}
v___jp_3036_:
{
size_t v___x_3038_; size_t v___x_3039_; 
v___x_3038_ = ((size_t)1ULL);
v___x_3039_ = lean_usize_add(v_i_3033_, v___x_3038_);
v_i_3033_ = v___x_3039_;
v_b_3035_ = v___y_3037_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0___boxed(lean_object* v_as_3048_, lean_object* v_i_3049_, lean_object* v_stop_3050_, lean_object* v_b_3051_){
_start:
{
size_t v_i_boxed_3052_; size_t v_stop_boxed_3053_; lean_object* v_res_3054_; 
v_i_boxed_3052_ = lean_unbox_usize(v_i_3049_);
lean_dec(v_i_3049_);
v_stop_boxed_3053_ = lean_unbox_usize(v_stop_3050_);
lean_dec(v_stop_3050_);
v_res_3054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_as_3048_, v_i_boxed_3052_, v_stop_boxed_3053_, v_b_3051_);
lean_dec_ref(v_as_3048_);
return v_res_3054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff(lean_object* v_s_3055_, lean_object* v_s_x27_3056_, uint8_t v_granularity_3057_){
_start:
{
lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; uint8_t v___y_3062_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; 
switch(v_granularity_3057_)
{
case 0:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___y_3104_; uint8_t v___x_3110_; 
v___x_3101_ = lean_string_length(v_s_3055_);
v___x_3102_ = lean_string_length(v_s_x27_3056_);
v___x_3110_ = lean_nat_dec_le(v___x_3101_, v___x_3102_);
if (v___x_3110_ == 0)
{
v___y_3104_ = v___x_3102_;
goto v___jp_3103_;
}
else
{
v___y_3104_ = v___x_3101_;
goto v___jp_3103_;
}
v___jp_3103_:
{
lean_object* v___x_3105_; lean_object* v_maxCharDiffDistance_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; uint8_t v___x_3109_; 
v___x_3105_ = lean_unsigned_to_nat(5u);
v_maxCharDiffDistance_3106_ = lean_nat_div(v___y_3104_, v___x_3105_);
v___x_3107_ = lean_unsigned_to_nat(1u);
v___x_3108_ = lean_nat_shiftr(v___y_3104_, v___x_3107_);
lean_dec(v___y_3104_);
v___x_3109_ = lean_nat_dec_le(v___x_3101_, v___x_3102_);
if (v___x_3109_ == 0)
{
v___y_3081_ = v___x_3107_;
v___y_3082_ = v_maxCharDiffDistance_3106_;
v___y_3083_ = v___x_3108_;
v___y_3084_ = v___x_3101_;
goto v___jp_3080_;
}
else
{
v___y_3081_ = v___x_3107_;
v___y_3082_ = v_maxCharDiffDistance_3106_;
v___y_3083_ = v___x_3108_;
v___y_3084_ = v___x_3102_;
goto v___jp_3080_;
}
}
}
case 1:
{
lean_object* v___x_3111_; 
v___x_3111_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(v_s_3055_, v_s_x27_3056_);
return v___x_3111_;
}
case 2:
{
lean_object* v___x_3112_; 
v___x_3112_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3055_, v_s_x27_3056_);
lean_dec_ref(v_s_x27_3056_);
lean_dec_ref(v_s_3055_);
return v___x_3112_;
}
case 3:
{
lean_object* v___x_3113_; 
v___x_3113_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3055_, v_s_x27_3056_);
return v___x_3113_;
}
default: 
{
uint8_t v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
lean_dec_ref(v_s_3055_);
v___x_3114_ = 0;
v___x_3115_ = lean_box(v___x_3114_);
v___x_3116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3115_);
lean_ctor_set(v___x_3116_, 1, v_s_x27_3056_);
v___x_3117_ = lean_unsigned_to_nat(1u);
v___x_3118_ = lean_mk_empty_array_with_capacity(v___x_3117_);
v___x_3119_ = lean_array_push(v___x_3118_, v___x_3116_);
return v___x_3119_;
}
}
v___jp_3058_:
{
if (v___y_3062_ == 0)
{
uint8_t v___x_3063_; 
lean_dec_ref(v___y_3061_);
v___x_3063_ = lean_nat_dec_le(v___y_3059_, v___y_3060_);
lean_dec(v___y_3060_);
lean_dec(v___y_3059_);
if (v___x_3063_ == 0)
{
lean_object* v___x_3064_; 
v___x_3064_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3055_, v_s_x27_3056_);
return v___x_3064_;
}
else
{
lean_object* v___x_3065_; 
v___x_3065_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3055_, v_s_x27_3056_);
lean_dec_ref(v_s_x27_3056_);
lean_dec_ref(v_s_3055_);
return v___x_3065_;
}
}
else
{
size_t v_sz_3066_; size_t v___x_3067_; lean_object* v___x_3068_; 
lean_dec(v___y_3060_);
lean_dec(v___y_3059_);
lean_dec_ref(v_s_x27_3056_);
lean_dec_ref(v_s_3055_);
v_sz_3066_ = lean_array_size(v___y_3061_);
v___x_3067_ = ((size_t)0ULL);
v___x_3068_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_3066_, v___x_3067_, v___y_3061_);
return v___x_3068_;
}
}
v___jp_3069_:
{
lean_object* v_approxEditDistance_3074_; lean_object* v_charArrDiff_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; uint8_t v___x_3078_; 
v_approxEditDistance_3074_ = lean_array_get_size(v___y_3073_);
lean_dec_ref(v___y_3073_);
v_charArrDiff_3075_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v___y_3071_);
lean_dec_ref(v___y_3071_);
v___x_3076_ = lean_array_get_size(v_charArrDiff_3075_);
v___x_3077_ = lean_unsigned_to_nat(3u);
v___x_3078_ = lean_nat_dec_le(v___x_3076_, v___x_3077_);
if (v___x_3078_ == 0)
{
uint8_t v___x_3079_; 
v___x_3079_ = lean_nat_dec_le(v_approxEditDistance_3074_, v___y_3072_);
lean_dec(v___y_3072_);
v___y_3059_ = v_approxEditDistance_3074_;
v___y_3060_ = v___y_3070_;
v___y_3061_ = v_charArrDiff_3075_;
v___y_3062_ = v___x_3079_;
goto v___jp_3058_;
}
else
{
lean_dec(v___y_3072_);
v___y_3059_ = v_approxEditDistance_3074_;
v___y_3060_ = v___y_3070_;
v___y_3061_ = v_charArrDiff_3075_;
v___y_3062_ = v___x_3078_;
goto v___jp_3058_;
}
}
v___jp_3080_:
{
lean_object* v___x_3085_; lean_object* v_maxWordDiffDistance_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v_charDiffRaw_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; uint8_t v___x_3093_; 
v___x_3085_ = lean_nat_shiftr(v___y_3084_, v___y_3081_);
lean_dec(v___y_3084_);
v_maxWordDiffDistance_3086_ = lean_nat_add(v___y_3083_, v___x_3085_);
lean_dec(v___x_3085_);
lean_dec(v___y_3083_);
lean_inc_ref(v_s_3055_);
v___x_3087_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3055_);
lean_inc_ref(v_s_x27_3056_);
v___x_3088_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3056_);
v_charDiffRaw_3089_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3087_, v___x_3088_);
v___x_3090_ = lean_unsigned_to_nat(0u);
v___x_3091_ = lean_array_get_size(v_charDiffRaw_3089_);
v___x_3092_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0));
v___x_3093_ = lean_nat_dec_lt(v___x_3090_, v___x_3091_);
if (v___x_3093_ == 0)
{
v___y_3070_ = v_maxWordDiffDistance_3086_;
v___y_3071_ = v_charDiffRaw_3089_;
v___y_3072_ = v___y_3082_;
v___y_3073_ = v___x_3092_;
goto v___jp_3069_;
}
else
{
uint8_t v___x_3094_; 
v___x_3094_ = lean_nat_dec_le(v___x_3091_, v___x_3091_);
if (v___x_3094_ == 0)
{
if (v___x_3093_ == 0)
{
v___y_3070_ = v_maxWordDiffDistance_3086_;
v___y_3071_ = v_charDiffRaw_3089_;
v___y_3072_ = v___y_3082_;
v___y_3073_ = v___x_3092_;
goto v___jp_3069_;
}
else
{
size_t v___x_3095_; size_t v___x_3096_; lean_object* v___x_3097_; 
v___x_3095_ = ((size_t)0ULL);
v___x_3096_ = lean_usize_of_nat(v___x_3091_);
v___x_3097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3089_, v___x_3095_, v___x_3096_, v___x_3092_);
v___y_3070_ = v_maxWordDiffDistance_3086_;
v___y_3071_ = v_charDiffRaw_3089_;
v___y_3072_ = v___y_3082_;
v___y_3073_ = v___x_3097_;
goto v___jp_3069_;
}
}
else
{
size_t v___x_3098_; size_t v___x_3099_; lean_object* v___x_3100_; 
v___x_3098_ = ((size_t)0ULL);
v___x_3099_ = lean_usize_of_nat(v___x_3091_);
v___x_3100_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3089_, v___x_3098_, v___x_3099_, v___x_3092_);
v___y_3070_ = v_maxWordDiffDistance_3086_;
v___y_3071_ = v_charDiffRaw_3089_;
v___y_3072_ = v___y_3082_;
v___y_3073_ = v___x_3100_;
goto v___jp_3069_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff___boxed(lean_object* v_s_3120_, lean_object* v_s_x27_3121_, lean_object* v_granularity_3122_){
_start:
{
uint8_t v_granularity_boxed_3123_; lean_object* v_res_3124_; 
v_granularity_boxed_3123_ = lean_unbox(v_granularity_3122_);
v_res_3124_ = l_Lean_Meta_Hint_readableDiff(v_s_3120_, v_s_x27_3121_, v_granularity_boxed_3123_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(lean_object* v_as_3125_, size_t v_i_3126_, size_t v_stop_3127_, lean_object* v_b_3128_){
_start:
{
uint8_t v___x_3129_; 
v___x_3129_ = lean_usize_dec_eq(v_i_3126_, v_stop_3127_);
if (v___x_3129_ == 0)
{
lean_object* v___x_3130_; lean_object* v_snd_3131_; lean_object* v___x_3132_; size_t v___x_3133_; size_t v___x_3134_; 
v___x_3130_ = lean_array_uget_borrowed(v_as_3125_, v_i_3126_);
v_snd_3131_ = lean_ctor_get(v___x_3130_, 1);
v___x_3132_ = lean_string_append(v_b_3128_, v_snd_3131_);
v___x_3133_ = ((size_t)1ULL);
v___x_3134_ = lean_usize_add(v_i_3126_, v___x_3133_);
v_i_3126_ = v___x_3134_;
v_b_3128_ = v___x_3132_;
goto _start;
}
else
{
return v_b_3128_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0___boxed(lean_object* v_as_3136_, lean_object* v_i_3137_, lean_object* v_stop_3138_, lean_object* v_b_3139_){
_start:
{
size_t v_i_boxed_3140_; size_t v_stop_boxed_3141_; lean_object* v_res_3142_; 
v_i_boxed_3140_ = lean_unbox_usize(v_i_3137_);
lean_dec(v_i_3137_);
v_stop_boxed_3141_ = lean_unbox_usize(v_stop_3138_);
lean_dec(v_stop_3138_);
v_res_3142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v_as_3136_, v_i_boxed_3140_, v_stop_boxed_3141_, v_b_3139_);
lean_dec_ref(v_as_3136_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(lean_object* v_t_3143_, lean_object* v___y_3144_){
_start:
{
lean_object* v___x_3146_; lean_object* v_infoState_3147_; uint8_t v_enabled_3148_; 
v___x_3146_ = lean_st_ref_get(v___y_3144_);
v_infoState_3147_ = lean_ctor_get(v___x_3146_, 7);
lean_inc_ref(v_infoState_3147_);
lean_dec(v___x_3146_);
v_enabled_3148_ = lean_ctor_get_uint8(v_infoState_3147_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3147_);
if (v_enabled_3148_ == 0)
{
lean_object* v___x_3149_; lean_object* v___x_3150_; 
lean_dec_ref(v_t_3143_);
v___x_3149_ = lean_box(0);
v___x_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3150_, 0, v___x_3149_);
return v___x_3150_;
}
else
{
lean_object* v___x_3151_; lean_object* v_infoState_3152_; lean_object* v_env_3153_; lean_object* v_nextMacroScope_3154_; lean_object* v_ngen_3155_; lean_object* v_auxDeclNGen_3156_; lean_object* v_traceState_3157_; lean_object* v_cache_3158_; lean_object* v_messages_3159_; lean_object* v_snapshotTasks_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3182_; 
v___x_3151_ = lean_st_ref_take(v___y_3144_);
v_infoState_3152_ = lean_ctor_get(v___x_3151_, 7);
v_env_3153_ = lean_ctor_get(v___x_3151_, 0);
v_nextMacroScope_3154_ = lean_ctor_get(v___x_3151_, 1);
v_ngen_3155_ = lean_ctor_get(v___x_3151_, 2);
v_auxDeclNGen_3156_ = lean_ctor_get(v___x_3151_, 3);
v_traceState_3157_ = lean_ctor_get(v___x_3151_, 4);
v_cache_3158_ = lean_ctor_get(v___x_3151_, 5);
v_messages_3159_ = lean_ctor_get(v___x_3151_, 6);
v_snapshotTasks_3160_ = lean_ctor_get(v___x_3151_, 8);
v_isSharedCheck_3182_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3182_ == 0)
{
v___x_3162_ = v___x_3151_;
v_isShared_3163_ = v_isSharedCheck_3182_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_snapshotTasks_3160_);
lean_inc(v_infoState_3152_);
lean_inc(v_messages_3159_);
lean_inc(v_cache_3158_);
lean_inc(v_traceState_3157_);
lean_inc(v_auxDeclNGen_3156_);
lean_inc(v_ngen_3155_);
lean_inc(v_nextMacroScope_3154_);
lean_inc(v_env_3153_);
lean_dec(v___x_3151_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3182_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
uint8_t v_enabled_3164_; lean_object* v_assignment_3165_; lean_object* v_lazyAssignment_3166_; lean_object* v_trees_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3181_; 
v_enabled_3164_ = lean_ctor_get_uint8(v_infoState_3152_, sizeof(void*)*3);
v_assignment_3165_ = lean_ctor_get(v_infoState_3152_, 0);
v_lazyAssignment_3166_ = lean_ctor_get(v_infoState_3152_, 1);
v_trees_3167_ = lean_ctor_get(v_infoState_3152_, 2);
v_isSharedCheck_3181_ = !lean_is_exclusive(v_infoState_3152_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3169_ = v_infoState_3152_;
v_isShared_3170_ = v_isSharedCheck_3181_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_trees_3167_);
lean_inc(v_lazyAssignment_3166_);
lean_inc(v_assignment_3165_);
lean_dec(v_infoState_3152_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3181_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3171_; lean_object* v___x_3173_; 
v___x_3171_ = l_Lean_PersistentArray_push___redArg(v_trees_3167_, v_t_3143_);
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 2, v___x_3171_);
v___x_3173_ = v___x_3169_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_assignment_3165_);
lean_ctor_set(v_reuseFailAlloc_3180_, 1, v_lazyAssignment_3166_);
lean_ctor_set(v_reuseFailAlloc_3180_, 2, v___x_3171_);
lean_ctor_set_uint8(v_reuseFailAlloc_3180_, sizeof(void*)*3, v_enabled_3164_);
v___x_3173_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
lean_object* v___x_3175_; 
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 7, v___x_3173_);
v___x_3175_ = v___x_3162_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_env_3153_);
lean_ctor_set(v_reuseFailAlloc_3179_, 1, v_nextMacroScope_3154_);
lean_ctor_set(v_reuseFailAlloc_3179_, 2, v_ngen_3155_);
lean_ctor_set(v_reuseFailAlloc_3179_, 3, v_auxDeclNGen_3156_);
lean_ctor_set(v_reuseFailAlloc_3179_, 4, v_traceState_3157_);
lean_ctor_set(v_reuseFailAlloc_3179_, 5, v_cache_3158_);
lean_ctor_set(v_reuseFailAlloc_3179_, 6, v_messages_3159_);
lean_ctor_set(v_reuseFailAlloc_3179_, 7, v___x_3173_);
lean_ctor_set(v_reuseFailAlloc_3179_, 8, v_snapshotTasks_3160_);
v___x_3175_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3176_ = lean_st_ref_set(v___y_3144_, v___x_3175_);
v___x_3177_ = lean_box(0);
v___x_3178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
return v___x_3178_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg___boxed(lean_object* v_t_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
lean_object* v_res_3186_; 
v_res_3186_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3183_, v___y_3184_);
lean_dec(v___y_3184_);
return v_res_3186_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3187_ = lean_unsigned_to_nat(32u);
v___x_3188_ = lean_mk_empty_array_with_capacity(v___x_3187_);
v___x_3189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3188_);
return v___x_3189_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1(void){
_start:
{
size_t v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3190_ = ((size_t)5ULL);
v___x_3191_ = lean_unsigned_to_nat(0u);
v___x_3192_ = lean_unsigned_to_nat(32u);
v___x_3193_ = lean_mk_empty_array_with_capacity(v___x_3192_);
v___x_3194_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0);
v___x_3195_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3195_, 0, v___x_3194_);
lean_ctor_set(v___x_3195_, 1, v___x_3193_);
lean_ctor_set(v___x_3195_, 2, v___x_3191_);
lean_ctor_set(v___x_3195_, 3, v___x_3191_);
lean_ctor_set_usize(v___x_3195_, 4, v___x_3190_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(lean_object* v_t_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v___x_3200_; lean_object* v_infoState_3201_; uint8_t v_enabled_3202_; 
v___x_3200_ = lean_st_ref_get(v___y_3198_);
v_infoState_3201_ = lean_ctor_get(v___x_3200_, 7);
lean_inc_ref(v_infoState_3201_);
lean_dec(v___x_3200_);
v_enabled_3202_ = lean_ctor_get_uint8(v_infoState_3201_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3201_);
if (v_enabled_3202_ == 0)
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
lean_dec_ref(v_t_3196_);
v___x_3203_ = lean_box(0);
v___x_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
return v___x_3204_;
}
else
{
lean_object* v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3205_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1);
v___x_3206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3206_, 0, v_t_3196_);
lean_ctor_set(v___x_3206_, 1, v___x_3205_);
v___x_3207_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v___x_3206_, v___y_3198_);
return v___x_3207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___boxed(lean_object* v_t_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v_t_3208_, v___y_3209_, v___y_3210_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0(lean_object* v___x_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v___x_3215_; 
v___x_3215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3215_, 0, v___x_3213_);
lean_ctor_set(v___x_3215_, 1, v___y_3214_);
return v___x_3215_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3217_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__0));
v___x_3218_ = l_Lean_stringToMessageData(v___x_3217_);
return v___x_3218_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3220_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__2));
v___x_3221_ = l_Lean_stringToMessageData(v___x_3220_);
return v___x_3221_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29(void){
_start:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
v___x_3270_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__28));
v___x_3271_ = l_Lean_Json_mkObj(v___x_3270_);
return v___x_3271_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30(void){
_start:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3272_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29);
v___x_3273_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__19));
v___x_3274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3273_);
lean_ctor_set(v___x_3274_, 1, v___x_3272_);
return v___x_3274_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31(void){
_start:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3275_ = lean_box(0);
v___x_3276_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30);
v___x_3277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3276_);
lean_ctor_set(v___x_3277_, 1, v___x_3275_);
return v___x_3277_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33(void){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3280_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__32));
v___x_3281_ = l_Lean_MessageData_ofFormat(v___x_3280_);
return v___x_3281_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35(void){
_start:
{
lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3283_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__34));
v___x_3284_ = l_Lean_stringToMessageData(v___x_3283_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(lean_object* v_suggestions_3286_, uint8_t v_forceList_3287_, lean_object* v_codeActionPrefix_x3f_3288_, lean_object* v_ref_3289_, lean_object* v_as_3290_, size_t v_sz_3291_, size_t v_i_3292_, lean_object* v_b_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
lean_object* v_a_3298_; lean_object* v___y_3303_; lean_object* v___y_3307_; lean_object* v___y_3308_; lean_object* v___y_3309_; lean_object* v___y_3314_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; uint8_t v___x_3342_; 
v___x_3342_ = lean_usize_dec_lt(v_i_3292_, v_sz_3291_);
if (v___x_3342_ == 0)
{
lean_object* v___x_3343_; 
lean_dec(v_ref_3289_);
lean_dec(v_codeActionPrefix_x3f_3288_);
v___x_3343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3343_, 0, v_b_3293_);
return v___x_3343_;
}
else
{
lean_object* v_a_3344_; lean_object* v_span_x3f_3345_; lean_object* v___x_3346_; lean_object* v___y_3348_; uint8_t v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3381_; lean_object* v___y_3382_; uint8_t v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; uint8_t v___y_3434_; lean_object* v___y_3437_; lean_object* v___y_3438_; uint8_t v___y_3439_; lean_object* v___y_3440_; uint8_t v___y_3441_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3447_; lean_object* v_postInfo_x3f_3448_; lean_object* v___y_3449_; uint8_t v___y_3450_; lean_object* v___y_3451_; uint8_t v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3458_; lean_object* v___y_3459_; uint8_t v___y_3460_; lean_object* v___y_3461_; uint8_t v___y_3462_; lean_object* v___y_3463_; lean_object* v_edits_3464_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; uint8_t v___y_3474_; lean_object* v___y_3475_; lean_object* v_stop_3476_; uint8_t v___y_3477_; lean_object* v___y_3478_; lean_object* v_edits_3479_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; uint8_t v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; uint8_t v___y_3495_; lean_object* v___y_3496_; lean_object* v_edits_3497_; lean_object* v___y_3498_; lean_object* v___x_3522_; lean_object* v___y_3524_; lean_object* v___y_3525_; uint8_t v___y_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; uint8_t v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3569_; lean_object* v___y_3570_; uint8_t v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; uint8_t v___y_3574_; lean_object* v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3587_; 
v_a_3344_ = lean_array_uget_borrowed(v_as_3290_, v_i_3292_);
v_span_x3f_3345_ = lean_ctor_get(v_a_3344_, 1);
v___x_3346_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_3522_ = l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_;
if (lean_obj_tag(v_span_x3f_3345_) == 0)
{
lean_inc(v_ref_3289_);
v___y_3587_ = v_ref_3289_;
goto v___jp_3586_;
}
else
{
lean_object* v_val_3608_; 
v_val_3608_ = lean_ctor_get(v_span_x3f_3345_, 0);
lean_inc(v_val_3608_);
v___y_3587_ = v_val_3608_;
goto v___jp_3586_;
}
v___jp_3347_:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___f_3368_; 
lean_inc_ref(v___y_3353_);
v___x_3354_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson(v___y_3353_);
v___x_3355_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__9));
v___x_3356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3356_, 0, v___x_3355_);
lean_ctor_set(v___x_3356_, 1, v___x_3354_);
v___x_3357_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3358_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3358_, 0, v___y_3348_);
v___x_3359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3357_);
lean_ctor_set(v___x_3359_, 1, v___x_3358_);
v___x_3360_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3361_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3351_);
v___x_3362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3360_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
v___x_3363_ = lean_box(0);
v___x_3364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3362_);
lean_ctor_set(v___x_3364_, 1, v___x_3363_);
v___x_3365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3359_);
lean_ctor_set(v___x_3365_, 1, v___x_3364_);
v___x_3366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3356_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
v___x_3367_ = l_Lean_Json_mkObj(v___x_3366_);
v___f_3368_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3368_, 0, v___x_3367_);
if (v___y_3349_ == 0)
{
lean_object* v___x_3369_; 
v___x_3369_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString(v___y_3353_);
v___y_3322_ = v___f_3368_;
v___y_3323_ = v___y_3352_;
v___y_3324_ = v___y_3350_;
v___y_3325_ = v___x_3369_;
goto v___jp_3321_;
}
else
{
lean_object* v___x_3370_; lean_object* v___x_3371_; uint8_t v___x_3372_; 
v___x_3370_ = lean_unsigned_to_nat(0u);
v___x_3371_ = lean_array_get_size(v___y_3353_);
v___x_3372_ = lean_nat_dec_lt(v___x_3370_, v___x_3371_);
if (v___x_3372_ == 0)
{
lean_dec_ref(v___y_3353_);
v___y_3322_ = v___f_3368_;
v___y_3323_ = v___y_3352_;
v___y_3324_ = v___y_3350_;
v___y_3325_ = v___x_3346_;
goto v___jp_3321_;
}
else
{
uint8_t v___x_3373_; 
v___x_3373_ = lean_nat_dec_le(v___x_3371_, v___x_3371_);
if (v___x_3373_ == 0)
{
if (v___x_3372_ == 0)
{
lean_dec_ref(v___y_3353_);
v___y_3322_ = v___f_3368_;
v___y_3323_ = v___y_3352_;
v___y_3324_ = v___y_3350_;
v___y_3325_ = v___x_3346_;
goto v___jp_3321_;
}
else
{
size_t v___x_3374_; size_t v___x_3375_; lean_object* v___x_3376_; 
v___x_3374_ = ((size_t)0ULL);
v___x_3375_ = lean_usize_of_nat(v___x_3371_);
v___x_3376_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3353_, v___x_3374_, v___x_3375_, v___x_3346_);
lean_dec_ref(v___y_3353_);
v___y_3322_ = v___f_3368_;
v___y_3323_ = v___y_3352_;
v___y_3324_ = v___y_3350_;
v___y_3325_ = v___x_3376_;
goto v___jp_3321_;
}
}
else
{
size_t v___x_3377_; size_t v___x_3378_; lean_object* v___x_3379_; 
v___x_3377_ = ((size_t)0ULL);
v___x_3378_ = lean_usize_of_nat(v___x_3371_);
v___x_3379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3353_, v___x_3377_, v___x_3378_, v___x_3346_);
lean_dec_ref(v___y_3353_);
v___y_3322_ = v___f_3368_;
v___y_3323_ = v___y_3352_;
v___y_3324_ = v___y_3350_;
v___y_3325_ = v___x_3379_;
goto v___jp_3321_;
}
}
}
}
v___jp_3380_:
{
if (lean_obj_tag(v___y_3387_) == 0)
{
lean_object* v___x_3389_; uint64_t v_javascriptHash_3390_; lean_object* v_suggestion_3391_; lean_object* v_messageData_x3f_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___f_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; 
lean_dec_ref(v___y_3388_);
v___x_3389_ = l_Lean_Meta_Hint_textInsertionWidget;
v_javascriptHash_3390_ = lean_ctor_get_uint64(v___x_3389_, sizeof(void*)*1);
v_suggestion_3391_ = lean_ctor_get(v___y_3381_, 0);
lean_inc_ref(v_suggestion_3391_);
v_messageData_x3f_3392_ = lean_ctor_get(v___y_3381_, 4);
lean_inc(v_messageData_x3f_3392_);
lean_dec_ref(v___y_3381_);
v___x_3393_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18));
v___x_3394_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3395_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3385_);
v___x_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3394_);
lean_ctor_set(v___x_3396_, 1, v___x_3395_);
v___x_3397_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3398_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3398_, 0, v___y_3382_);
v___x_3399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3397_);
lean_ctor_set(v___x_3399_, 1, v___x_3398_);
v___x_3400_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31);
v___x_3401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3401_, 0, v___x_3399_);
lean_ctor_set(v___x_3401_, 1, v___x_3400_);
v___x_3402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3396_);
lean_ctor_set(v___x_3402_, 1, v___x_3401_);
v___x_3403_ = l_Lean_Json_mkObj(v___x_3402_);
v___f_3404_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3404_, 0, v___x_3403_);
v___x_3405_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3405_, 0, v___x_3393_);
lean_ctor_set(v___x_3405_, 1, v___f_3404_);
lean_ctor_set_uint64(v___x_3405_, sizeof(void*)*2, v_javascriptHash_3390_);
v___x_3406_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33);
v___x_3407_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3405_);
lean_ctor_set(v___x_3407_, 1, v___x_3406_);
v___x_3408_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3408_);
lean_ctor_set(v___x_3409_, 1, v___x_3407_);
v___x_3410_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35);
v___x_3411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3409_);
lean_ctor_set(v___x_3411_, 1, v___x_3410_);
v___x_3412_ = l_Lean_stringToMessageData(v___y_3386_);
v___x_3413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3411_);
lean_ctor_set(v___x_3413_, 1, v___x_3412_);
if (lean_obj_tag(v_messageData_x3f_3392_) == 0)
{
if (lean_obj_tag(v_suggestion_3391_) == 0)
{
lean_object* v_a_3414_; lean_object* v___x_3415_; 
v_a_3414_ = lean_ctor_get(v_suggestion_3391_, 1);
lean_inc(v_a_3414_);
lean_dec_ref(v_suggestion_3391_);
v___x_3415_ = l_Lean_MessageData_ofSyntax(v_a_3414_);
v___y_3307_ = v___y_3384_;
v___y_3308_ = v___x_3413_;
v___y_3309_ = v___x_3415_;
goto v___jp_3306_;
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3424_; 
v_a_3416_ = lean_ctor_get(v_suggestion_3391_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v_suggestion_3391_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3418_ = v_suggestion_3391_;
v_isShared_3419_ = v_isSharedCheck_3424_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v_suggestion_3391_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3424_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
lean_ctor_set_tag(v___x_3418_, 3);
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
lean_object* v___x_3422_; 
v___x_3422_ = l_Lean_MessageData_ofFormat(v___x_3421_);
v___y_3307_ = v___y_3384_;
v___y_3308_ = v___x_3413_;
v___y_3309_ = v___x_3422_;
goto v___jp_3306_;
}
}
}
}
else
{
lean_object* v_val_3425_; 
lean_dec_ref(v_suggestion_3391_);
v_val_3425_ = lean_ctor_get(v_messageData_x3f_3392_, 0);
lean_inc(v_val_3425_);
lean_dec_ref(v_messageData_x3f_3392_);
v___y_3307_ = v___y_3384_;
v___y_3308_ = v___x_3413_;
v___y_3309_ = v_val_3425_;
goto v___jp_3306_;
}
}
else
{
lean_dec_ref(v___y_3387_);
lean_dec_ref(v___y_3381_);
v___y_3348_ = v___y_3382_;
v___y_3349_ = v___y_3383_;
v___y_3350_ = v___y_3384_;
v___y_3351_ = v___y_3385_;
v___y_3352_ = v___y_3386_;
v___y_3353_ = v___y_3388_;
goto v___jp_3347_;
}
}
v___jp_3426_:
{
if (v___y_3434_ == 0)
{
lean_object* v_messageData_x3f_3435_; 
v_messageData_x3f_3435_ = lean_ctor_get(v___y_3427_, 4);
if (lean_obj_tag(v_messageData_x3f_3435_) == 0)
{
lean_dec(v___y_3432_);
lean_dec_ref(v___y_3427_);
v___y_3348_ = v___y_3428_;
v___y_3349_ = v___y_3434_;
v___y_3350_ = v___y_3430_;
v___y_3351_ = v___y_3429_;
v___y_3352_ = v___y_3431_;
v___y_3353_ = v___y_3433_;
goto v___jp_3347_;
}
else
{
v___y_3381_ = v___y_3427_;
v___y_3382_ = v___y_3428_;
v___y_3383_ = v___y_3434_;
v___y_3384_ = v___y_3430_;
v___y_3385_ = v___y_3429_;
v___y_3386_ = v___y_3431_;
v___y_3387_ = v___y_3432_;
v___y_3388_ = v___y_3433_;
goto v___jp_3380_;
}
}
else
{
v___y_3381_ = v___y_3427_;
v___y_3382_ = v___y_3428_;
v___y_3383_ = v___y_3434_;
v___y_3384_ = v___y_3430_;
v___y_3385_ = v___y_3429_;
v___y_3386_ = v___y_3431_;
v___y_3387_ = v___y_3432_;
v___y_3388_ = v___y_3433_;
goto v___jp_3380_;
}
}
v___jp_3436_:
{
if (v___y_3441_ == 4)
{
v___y_3427_ = v___y_3437_;
v___y_3428_ = v___y_3438_;
v___y_3429_ = v___y_3440_;
v___y_3430_ = v___y_3445_;
v___y_3431_ = v___y_3442_;
v___y_3432_ = v___y_3443_;
v___y_3433_ = v___y_3444_;
v___y_3434_ = v___x_3342_;
goto v___jp_3426_;
}
else
{
v___y_3427_ = v___y_3437_;
v___y_3428_ = v___y_3438_;
v___y_3429_ = v___y_3440_;
v___y_3430_ = v___y_3445_;
v___y_3431_ = v___y_3442_;
v___y_3432_ = v___y_3443_;
v___y_3433_ = v___y_3444_;
v___y_3434_ = v___y_3439_;
goto v___jp_3426_;
}
}
v___jp_3446_:
{
if (lean_obj_tag(v_postInfo_x3f_3448_) == 0)
{
v___y_3437_ = v___y_3447_;
v___y_3438_ = v___y_3449_;
v___y_3439_ = v___y_3450_;
v___y_3440_ = v___y_3451_;
v___y_3441_ = v___y_3452_;
v___y_3442_ = v___y_3455_;
v___y_3443_ = v___y_3453_;
v___y_3444_ = v___y_3454_;
v___y_3445_ = v___x_3346_;
goto v___jp_3436_;
}
else
{
lean_object* v_val_3456_; 
v_val_3456_ = lean_ctor_get(v_postInfo_x3f_3448_, 0);
lean_inc(v_val_3456_);
lean_dec_ref(v_postInfo_x3f_3448_);
v___y_3437_ = v___y_3447_;
v___y_3438_ = v___y_3449_;
v___y_3439_ = v___y_3450_;
v___y_3440_ = v___y_3451_;
v___y_3441_ = v___y_3452_;
v___y_3442_ = v___y_3455_;
v___y_3443_ = v___y_3453_;
v___y_3444_ = v___y_3454_;
v___y_3445_ = v_val_3456_;
goto v___jp_3436_;
}
}
v___jp_3457_:
{
lean_object* v_preInfo_x3f_3465_; 
v_preInfo_x3f_3465_ = lean_ctor_get(v___y_3458_, 1);
if (lean_obj_tag(v_preInfo_x3f_3465_) == 0)
{
lean_object* v_postInfo_x3f_3466_; 
v_postInfo_x3f_3466_ = lean_ctor_get(v___y_3458_, 2);
lean_inc(v_postInfo_x3f_3466_);
v___y_3447_ = v___y_3458_;
v_postInfo_x3f_3448_ = v_postInfo_x3f_3466_;
v___y_3449_ = v___y_3459_;
v___y_3450_ = v___y_3460_;
v___y_3451_ = v___y_3461_;
v___y_3452_ = v___y_3462_;
v___y_3453_ = v___y_3463_;
v___y_3454_ = v_edits_3464_;
v___y_3455_ = v___x_3346_;
goto v___jp_3446_;
}
else
{
lean_object* v_postInfo_x3f_3467_; lean_object* v_val_3468_; 
v_postInfo_x3f_3467_ = lean_ctor_get(v___y_3458_, 2);
lean_inc(v_postInfo_x3f_3467_);
v_val_3468_ = lean_ctor_get(v_preInfo_x3f_3465_, 0);
lean_inc(v_val_3468_);
v___y_3447_ = v___y_3458_;
v_postInfo_x3f_3448_ = v_postInfo_x3f_3467_;
v___y_3449_ = v___y_3459_;
v___y_3450_ = v___y_3460_;
v___y_3451_ = v___y_3461_;
v___y_3452_ = v___y_3462_;
v___y_3453_ = v___y_3463_;
v___y_3454_ = v_edits_3464_;
v___y_3455_ = v_val_3468_;
goto v___jp_3446_;
}
}
v___jp_3469_:
{
uint8_t v___x_3480_; 
v___x_3480_ = lean_nat_dec_lt(v___y_3471_, v_stop_3476_);
if (v___x_3480_ == 0)
{
lean_dec(v_stop_3476_);
lean_dec(v___y_3471_);
v___y_3458_ = v___y_3470_;
v___y_3459_ = v___y_3472_;
v___y_3460_ = v___y_3474_;
v___y_3461_ = v___y_3475_;
v___y_3462_ = v___y_3477_;
v___y_3463_ = v___y_3478_;
v_edits_3464_ = v_edits_3479_;
goto v___jp_3457_;
}
else
{
lean_object* v_source_3481_; uint8_t v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
v_source_3481_ = lean_ctor_get(v___y_3473_, 0);
v___x_3482_ = 2;
v___x_3483_ = lean_string_utf8_extract(v_source_3481_, v___y_3471_, v_stop_3476_);
lean_dec(v_stop_3476_);
lean_dec(v___y_3471_);
v___x_3484_ = lean_box(v___x_3482_);
v___x_3485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
lean_ctor_set(v___x_3485_, 1, v___x_3483_);
v___x_3486_ = lean_array_push(v_edits_3479_, v___x_3485_);
v___y_3458_ = v___y_3470_;
v___y_3459_ = v___y_3472_;
v___y_3460_ = v___y_3474_;
v___y_3461_ = v___y_3475_;
v___y_3462_ = v___y_3477_;
v___y_3463_ = v___y_3478_;
v_edits_3464_ = v___x_3486_;
goto v___jp_3457_;
}
}
v___jp_3487_:
{
if (lean_obj_tag(v___y_3496_) == 0)
{
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3491_);
lean_dec(v___y_3488_);
v___y_3458_ = v___y_3489_;
v___y_3459_ = v___y_3490_;
v___y_3460_ = v___y_3492_;
v___y_3461_ = v___y_3493_;
v___y_3462_ = v___y_3495_;
v___y_3463_ = v___y_3496_;
v_edits_3464_ = v_edits_3497_;
goto v___jp_3457_;
}
else
{
lean_object* v_val_3499_; lean_object* v___x_3500_; 
v_val_3499_ = lean_ctor_get(v___y_3496_, 0);
v___x_3500_ = l_Lean_Syntax_getRange_x3f(v_val_3499_, v___y_3492_);
if (lean_obj_tag(v___x_3500_) == 1)
{
lean_object* v_val_3501_; uint8_t v___x_3502_; 
v_val_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_val_3501_);
lean_dec_ref(v___x_3500_);
v___x_3502_ = l_Lean_Syntax_Range_includes(v_val_3501_, v___y_3494_, v___y_3492_, v___y_3492_);
lean_dec_ref(v___y_3494_);
if (v___x_3502_ == 0)
{
lean_dec(v_val_3501_);
lean_dec(v___y_3491_);
lean_dec(v___y_3488_);
v___y_3458_ = v___y_3489_;
v___y_3459_ = v___y_3490_;
v___y_3460_ = v___y_3492_;
v___y_3461_ = v___y_3493_;
v___y_3462_ = v___y_3495_;
v___y_3463_ = v___y_3496_;
v_edits_3464_ = v_edits_3497_;
goto v___jp_3457_;
}
else
{
lean_object* v_fileMap_3503_; lean_object* v_start_3504_; lean_object* v_stop_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3521_; 
v_fileMap_3503_ = lean_ctor_get(v___y_3498_, 1);
v_start_3504_ = lean_ctor_get(v_val_3501_, 0);
v_stop_3505_ = lean_ctor_get(v_val_3501_, 1);
v_isSharedCheck_3521_ = !lean_is_exclusive(v_val_3501_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3507_ = v_val_3501_;
v_isShared_3508_ = v_isSharedCheck_3521_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_stop_3505_);
lean_inc(v_start_3504_);
lean_dec(v_val_3501_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3521_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
uint8_t v___x_3509_; 
v___x_3509_ = lean_nat_dec_lt(v_start_3504_, v___y_3491_);
if (v___x_3509_ == 0)
{
lean_del_object(v___x_3507_);
lean_dec(v_start_3504_);
lean_dec(v___y_3491_);
v___y_3470_ = v___y_3489_;
v___y_3471_ = v___y_3488_;
v___y_3472_ = v___y_3490_;
v___y_3473_ = v_fileMap_3503_;
v___y_3474_ = v___y_3492_;
v___y_3475_ = v___y_3493_;
v_stop_3476_ = v_stop_3505_;
v___y_3477_ = v___y_3495_;
v___y_3478_ = v___y_3496_;
v_edits_3479_ = v_edits_3497_;
goto v___jp_3469_;
}
else
{
lean_object* v_source_3510_; uint8_t v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3515_; 
v_source_3510_ = lean_ctor_get(v_fileMap_3503_, 0);
v___x_3511_ = 2;
v___x_3512_ = lean_string_utf8_extract(v_source_3510_, v_start_3504_, v___y_3491_);
lean_dec(v___y_3491_);
lean_dec(v_start_3504_);
v___x_3513_ = lean_box(v___x_3511_);
if (v_isShared_3508_ == 0)
{
lean_ctor_set(v___x_3507_, 1, v___x_3512_);
lean_ctor_set(v___x_3507_, 0, v___x_3513_);
v___x_3515_ = v___x_3507_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v___x_3513_);
lean_ctor_set(v_reuseFailAlloc_3520_, 1, v___x_3512_);
v___x_3515_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3516_ = lean_unsigned_to_nat(1u);
v___x_3517_ = lean_mk_empty_array_with_capacity(v___x_3516_);
v___x_3518_ = lean_array_push(v___x_3517_, v___x_3515_);
v___x_3519_ = l_Array_append___redArg(v___x_3518_, v_edits_3497_);
lean_dec_ref(v_edits_3497_);
v___y_3470_ = v___y_3489_;
v___y_3471_ = v___y_3488_;
v___y_3472_ = v___y_3490_;
v___y_3473_ = v_fileMap_3503_;
v___y_3474_ = v___y_3492_;
v___y_3475_ = v___y_3493_;
v_stop_3476_ = v_stop_3505_;
v___y_3477_ = v___y_3495_;
v___y_3478_ = v___y_3496_;
v_edits_3479_ = v___x_3519_;
goto v___jp_3469_;
}
}
}
}
}
else
{
lean_dec(v___x_3500_);
lean_dec_ref(v___y_3494_);
lean_dec(v___y_3491_);
lean_dec(v___y_3488_);
v___y_3458_ = v___y_3489_;
v___y_3459_ = v___y_3490_;
v___y_3460_ = v___y_3492_;
v___y_3461_ = v___y_3493_;
v___y_3462_ = v___y_3495_;
v___y_3463_ = v___y_3496_;
v_edits_3464_ = v_edits_3497_;
goto v___jp_3457_;
}
}
}
v___jp_3523_:
{
lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
lean_inc_ref(v___y_3524_);
v___x_3534_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3534_, 0, v___y_3531_);
lean_ctor_set(v___x_3534_, 1, v___y_3533_);
lean_ctor_set(v___x_3534_, 2, v___y_3524_);
v___x_3535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3522_);
lean_ctor_set(v___x_3535_, 1, v___x_3534_);
v___x_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3536_, 0, v___y_3528_);
lean_ctor_set(v___x_3536_, 1, v___x_3535_);
v___x_3537_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3536_);
v___x_3538_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v___x_3537_, v___y_3294_, v___y_3295_);
if (lean_obj_tag(v___x_3538_) == 0)
{
lean_object* v_messageData_x3f_3539_; 
lean_dec_ref(v___x_3538_);
v_messageData_x3f_3539_ = lean_ctor_get(v___y_3524_, 4);
if (lean_obj_tag(v_messageData_x3f_3539_) == 1)
{
lean_object* v_start_3540_; lean_object* v_stop_3541_; lean_object* v_val_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; uint8_t v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; 
v_start_3540_ = lean_ctor_get(v___y_3530_, 0);
lean_inc(v_start_3540_);
v_stop_3541_ = lean_ctor_get(v___y_3530_, 1);
lean_inc(v_stop_3541_);
v_val_3542_ = lean_ctor_get(v_messageData_x3f_3539_, 0);
v___x_3543_ = lean_box(0);
lean_inc(v_val_3542_);
v___x_3544_ = l_Lean_MessageData_format(v_val_3542_, v___x_3543_);
v___x_3545_ = 0;
v___x_3546_ = l_Std_Format_defWidth;
v___x_3547_ = lean_unsigned_to_nat(0u);
v___x_3548_ = l_Std_Format_pretty(v___x_3544_, v___x_3546_, v___x_3547_, v___x_3547_);
v___x_3549_ = lean_box(v___x_3545_);
v___x_3550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
lean_ctor_set(v___x_3550_, 1, v___x_3548_);
v___x_3551_ = lean_unsigned_to_nat(1u);
v___x_3552_ = lean_mk_empty_array_with_capacity(v___x_3551_);
v___x_3553_ = lean_array_push(v___x_3552_, v___x_3550_);
v___y_3488_ = v_stop_3541_;
v___y_3489_ = v___y_3524_;
v___y_3490_ = v___y_3525_;
v___y_3491_ = v_start_3540_;
v___y_3492_ = v___y_3526_;
v___y_3493_ = v___y_3527_;
v___y_3494_ = v___y_3530_;
v___y_3495_ = v___y_3529_;
v___y_3496_ = v___y_3532_;
v_edits_3497_ = v___x_3553_;
v___y_3498_ = v___y_3294_;
goto v___jp_3487_;
}
else
{
lean_object* v_fileMap_3554_; lean_object* v_start_3555_; lean_object* v_stop_3556_; lean_object* v_source_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; 
v_fileMap_3554_ = lean_ctor_get(v___y_3294_, 1);
v_start_3555_ = lean_ctor_get(v___y_3530_, 0);
lean_inc(v_start_3555_);
v_stop_3556_ = lean_ctor_get(v___y_3530_, 1);
lean_inc(v_stop_3556_);
v_source_3557_ = lean_ctor_get(v_fileMap_3554_, 0);
v___x_3558_ = lean_string_utf8_extract(v_source_3557_, v_start_3555_, v_stop_3556_);
lean_inc_ref(v___y_3525_);
v___x_3559_ = l_Lean_Meta_Hint_readableDiff(v___x_3558_, v___y_3525_, v___y_3529_);
v___y_3488_ = v_stop_3556_;
v___y_3489_ = v___y_3524_;
v___y_3490_ = v___y_3525_;
v___y_3491_ = v_start_3555_;
v___y_3492_ = v___y_3526_;
v___y_3493_ = v___y_3527_;
v___y_3494_ = v___y_3530_;
v___y_3495_ = v___y_3529_;
v___y_3496_ = v___y_3532_;
v_edits_3497_ = v___x_3559_;
v___y_3498_ = v___y_3294_;
goto v___jp_3487_;
}
}
else
{
lean_object* v_a_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3567_; 
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3530_);
lean_dec_ref(v___y_3527_);
lean_dec_ref(v___y_3525_);
lean_dec_ref(v___y_3524_);
lean_dec_ref(v_b_3293_);
lean_dec(v_ref_3289_);
lean_dec(v_codeActionPrefix_x3f_3288_);
v_a_3560_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3562_ = v___x_3538_;
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_a_3560_);
lean_dec(v___x_3538_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3565_; 
if (v_isShared_3563_ == 0)
{
v___x_3565_ = v___x_3562_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_a_3560_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
}
}
v___jp_3568_:
{
lean_object* v_toCodeActionTitle_x3f_3578_; lean_object* v___x_3579_; 
v_toCodeActionTitle_x3f_3578_ = lean_ctor_get(v___y_3569_, 5);
v___x_3579_ = l_Lean_Syntax_ofRange(v___y_3577_, v___x_3342_);
if (lean_obj_tag(v_toCodeActionTitle_x3f_3578_) == 0)
{
if (lean_obj_tag(v_codeActionPrefix_x3f_3288_) == 0)
{
lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3580_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__36));
v___x_3581_ = lean_string_append(v___x_3580_, v___y_3570_);
v___y_3524_ = v___y_3569_;
v___y_3525_ = v___y_3570_;
v___y_3526_ = v___y_3571_;
v___y_3527_ = v___y_3572_;
v___y_3528_ = v___x_3579_;
v___y_3529_ = v___y_3574_;
v___y_3530_ = v___y_3573_;
v___y_3531_ = v___y_3575_;
v___y_3532_ = v___y_3576_;
v___y_3533_ = v___x_3581_;
goto v___jp_3523_;
}
else
{
lean_object* v_val_3582_; lean_object* v___x_3583_; 
v_val_3582_ = lean_ctor_get(v_codeActionPrefix_x3f_3288_, 0);
lean_inc(v_val_3582_);
v___x_3583_ = lean_string_append(v_val_3582_, v___y_3570_);
v___y_3524_ = v___y_3569_;
v___y_3525_ = v___y_3570_;
v___y_3526_ = v___y_3571_;
v___y_3527_ = v___y_3572_;
v___y_3528_ = v___x_3579_;
v___y_3529_ = v___y_3574_;
v___y_3530_ = v___y_3573_;
v___y_3531_ = v___y_3575_;
v___y_3532_ = v___y_3576_;
v___y_3533_ = v___x_3583_;
goto v___jp_3523_;
}
}
else
{
lean_object* v_val_3584_; lean_object* v___x_3585_; 
v_val_3584_ = lean_ctor_get(v_toCodeActionTitle_x3f_3578_, 0);
lean_inc(v_val_3584_);
lean_inc_ref(v___y_3570_);
v___x_3585_ = lean_apply_1(v_val_3584_, v___y_3570_);
v___y_3524_ = v___y_3569_;
v___y_3525_ = v___y_3570_;
v___y_3526_ = v___y_3571_;
v___y_3527_ = v___y_3572_;
v___y_3528_ = v___x_3579_;
v___y_3529_ = v___y_3574_;
v___y_3530_ = v___y_3573_;
v___y_3531_ = v___y_3575_;
v___y_3532_ = v___y_3576_;
v___y_3533_ = v___x_3585_;
goto v___jp_3523_;
}
}
v___jp_3586_:
{
uint8_t v___x_3588_; lean_object* v___x_3589_; 
v___x_3588_ = 0;
v___x_3589_ = l_Lean_Syntax_getRange_x3f(v___y_3587_, v___x_3588_);
lean_dec(v___y_3587_);
if (lean_obj_tag(v___x_3589_) == 1)
{
lean_object* v_val_3590_; lean_object* v_toTryThisSuggestion_3591_; lean_object* v_previewSpan_x3f_3592_; uint8_t v_diffGranularity_3593_; lean_object* v___x_3594_; 
v_val_3590_ = lean_ctor_get(v___x_3589_, 0);
lean_inc_n(v_val_3590_, 2);
lean_dec_ref(v___x_3589_);
v_toTryThisSuggestion_3591_ = lean_ctor_get(v_a_3344_, 0);
v_previewSpan_x3f_3592_ = lean_ctor_get(v_a_3344_, 2);
v_diffGranularity_3593_ = lean_ctor_get_uint8(v_a_3344_, sizeof(void*)*3);
lean_inc_ref(v_toTryThisSuggestion_3591_);
v___x_3594_ = l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(v_toTryThisSuggestion_3591_, v_val_3590_, v___y_3294_, v___y_3295_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v_a_3595_; lean_object* v_range_3596_; lean_object* v_newText_3597_; lean_object* v___x_3598_; 
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_a_3595_);
lean_dec_ref(v___x_3594_);
v_range_3596_ = lean_ctor_get(v_a_3595_, 0);
lean_inc_ref(v_range_3596_);
v_newText_3597_ = lean_ctor_get(v_a_3595_, 1);
lean_inc_ref(v_newText_3597_);
v___x_3598_ = l_Lean_Syntax_getRange_x3f(v_ref_3289_, v___x_3588_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_inc(v_previewSpan_x3f_3592_);
lean_inc(v_val_3590_);
lean_inc_ref(v_toTryThisSuggestion_3591_);
v___y_3569_ = v_toTryThisSuggestion_3591_;
v___y_3570_ = v_newText_3597_;
v___y_3571_ = v___x_3588_;
v___y_3572_ = v_range_3596_;
v___y_3573_ = v_val_3590_;
v___y_3574_ = v_diffGranularity_3593_;
v___y_3575_ = v_a_3595_;
v___y_3576_ = v_previewSpan_x3f_3592_;
v___y_3577_ = v_val_3590_;
goto v___jp_3568_;
}
else
{
lean_object* v_val_3599_; 
v_val_3599_ = lean_ctor_get(v___x_3598_, 0);
lean_inc(v_val_3599_);
lean_dec_ref(v___x_3598_);
lean_inc(v_previewSpan_x3f_3592_);
lean_inc_ref(v_toTryThisSuggestion_3591_);
v___y_3569_ = v_toTryThisSuggestion_3591_;
v___y_3570_ = v_newText_3597_;
v___y_3571_ = v___x_3588_;
v___y_3572_ = v_range_3596_;
v___y_3573_ = v_val_3590_;
v___y_3574_ = v_diffGranularity_3593_;
v___y_3575_ = v_a_3595_;
v___y_3576_ = v_previewSpan_x3f_3592_;
v___y_3577_ = v_val_3599_;
goto v___jp_3568_;
}
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3607_; 
lean_dec(v_val_3590_);
lean_dec_ref(v_b_3293_);
lean_dec(v_ref_3289_);
lean_dec(v_codeActionPrefix_x3f_3288_);
v_a_3600_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3602_ = v___x_3594_;
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3594_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3605_; 
if (v_isShared_3603_ == 0)
{
v___x_3605_ = v___x_3602_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3600_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
else
{
lean_dec(v___x_3589_);
v_a_3298_ = v_b_3293_;
goto v___jp_3297_;
}
}
}
v___jp_3297_:
{
size_t v___x_3299_; size_t v___x_3300_; 
v___x_3299_ = ((size_t)1ULL);
v___x_3300_ = lean_usize_add(v_i_3292_, v___x_3299_);
v_i_3292_ = v___x_3300_;
v_b_3293_ = v_a_3298_;
goto _start;
}
v___jp_3302_:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = l_Lean_MessageData_nestD(v___y_3303_);
v___x_3305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3305_, 0, v_b_3293_);
lean_ctor_set(v___x_3305_, 1, v___x_3304_);
v_a_3298_ = v___x_3305_;
goto v___jp_3297_;
}
v___jp_3306_:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___y_3308_);
lean_ctor_set(v___x_3310_, 1, v___y_3309_);
v___x_3311_ = l_Lean_stringToMessageData(v___y_3307_);
v___x_3312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3310_);
lean_ctor_set(v___x_3312_, 1, v___x_3311_);
v___y_3303_ = v___x_3312_;
goto v___jp_3302_;
}
v___jp_3313_:
{
lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3315_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3316_ = lean_unsigned_to_nat(2u);
v___x_3317_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3);
v___x_3318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3317_);
lean_ctor_set(v___x_3318_, 1, v___y_3314_);
v___x_3319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3316_);
lean_ctor_set(v___x_3319_, 1, v___x_3318_);
v___x_3320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3315_);
lean_ctor_set(v___x_3320_, 1, v___x_3319_);
v___y_3303_ = v___x_3320_;
goto v___jp_3302_;
}
v___jp_3321_:
{
lean_object* v___x_3326_; uint64_t v_javascriptHash_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; uint8_t v___x_3339_; 
v___x_3326_ = l_Lean_Meta_Hint_tryThisDiffWidget;
v_javascriptHash_3327_ = lean_ctor_get_uint64(v___x_3326_, sizeof(void*)*1);
v___x_3328_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8));
v___x_3329_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3329_, 0, v___x_3328_);
lean_ctor_set(v___x_3329_, 1, v___y_3322_);
lean_ctor_set_uint64(v___x_3329_, sizeof(void*)*2, v_javascriptHash_3327_);
v___x_3330_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3330_, 0, v___y_3325_);
v___x_3331_ = l_Lean_MessageData_ofFormat(v___x_3330_);
v___x_3332_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3329_);
lean_ctor_set(v___x_3332_, 1, v___x_3331_);
v___x_3333_ = l_Lean_stringToMessageData(v___y_3323_);
v___x_3334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
lean_ctor_set(v___x_3334_, 1, v___x_3332_);
v___x_3335_ = l_Lean_stringToMessageData(v___y_3324_);
v___x_3336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3334_);
lean_ctor_set(v___x_3336_, 1, v___x_3335_);
v___x_3337_ = lean_array_get_size(v_suggestions_3286_);
v___x_3338_ = lean_unsigned_to_nat(1u);
v___x_3339_ = lean_nat_dec_eq(v___x_3337_, v___x_3338_);
if (v___x_3339_ == 0)
{
v___y_3314_ = v___x_3336_;
goto v___jp_3313_;
}
else
{
if (v_forceList_3287_ == 0)
{
if (v___x_3339_ == 0)
{
v___y_3314_ = v___x_3336_;
goto v___jp_3313_;
}
else
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3340_);
lean_ctor_set(v___x_3341_, 1, v___x_3336_);
v___y_3303_ = v___x_3341_;
goto v___jp_3302_;
}
}
else
{
v___y_3314_ = v___x_3336_;
goto v___jp_3313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___boxed(lean_object* v_suggestions_3609_, lean_object* v_forceList_3610_, lean_object* v_codeActionPrefix_x3f_3611_, lean_object* v_ref_3612_, lean_object* v_as_3613_, lean_object* v_sz_3614_, lean_object* v_i_3615_, lean_object* v_b_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
uint8_t v_forceList_boxed_3620_; size_t v_sz_boxed_3621_; size_t v_i_boxed_3622_; lean_object* v_res_3623_; 
v_forceList_boxed_3620_ = lean_unbox(v_forceList_3610_);
v_sz_boxed_3621_ = lean_unbox_usize(v_sz_3614_);
lean_dec(v_sz_3614_);
v_i_boxed_3622_ = lean_unbox_usize(v_i_3615_);
lean_dec(v_i_3615_);
v_res_3623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3609_, v_forceList_boxed_3620_, v_codeActionPrefix_x3f_3611_, v_ref_3612_, v_as_3613_, v_sz_boxed_3621_, v_i_boxed_3622_, v_b_3616_, v___y_3617_, v___y_3618_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
lean_dec_ref(v_as_3613_);
lean_dec_ref(v_suggestions_3609_);
return v_res_3623_;
}
}
static lean_object* _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0(void){
_start:
{
lean_object* v___x_3624_; lean_object* v_msg_3625_; 
v___x_3624_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v_msg_3625_ = l_Lean_stringToMessageData(v___x_3624_);
return v_msg_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage(lean_object* v_suggestions_3626_, lean_object* v_ref_3627_, lean_object* v_codeActionPrefix_x3f_3628_, uint8_t v_forceList_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_){
_start:
{
lean_object* v_msg_3633_; size_t v_sz_3634_; size_t v___x_3635_; lean_object* v___x_3636_; 
v_msg_3633_ = lean_obj_once(&l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0, &l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0_once, _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0);
v_sz_3634_ = lean_array_size(v_suggestions_3626_);
v___x_3635_ = ((size_t)0ULL);
v___x_3636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3626_, v_forceList_3629_, v_codeActionPrefix_x3f_3628_, v_ref_3627_, v_suggestions_3626_, v_sz_3634_, v___x_3635_, v_msg_3633_, v_a_3630_, v_a_3631_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage___boxed(lean_object* v_suggestions_3637_, lean_object* v_ref_3638_, lean_object* v_codeActionPrefix_x3f_3639_, lean_object* v_forceList_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_){
_start:
{
uint8_t v_forceList_boxed_3644_; lean_object* v_res_3645_; 
v_forceList_boxed_3644_ = lean_unbox(v_forceList_3640_);
v_res_3645_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3637_, v_ref_3638_, v_codeActionPrefix_x3f_3639_, v_forceList_boxed_3644_, v_a_3641_, v_a_3642_);
lean_dec(v_a_3642_);
lean_dec_ref(v_a_3641_);
lean_dec_ref(v_suggestions_3637_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(lean_object* v_t_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
lean_object* v___x_3650_; 
v___x_3650_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3646_, v___y_3648_);
return v___x_3650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___boxed(lean_object* v_t_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
lean_object* v_res_3655_; 
v_res_3655_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(v_t_3651_, v___y_3652_, v___y_3653_);
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
return v_res_3655_;
}
}
static lean_object* _init_l_Lean_MessageData_hint___closed__3(void){
_start:
{
lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3660_ = ((lean_object*)(l_Lean_MessageData_hint___closed__2));
v___x_3661_ = l_Lean_stringToMessageData(v___x_3660_);
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint(lean_object* v_hint_3662_, lean_object* v_suggestions_3663_, lean_object* v_ref_x3f_3664_, lean_object* v_codeActionPrefix_x3f_3665_, uint8_t v_forceList_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_){
_start:
{
lean_object* v___y_3671_; 
if (lean_obj_tag(v_ref_x3f_3664_) == 0)
{
lean_object* v_ref_3686_; 
v_ref_3686_ = lean_ctor_get(v_a_3667_, 5);
lean_inc(v_ref_3686_);
v___y_3671_ = v_ref_3686_;
goto v___jp_3670_;
}
else
{
lean_object* v_val_3687_; 
v_val_3687_ = lean_ctor_get(v_ref_x3f_3664_, 0);
lean_inc(v_val_3687_);
lean_dec_ref(v_ref_x3f_3664_);
v___y_3671_ = v_val_3687_;
goto v___jp_3670_;
}
v___jp_3670_:
{
lean_object* v___x_3672_; 
v___x_3672_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3663_, v___y_3671_, v_codeActionPrefix_x3f_3665_, v_forceList_3666_, v_a_3667_, v_a_3668_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v_a_3673_; lean_object* v___x_3675_; uint8_t v_isShared_3676_; uint8_t v_isSharedCheck_3685_; 
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3675_ = v___x_3672_;
v_isShared_3676_ = v_isSharedCheck_3685_;
goto v_resetjp_3674_;
}
else
{
lean_inc(v_a_3673_);
lean_dec(v___x_3672_);
v___x_3675_ = lean_box(0);
v_isShared_3676_ = v_isSharedCheck_3685_;
goto v_resetjp_3674_;
}
v_resetjp_3674_:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3683_; 
v___x_3677_ = ((lean_object*)(l_Lean_MessageData_hint___closed__1));
v___x_3678_ = lean_obj_once(&l_Lean_MessageData_hint___closed__3, &l_Lean_MessageData_hint___closed__3_once, _init_l_Lean_MessageData_hint___closed__3);
v___x_3679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3678_);
lean_ctor_set(v___x_3679_, 1, v_hint_3662_);
v___x_3680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3679_);
lean_ctor_set(v___x_3680_, 1, v_a_3673_);
v___x_3681_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3677_);
lean_ctor_set(v___x_3681_, 1, v___x_3680_);
if (v_isShared_3676_ == 0)
{
lean_ctor_set(v___x_3675_, 0, v___x_3681_);
v___x_3683_ = v___x_3675_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3681_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
else
{
lean_dec_ref(v_hint_3662_);
return v___x_3672_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint___boxed(lean_object* v_hint_3688_, lean_object* v_suggestions_3689_, lean_object* v_ref_x3f_3690_, lean_object* v_codeActionPrefix_x3f_3691_, lean_object* v_forceList_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_){
_start:
{
uint8_t v_forceList_boxed_3696_; lean_object* v_res_3697_; 
v_forceList_boxed_3696_ = lean_unbox(v_forceList_3692_);
v_res_3697_ = l_Lean_MessageData_hint(v_hint_3688_, v_suggestions_3689_, v_ref_x3f_3690_, v_codeActionPrefix_x3f_3691_, v_forceList_boxed_3696_, v_a_3693_, v_a_3694_);
lean_dec(v_a_3694_);
lean_dec_ref(v_a_3693_);
lean_dec_ref(v_suggestions_3689_);
return v_res_3697_;
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
