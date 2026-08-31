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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Subarray_drop___redArg(lean_object*, lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Subarray_take___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
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
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_split___redArg(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Diff_instBEqAction_beq(uint8_t, uint8_t);
uint64_t lean_uint32_to_uint64(uint32_t);
lean_object* l_Lean_Json_mkObj(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_string_data(lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
lean_object* l_Lean_MessageData_nestD(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Lsp_instToJsonRange_toJson(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0;
static lean_once_cell_t l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(lean_object*, lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14(lean_object*, lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24(lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0;
static lean_once_cell_t l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg(uint32_t v_a_511_, lean_object* v_x_512_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg___boxed(lean_object* v_a_521_, lean_object* v_x_522_){
_start:
{
uint32_t v_a_boxed_523_; lean_object* v_res_524_; 
v_a_boxed_523_ = lean_unbox_uint32(v_a_521_);
lean_dec(v_a_521_);
v_res_524_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg(v_a_boxed_523_, v_x_522_);
lean_dec(v_x_522_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(lean_object* v_m_525_, uint32_t v_a_526_){
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
v___x_542_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg(v_a_526_, v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg___boxed(lean_object* v_m_543_, lean_object* v_a_544_){
_start:
{
uint32_t v_a_boxed_545_; lean_object* v_res_546_; 
v_a_boxed_545_ = lean_unbox_uint32(v_a_544_);
lean_dec(v_a_544_);
v_res_546_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_m_543_, v_a_boxed_545_);
lean_dec_ref(v_m_543_);
return v_res_546_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(uint32_t v_a_547_, lean_object* v_x_548_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg___boxed(lean_object* v_a_555_, lean_object* v_x_556_){
_start:
{
uint32_t v_a_boxed_557_; uint8_t v_res_558_; lean_object* v_r_559_; 
v_a_boxed_557_ = lean_unbox_uint32(v_a_555_);
lean_dec(v_a_555_);
v_res_558_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(v_a_boxed_557_, v_x_556_);
lean_dec(v_x_556_);
v_r_559_ = lean_box(v_res_558_);
return v_r_559_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(uint32_t v_a_560_, lean_object* v_b_561_, lean_object* v_x_562_){
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
v___x_571_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(v_a_560_, v_b_561_, v_tail_565_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg___boxed(lean_object* v_a_580_, lean_object* v_b_581_, lean_object* v_x_582_){
_start:
{
uint32_t v_a_boxed_583_; lean_object* v_res_584_; 
v_a_boxed_583_ = lean_unbox_uint32(v_a_580_);
lean_dec(v_a_580_);
v_res_584_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(v_a_boxed_583_, v_b_581_, v_x_582_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29___redArg(lean_object* v_x_585_, lean_object* v_x_586_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28___redArg(lean_object* v_i_614_, lean_object* v_source_615_, lean_object* v_target_616_){
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
v_target_622_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29___redArg(v_target_616_, v_es_619_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23___redArg(lean_object* v_data_626_){
_start:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v_nbuckets_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; 
v___x_627_ = lean_array_get_size(v_data_626_);
v___x_628_ = lean_unsigned_to_nat(2u);
v_nbuckets_629_ = lean_nat_mul(v___x_627_, v___x_628_);
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_box(0);
v___x_632_ = lean_mk_array(v_nbuckets_629_, v___x_631_);
v___x_633_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28___redArg(v___x_630_, v_data_626_, v___x_632_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(lean_object* v_m_634_, uint32_t v_a_635_, lean_object* v_b_636_){
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
v___x_656_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(v_a_635_, v_bkt_655_);
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
v_val_668_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23___redArg(v_buckets_x27_661_);
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
v___x_677_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(v_a_635_, v_b_636_, v_bkt_655_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg___boxed(lean_object* v_m_683_, lean_object* v_a_684_, lean_object* v_b_685_){
_start:
{
uint32_t v_a_boxed_686_; lean_object* v_res_687_; 
v_a_boxed_686_ = lean_unbox_uint32(v_a_684_);
lean_dec(v_a_684_);
v_res_687_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_m_683_, v_a_boxed_686_, v_b_685_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(lean_object* v_histogram_688_, lean_object* v_index_689_, uint32_t v_val_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_histogram_688_, v_val_690_);
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
v___x_697_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_688_, v_val_690_, v___x_696_);
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
v___x_713_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_688_, v_val_690_, v___x_712_);
return v___x_713_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_histogram_720_, lean_object* v_index_721_, lean_object* v_val_722_){
_start:
{
uint32_t v_val_boxed_723_; lean_object* v_res_724_; 
v_val_boxed_723_ = lean_unbox_uint32(v_val_722_);
lean_dec(v_val_722_);
v_res_724_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(v_histogram_720_, v_index_721_, v_val_boxed_723_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(lean_object* v_upperBound_725_, lean_object* v___x_726_, lean_object* v_fst_727_, lean_object* v___x_728_, lean_object* v_a_729_, lean_object* v_b_730_){
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
v___x_734_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(v_b_730_, v_a_729_, v___x_733_);
v___x_735_ = lean_unsigned_to_nat(1u);
v___x_736_ = lean_nat_add(v_a_729_, v___x_735_);
lean_dec(v_a_729_);
v_a_729_ = v___x_736_;
v_b_730_ = v___x_734_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg___boxed(lean_object* v_upperBound_738_, lean_object* v___x_739_, lean_object* v_fst_740_, lean_object* v___x_741_, lean_object* v_a_742_, lean_object* v_b_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(v_upperBound_738_, v___x_739_, v_fst_740_, v___x_741_, v_a_742_, v_b_743_);
lean_dec(v___x_741_);
lean_dec_ref(v_fst_740_);
lean_dec(v___x_739_);
lean_dec(v_upperBound_738_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(lean_object* v_as_x27_745_, lean_object* v_b_746_){
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_as_x27_797_, lean_object* v_b_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(v_as_x27_797_, v_b_798_);
lean_dec(v_as_x27_797_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(lean_object* v_a_800_, lean_object* v_b_801_){
_start:
{
lean_object* v_array_802_; lean_object* v_start_803_; lean_object* v_stop_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_817_; 
v_array_802_ = lean_ctor_get(v_a_800_, 0);
v_start_803_ = lean_ctor_get(v_a_800_, 1);
v_stop_804_ = lean_ctor_get(v_a_800_, 2);
v_isSharedCheck_817_ = !lean_is_exclusive(v_a_800_);
if (v_isSharedCheck_817_ == 0)
{
v___x_806_ = v_a_800_;
v_isShared_807_ = v_isSharedCheck_817_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_stop_804_);
lean_inc(v_start_803_);
lean_inc(v_array_802_);
lean_dec(v_a_800_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_817_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
uint8_t v___x_808_; 
v___x_808_ = lean_nat_dec_lt(v_start_803_, v_stop_804_);
if (v___x_808_ == 0)
{
lean_del_object(v___x_806_);
lean_dec(v_stop_804_);
lean_dec(v_start_803_);
lean_dec_ref(v_array_802_);
return v_b_801_;
}
else
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_812_; 
v___x_809_ = lean_unsigned_to_nat(1u);
v___x_810_ = lean_nat_add(v_start_803_, v___x_809_);
lean_inc_ref(v_array_802_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 1, v___x_810_);
v___x_812_ = v___x_806_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_array_802_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v___x_810_);
lean_ctor_set(v_reuseFailAlloc_816_, 2, v_stop_804_);
v___x_812_ = v_reuseFailAlloc_816_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = lean_array_fget(v_array_802_, v_start_803_);
lean_dec(v_start_803_);
lean_dec_ref(v_array_802_);
v___x_814_ = lean_array_push(v_b_801_, v___x_813_);
v_a_800_ = v___x_812_;
v_b_801_ = v___x_814_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8(lean_object* v_left_818_, lean_object* v_right_819_, lean_object* v_i_820_){
_start:
{
lean_object* v_start_821_; lean_object* v_stop_822_; lean_object* v_start_823_; lean_object* v_stop_824_; lean_object* v___x_825_; uint8_t v___x_826_; lean_object* v___x_827_; uint8_t v___y_829_; 
v_start_821_ = lean_ctor_get(v_left_818_, 1);
v_stop_822_ = lean_ctor_get(v_left_818_, 2);
v_start_823_ = lean_ctor_get(v_right_819_, 1);
v_stop_824_ = lean_ctor_get(v_right_819_, 2);
v___x_825_ = lean_nat_sub(v_stop_822_, v_start_821_);
v___x_826_ = lean_nat_dec_lt(v_i_820_, v___x_825_);
v___x_827_ = lean_nat_sub(v_stop_824_, v_start_823_);
if (v___x_826_ == 0)
{
v___y_829_ = v___x_826_;
goto v___jp_828_;
}
else
{
uint8_t v___x_858_; 
v___x_858_ = lean_nat_dec_lt(v_i_820_, v___x_827_);
v___y_829_ = v___x_858_;
goto v___jp_828_;
}
v___jp_828_:
{
if (v___y_829_ == 0)
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_830_ = lean_nat_sub(v___x_825_, v_i_820_);
lean_dec(v___x_825_);
lean_inc_ref(v_left_818_);
v___x_831_ = l_Subarray_take___redArg(v_left_818_, v___x_830_);
v___x_832_ = lean_nat_sub(v___x_827_, v_i_820_);
lean_dec(v_i_820_);
lean_dec(v___x_827_);
v___x_833_ = l_Subarray_take___redArg(v_right_819_, v___x_832_);
lean_dec(v___x_832_);
v___x_834_ = l_Subarray_drop___redArg(v_left_818_, v___x_830_);
lean_dec(v___x_830_);
v___x_835_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_836_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(v___x_834_, v___x_835_);
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_833_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_831_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
return v___x_838_;
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; uint32_t v___x_846_; uint32_t v___x_847_; uint8_t v___x_848_; 
v___x_839_ = lean_nat_sub(v___x_825_, v_i_820_);
lean_dec(v___x_825_);
v___x_840_ = lean_unsigned_to_nat(1u);
v___x_841_ = lean_nat_sub(v___x_839_, v___x_840_);
v___x_842_ = l_Subarray_get___redArg(v_left_818_, v___x_841_);
lean_dec(v___x_841_);
v___x_843_ = lean_nat_sub(v___x_827_, v_i_820_);
lean_dec(v___x_827_);
v___x_844_ = lean_nat_sub(v___x_843_, v___x_840_);
v___x_845_ = l_Subarray_get___redArg(v_right_819_, v___x_844_);
lean_dec(v___x_844_);
v___x_846_ = lean_unbox_uint32(v___x_842_);
lean_dec(v___x_842_);
v___x_847_ = lean_unbox_uint32(v___x_845_);
lean_dec(v___x_845_);
v___x_848_ = lean_uint32_dec_eq(v___x_846_, v___x_847_);
if (v___x_848_ == 0)
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
lean_dec(v_i_820_);
lean_inc_ref(v_left_818_);
v___x_849_ = l_Subarray_take___redArg(v_left_818_, v___x_839_);
v___x_850_ = l_Subarray_take___redArg(v_right_819_, v___x_843_);
lean_dec(v___x_843_);
v___x_851_ = l_Subarray_drop___redArg(v_left_818_, v___x_839_);
lean_dec(v___x_839_);
v___x_852_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_853_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(v___x_851_, v___x_852_);
v___x_854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_854_, 0, v___x_850_);
lean_ctor_set(v___x_854_, 1, v___x_853_);
v___x_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_849_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
return v___x_855_;
}
else
{
lean_object* v___x_856_; 
lean_dec(v___x_843_);
lean_dec(v___x_839_);
v___x_856_ = lean_nat_add(v_i_820_, v___x_840_);
lean_dec(v_i_820_);
v_i_820_ = v___x_856_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6(lean_object* v_left_859_, lean_object* v_right_860_){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_unsigned_to_nat(0u);
v___x_862_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8(v_left_859_, v_right_860_, v___x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(lean_object* v_x_863_, lean_object* v_x_864_){
_start:
{
if (lean_obj_tag(v_x_864_) == 0)
{
lean_inc(v_x_863_);
return v_x_863_;
}
else
{
lean_object* v_key_865_; lean_object* v_value_866_; lean_object* v_tail_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v_key_865_ = lean_ctor_get(v_x_864_, 0);
v_value_866_ = lean_ctor_get(v_x_864_, 1);
v_tail_867_ = lean_ctor_get(v_x_864_, 2);
v___x_868_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(v_x_863_, v_tail_867_);
lean_inc(v_value_866_);
lean_inc(v_key_865_);
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v_key_865_);
lean_ctor_set(v___x_869_, 1, v_value_866_);
v___x_870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_869_);
lean_ctor_set(v___x_870_, 1, v___x_868_);
return v___x_870_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8___boxed(lean_object* v_x_871_, lean_object* v_x_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(v_x_871_, v_x_872_);
lean_dec(v_x_872_);
lean_dec(v_x_871_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9(lean_object* v_as_874_, size_t v_i_875_, size_t v_stop_876_, lean_object* v_b_877_){
_start:
{
uint8_t v___x_878_; 
v___x_878_ = lean_usize_dec_eq(v_i_875_, v_stop_876_);
if (v___x_878_ == 0)
{
size_t v___x_879_; size_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_879_ = ((size_t)1ULL);
v___x_880_ = lean_usize_sub(v_i_875_, v___x_879_);
v___x_881_ = lean_array_uget_borrowed(v_as_874_, v___x_880_);
v___x_882_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(v_b_877_, v___x_881_);
lean_dec(v_b_877_);
v_i_875_ = v___x_880_;
v_b_877_ = v___x_882_;
goto _start;
}
else
{
return v_b_877_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9___boxed(lean_object* v_as_884_, lean_object* v_i_885_, lean_object* v_stop_886_, lean_object* v_b_887_){
_start:
{
size_t v_i_boxed_888_; size_t v_stop_boxed_889_; lean_object* v_res_890_; 
v_i_boxed_888_ = lean_unbox_usize(v_i_885_);
lean_dec(v_i_885_);
v_stop_boxed_889_ = lean_unbox_usize(v_stop_886_);
lean_dec(v_stop_886_);
v_res_890_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9(v_as_884_, v_i_boxed_888_, v_stop_boxed_889_, v_b_887_);
lean_dec_ref(v_as_884_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5_spec__6(lean_object* v_left_891_, lean_object* v_right_892_, lean_object* v_pref_893_){
_start:
{
lean_object* v_start_894_; lean_object* v_stop_895_; lean_object* v_start_896_; lean_object* v_stop_897_; lean_object* v_i_898_; uint8_t v___y_900_; lean_object* v___x_916_; uint8_t v___x_917_; 
v_start_894_ = lean_ctor_get(v_left_891_, 1);
v_stop_895_ = lean_ctor_get(v_left_891_, 2);
v_start_896_ = lean_ctor_get(v_right_892_, 1);
v_stop_897_ = lean_ctor_get(v_right_892_, 2);
v_i_898_ = lean_array_get_size(v_pref_893_);
v___x_916_ = lean_nat_sub(v_stop_895_, v_start_894_);
v___x_917_ = lean_nat_dec_lt(v_i_898_, v___x_916_);
lean_dec(v___x_916_);
if (v___x_917_ == 0)
{
v___y_900_ = v___x_917_;
goto v___jp_899_;
}
else
{
lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_918_ = lean_nat_sub(v_stop_897_, v_start_896_);
v___x_919_ = lean_nat_dec_lt(v_i_898_, v___x_918_);
lean_dec(v___x_918_);
v___y_900_ = v___x_919_;
goto v___jp_899_;
}
v___jp_899_:
{
if (v___y_900_ == 0)
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_901_ = l_Subarray_drop___redArg(v_left_891_, v_i_898_);
v___x_902_ = l_Subarray_drop___redArg(v_right_892_, v_i_898_);
v___x_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_903_, 0, v___x_901_);
lean_ctor_set(v___x_903_, 1, v___x_902_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v_pref_893_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
return v___x_904_;
}
else
{
lean_object* v___x_905_; lean_object* v___x_906_; uint32_t v___x_907_; uint32_t v___x_908_; uint8_t v___x_909_; 
v___x_905_ = l_Subarray_get___redArg(v_left_891_, v_i_898_);
v___x_906_ = l_Subarray_get___redArg(v_right_892_, v_i_898_);
v___x_907_ = lean_unbox_uint32(v___x_905_);
v___x_908_ = lean_unbox_uint32(v___x_906_);
lean_dec(v___x_906_);
v___x_909_ = lean_uint32_dec_eq(v___x_907_, v___x_908_);
if (v___x_909_ == 0)
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
lean_dec(v___x_905_);
v___x_910_ = l_Subarray_drop___redArg(v_left_891_, v_i_898_);
v___x_911_ = l_Subarray_drop___redArg(v_right_892_, v_i_898_);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_910_);
lean_ctor_set(v___x_912_, 1, v___x_911_);
v___x_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_913_, 0, v_pref_893_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
return v___x_913_;
}
else
{
lean_object* v___x_914_; 
v___x_914_ = lean_array_push(v_pref_893_, v___x_905_);
v_pref_893_ = v___x_914_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5(lean_object* v_left_920_, lean_object* v_right_921_){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_923_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5_spec__6(v_left_920_, v_right_921_, v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(lean_object* v_histogram_924_, lean_object* v_index_925_, uint32_t v_val_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_histogram_924_, v_val_926_);
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_928_ = lean_unsigned_to_nat(1u);
v___x_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_929_, 0, v_index_925_);
v___x_930_ = lean_unsigned_to_nat(0u);
v___x_931_ = lean_box(0);
v___x_932_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_932_, 0, v___x_928_);
lean_ctor_set(v___x_932_, 1, v___x_929_);
lean_ctor_set(v___x_932_, 2, v___x_930_);
lean_ctor_set(v___x_932_, 3, v___x_931_);
v___x_933_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_924_, v_val_926_, v___x_932_);
return v___x_933_;
}
else
{
lean_object* v_val_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_955_; 
v_val_934_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_955_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_955_ == 0)
{
v___x_936_ = v___x_927_;
v_isShared_937_ = v_isSharedCheck_955_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_val_934_);
lean_dec(v___x_927_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_955_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v_leftCount_938_; lean_object* v_rightCount_939_; lean_object* v_rightIndex_940_; lean_object* v___x_942_; uint8_t v_isShared_943_; uint8_t v_isSharedCheck_953_; 
v_leftCount_938_ = lean_ctor_get(v_val_934_, 0);
v_rightCount_939_ = lean_ctor_get(v_val_934_, 2);
v_rightIndex_940_ = lean_ctor_get(v_val_934_, 3);
v_isSharedCheck_953_ = !lean_is_exclusive(v_val_934_);
if (v_isSharedCheck_953_ == 0)
{
lean_object* v_unused_954_; 
v_unused_954_ = lean_ctor_get(v_val_934_, 1);
lean_dec(v_unused_954_);
v___x_942_ = v_val_934_;
v_isShared_943_ = v_isSharedCheck_953_;
goto v_resetjp_941_;
}
else
{
lean_inc(v_rightIndex_940_);
lean_inc(v_rightCount_939_);
lean_inc(v_leftCount_938_);
lean_dec(v_val_934_);
v___x_942_ = lean_box(0);
v_isShared_943_ = v_isSharedCheck_953_;
goto v_resetjp_941_;
}
v_resetjp_941_:
{
lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_944_ = lean_unsigned_to_nat(1u);
v___x_945_ = lean_nat_add(v_leftCount_938_, v___x_944_);
lean_dec(v_leftCount_938_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v_index_925_);
v___x_947_ = v___x_936_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_index_925_);
v___x_947_ = v_reuseFailAlloc_952_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_949_; 
if (v_isShared_943_ == 0)
{
lean_ctor_set(v___x_942_, 1, v___x_947_);
lean_ctor_set(v___x_942_, 0, v___x_945_);
v___x_949_ = v___x_942_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_951_, 1, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_951_, 2, v_rightCount_939_);
lean_ctor_set(v_reuseFailAlloc_951_, 3, v_rightIndex_940_);
v___x_949_ = v_reuseFailAlloc_951_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; 
v___x_950_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_924_, v_val_926_, v___x_949_);
return v___x_950_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg___boxed(lean_object* v_histogram_956_, lean_object* v_index_957_, lean_object* v_val_958_){
_start:
{
uint32_t v_val_boxed_959_; lean_object* v_res_960_; 
v_val_boxed_959_ = lean_unbox_uint32(v_val_958_);
lean_dec(v_val_958_);
v_res_960_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(v_histogram_956_, v_index_957_, v_val_boxed_959_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(lean_object* v_upperBound_961_, lean_object* v_fst_962_, lean_object* v___x_963_, lean_object* v_fst_964_, lean_object* v_a_965_, lean_object* v_b_966_){
_start:
{
uint8_t v___x_967_; 
v___x_967_ = lean_nat_dec_lt(v_a_965_, v_upperBound_961_);
if (v___x_967_ == 0)
{
lean_dec(v_a_965_);
return v_b_966_;
}
else
{
lean_object* v___x_968_; uint32_t v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_968_ = l_Subarray_get___redArg(v_fst_964_, v_a_965_);
v___x_969_ = lean_unbox_uint32(v___x_968_);
lean_dec(v___x_968_);
lean_inc(v_a_965_);
v___x_970_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(v_b_966_, v_a_965_, v___x_969_);
v___x_971_ = lean_unsigned_to_nat(1u);
v___x_972_ = lean_nat_add(v_a_965_, v___x_971_);
lean_dec(v_a_965_);
v_a_965_ = v___x_972_;
v_b_966_ = v___x_970_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg___boxed(lean_object* v_upperBound_974_, lean_object* v_fst_975_, lean_object* v___x_976_, lean_object* v_fst_977_, lean_object* v_a_978_, lean_object* v_b_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(v_upperBound_974_, v_fst_975_, v___x_976_, v_fst_977_, v_a_978_, v_b_979_);
lean_dec_ref(v_fst_977_);
lean_dec(v___x_976_);
lean_dec_ref(v_fst_975_);
lean_dec(v_upperBound_974_);
return v_res_980_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v___x_981_ = lean_box(0);
v___x_982_ = lean_unsigned_to_nat(16u);
v___x_983_ = lean_mk_array(v___x_982_, v___x_981_);
return v___x_983_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v_hist_986_; 
v___x_984_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0);
v___x_985_ = lean_unsigned_to_nat(0u);
v_hist_986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_986_, 0, v___x_985_);
lean_ctor_set(v_hist_986_, 1, v___x_984_);
return v_hist_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(lean_object* v_left_987_, lean_object* v_right_988_){
_start:
{
lean_object* v___x_989_; lean_object* v_snd_990_; lean_object* v_fst_991_; lean_object* v_fst_992_; lean_object* v_snd_993_; lean_object* v___x_994_; lean_object* v_snd_995_; lean_object* v_fst_996_; lean_object* v_fst_997_; lean_object* v_snd_998_; lean_object* v_start_999_; lean_object* v_stop_1000_; lean_object* v___x_1001_; lean_object* v_hist_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v_start_1005_; lean_object* v_stop_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v_buckets_1009_; lean_object* v___x_1010_; lean_object* v___y_1012_; lean_object* v___x_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_989_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5(v_left_987_, v_right_988_);
v_snd_990_ = lean_ctor_get(v___x_989_, 1);
lean_inc(v_snd_990_);
v_fst_991_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_fst_991_);
lean_dec_ref(v___x_989_);
v_fst_992_ = lean_ctor_get(v_snd_990_, 0);
lean_inc(v_fst_992_);
v_snd_993_ = lean_ctor_get(v_snd_990_, 1);
lean_inc(v_snd_993_);
lean_dec(v_snd_990_);
v___x_994_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6(v_fst_992_, v_snd_993_);
v_snd_995_ = lean_ctor_get(v___x_994_, 1);
lean_inc(v_snd_995_);
v_fst_996_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_fst_996_);
lean_dec_ref(v___x_994_);
v_fst_997_ = lean_ctor_get(v_snd_995_, 0);
lean_inc(v_fst_997_);
v_snd_998_ = lean_ctor_get(v_snd_995_, 1);
lean_inc(v_snd_998_);
lean_dec(v_snd_995_);
v_start_999_ = lean_ctor_get(v_fst_996_, 1);
v_stop_1000_ = lean_ctor_get(v_fst_996_, 2);
v___x_1001_ = lean_unsigned_to_nat(0u);
v_hist_1002_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1);
v___x_1003_ = lean_nat_sub(v_stop_1000_, v_start_999_);
v___x_1004_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(v___x_1003_, v_fst_997_, v___x_1003_, v_fst_996_, v___x_1001_, v_hist_1002_);
v_start_1005_ = lean_ctor_get(v_fst_997_, 1);
v_stop_1006_ = lean_ctor_get(v_fst_997_, 2);
v___x_1007_ = lean_nat_sub(v_stop_1006_, v_start_1005_);
v___x_1008_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(v___x_1007_, v___x_1007_, v_fst_997_, v___x_1003_, v___x_1001_, v___x_1004_);
lean_dec(v___x_1003_);
lean_dec(v___x_1007_);
v_buckets_1009_ = lean_ctor_get(v___x_1008_, 1);
lean_inc_ref(v_buckets_1009_);
lean_dec_ref(v___x_1008_);
v___x_1010_ = lean_box(0);
v___x_1038_ = lean_box(0);
v___x_1039_ = lean_array_get_size(v_buckets_1009_);
v___x_1040_ = lean_nat_dec_lt(v___x_1001_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_dec_ref(v_buckets_1009_);
v___y_1012_ = v___x_1038_;
goto v___jp_1011_;
}
else
{
size_t v___x_1041_; size_t v___x_1042_; lean_object* v___x_1043_; 
v___x_1041_ = lean_usize_of_nat(v___x_1039_);
v___x_1042_ = ((size_t)0ULL);
v___x_1043_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9(v_buckets_1009_, v___x_1041_, v___x_1042_, v___x_1038_);
lean_dec_ref(v_buckets_1009_);
v___y_1012_ = v___x_1043_;
goto v___jp_1011_;
}
v___jp_1011_:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(v___y_1012_, v___x_1010_);
lean_dec(v___y_1012_);
if (lean_obj_tag(v___x_1013_) == 1)
{
lean_object* v_val_1014_; lean_object* v_snd_1015_; lean_object* v_snd_1016_; lean_object* v_fst_1017_; lean_object* v_fst_1018_; lean_object* v_snd_1019_; lean_object* v___x_1020_; lean_object* v_fst_1021_; lean_object* v_snd_1022_; lean_object* v___x_1023_; lean_object* v_fst_1024_; lean_object* v_snd_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; 
v_val_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_val_1014_);
lean_dec_ref_known(v___x_1013_, 1);
v_snd_1015_ = lean_ctor_get(v_val_1014_, 1);
lean_inc(v_snd_1015_);
lean_dec(v_val_1014_);
v_snd_1016_ = lean_ctor_get(v_snd_1015_, 1);
lean_inc(v_snd_1016_);
v_fst_1017_ = lean_ctor_get(v_snd_1015_, 0);
lean_inc(v_fst_1017_);
lean_dec(v_snd_1015_);
v_fst_1018_ = lean_ctor_get(v_snd_1016_, 0);
lean_inc(v_fst_1018_);
v_snd_1019_ = lean_ctor_get(v_snd_1016_, 1);
lean_inc(v_snd_1019_);
lean_dec(v_snd_1016_);
v___x_1020_ = l_Subarray_split___redArg(v_fst_996_, v_fst_1018_);
lean_dec(v_fst_1018_);
v_fst_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_fst_1021_);
v_snd_1022_ = lean_ctor_get(v___x_1020_, 1);
lean_inc(v_snd_1022_);
lean_dec_ref(v___x_1020_);
v___x_1023_ = l_Subarray_split___redArg(v_fst_997_, v_snd_1019_);
lean_dec(v_snd_1019_);
v_fst_1024_ = lean_ctor_get(v___x_1023_, 0);
lean_inc(v_fst_1024_);
v_snd_1025_ = lean_ctor_get(v___x_1023_, 1);
lean_inc(v_snd_1025_);
lean_dec_ref(v___x_1023_);
v___x_1026_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v_fst_1021_, v_fst_1024_);
v___x_1027_ = l_Array_append___redArg(v_fst_991_, v___x_1026_);
lean_dec_ref(v___x_1026_);
v___x_1028_ = lean_unsigned_to_nat(1u);
v___x_1029_ = lean_mk_empty_array_with_capacity(v___x_1028_);
v___x_1030_ = lean_array_push(v___x_1029_, v_fst_1017_);
v___x_1031_ = l_Array_append___redArg(v___x_1027_, v___x_1030_);
lean_dec_ref(v___x_1030_);
v___x_1032_ = l_Subarray_drop___redArg(v_snd_1022_, v___x_1028_);
v___x_1033_ = l_Subarray_drop___redArg(v_snd_1025_, v___x_1028_);
v___x_1034_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v___x_1032_, v___x_1033_);
v___x_1035_ = l_Array_append___redArg(v___x_1031_, v___x_1034_);
lean_dec_ref(v___x_1034_);
v___x_1036_ = l_Array_append___redArg(v___x_1035_, v_snd_998_);
lean_dec(v_snd_998_);
return v___x_1036_;
}
else
{
lean_object* v___x_1037_; 
lean_dec(v___x_1013_);
lean_dec(v_fst_997_);
lean_dec(v_fst_996_);
v___x_1037_ = l_Array_append___redArg(v_fst_991_, v_snd_998_);
lean_dec(v_snd_998_);
return v___x_1037_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(lean_object* v___x_1044_, lean_object* v_edited_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_fst_1047_; lean_object* v_snd_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1067_; 
v_fst_1047_ = lean_ctor_get(v_a_1046_, 0);
v_snd_1048_ = lean_ctor_get(v_a_1046_, 1);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_a_1046_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1050_ = v_a_1046_;
v_isShared_1051_ = v_isSharedCheck_1067_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_snd_1048_);
lean_inc(v_fst_1047_);
lean_dec(v_a_1046_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1067_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
uint8_t v___x_1052_; 
v___x_1052_ = lean_nat_dec_lt(v_snd_1048_, v___x_1044_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1054_; 
if (v_isShared_1051_ == 0)
{
v___x_1054_ = v___x_1050_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_fst_1047_);
lean_ctor_set(v_reuseFailAlloc_1055_, 1, v_snd_1048_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
else
{
uint8_t v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1060_; 
v___x_1056_ = 0;
v___x_1057_ = lean_array_fget_borrowed(v_edited_1045_, v_snd_1048_);
v___x_1058_ = lean_box(v___x_1056_);
lean_inc(v___x_1057_);
if (v_isShared_1051_ == 0)
{
lean_ctor_set(v___x_1050_, 1, v___x_1057_);
lean_ctor_set(v___x_1050_, 0, v___x_1058_);
v___x_1060_ = v___x_1050_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v___x_1057_);
v___x_1060_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1061_ = lean_array_push(v_fst_1047_, v___x_1060_);
v___x_1062_ = lean_unsigned_to_nat(1u);
v___x_1063_ = lean_nat_add(v_snd_1048_, v___x_1062_);
lean_dec(v_snd_1048_);
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1061_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
v_a_1046_ = v___x_1064_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg___boxed(lean_object* v___x_1068_, lean_object* v_edited_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1068_, v_edited_1069_, v_a_1070_);
lean_dec_ref(v_edited_1069_);
lean_dec(v___x_1068_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(size_t v_sz_1072_, size_t v_i_1073_, lean_object* v_bs_1074_){
_start:
{
uint8_t v___x_1075_; 
v___x_1075_ = lean_usize_dec_lt(v_i_1073_, v_sz_1072_);
if (v___x_1075_ == 0)
{
return v_bs_1074_;
}
else
{
lean_object* v_v_1076_; lean_object* v___x_1077_; lean_object* v_bs_x27_1078_; uint8_t v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; size_t v___x_1082_; size_t v___x_1083_; lean_object* v___x_1084_; 
v_v_1076_ = lean_array_uget(v_bs_1074_, v_i_1073_);
v___x_1077_ = lean_unsigned_to_nat(0u);
v_bs_x27_1078_ = lean_array_uset(v_bs_1074_, v_i_1073_, v___x_1077_);
v___x_1079_ = 1;
v___x_1080_ = lean_box(v___x_1079_);
v___x_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set(v___x_1081_, 1, v_v_1076_);
v___x_1082_ = ((size_t)1ULL);
v___x_1083_ = lean_usize_add(v_i_1073_, v___x_1082_);
v___x_1084_ = lean_array_uset(v_bs_x27_1078_, v_i_1073_, v___x_1081_);
v_i_1073_ = v___x_1083_;
v_bs_1074_ = v___x_1084_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8___boxed(lean_object* v_sz_1086_, lean_object* v_i_1087_, lean_object* v_bs_1088_){
_start:
{
size_t v_sz_boxed_1089_; size_t v_i_boxed_1090_; lean_object* v_res_1091_; 
v_sz_boxed_1089_ = lean_unbox_usize(v_sz_1086_);
lean_dec(v_sz_1086_);
v_i_boxed_1090_ = lean_unbox_usize(v_i_1087_);
lean_dec(v_i_1087_);
v_res_1091_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(v_sz_boxed_1089_, v_i_boxed_1090_, v_bs_1088_);
return v_res_1091_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = 65;
v___x_1093_ = lean_box_uint32(v___x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(lean_object* v___x_1094_, lean_object* v_original_1095_, uint32_t v_a_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v_fst_1098_; lean_object* v_snd_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1124_; 
v_fst_1098_ = lean_ctor_get(v_a_1097_, 0);
v_snd_1099_ = lean_ctor_get(v_a_1097_, 1);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_a_1097_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1101_ = v_a_1097_;
v_isShared_1102_ = v_isSharedCheck_1124_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_snd_1099_);
lean_inc(v_fst_1098_);
lean_dec(v_a_1097_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1124_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
uint8_t v___x_1103_; 
v___x_1103_ = lean_nat_dec_lt(v_snd_1099_, v___x_1094_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1105_; 
if (v_isShared_1102_ == 0)
{
v___x_1105_ = v___x_1101_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_fst_1098_);
lean_ctor_set(v_reuseFailAlloc_1106_, 1, v_snd_1099_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1108_; uint32_t v___x_1109_; uint8_t v___x_1110_; 
v___x_1107_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed__const__1;
v___x_1108_ = lean_array_get_borrowed(v___x_1107_, v_original_1095_, v_snd_1099_);
v___x_1109_ = lean_unbox_uint32(v___x_1108_);
v___x_1110_ = lean_uint32_dec_eq(v___x_1109_, v_a_1096_);
if (v___x_1110_ == 0)
{
uint8_t v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1114_; 
v___x_1111_ = 1;
v___x_1112_ = lean_box(v___x_1111_);
lean_inc(v___x_1108_);
if (v_isShared_1102_ == 0)
{
lean_ctor_set(v___x_1101_, 1, v___x_1108_);
lean_ctor_set(v___x_1101_, 0, v___x_1112_);
v___x_1114_ = v___x_1101_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1112_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v___x_1108_);
v___x_1114_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1115_ = lean_array_push(v_fst_1098_, v___x_1114_);
v___x_1116_ = lean_unsigned_to_nat(1u);
v___x_1117_ = lean_nat_add(v_snd_1099_, v___x_1116_);
lean_dec(v_snd_1099_);
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1115_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v_a_1097_ = v___x_1118_;
goto _start;
}
}
else
{
lean_object* v___x_1122_; 
if (v_isShared_1102_ == 0)
{
v___x_1122_ = v___x_1101_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_fst_1098_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_snd_1099_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed(lean_object* v___x_1125_, lean_object* v_original_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_){
_start:
{
uint32_t v_a_boxed_1129_; lean_object* v_res_1130_; 
v_a_boxed_1129_ = lean_unbox_uint32(v_a_1127_);
lean_dec(v_a_1127_);
v_res_1130_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1125_, v_original_1126_, v_a_boxed_1129_, v_a_1128_);
lean_dec_ref(v_original_1126_);
lean_dec(v___x_1125_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(lean_object* v___x_1131_, lean_object* v_edited_1132_, uint32_t v_a_1133_, lean_object* v_a_1134_){
_start:
{
lean_object* v_fst_1135_; lean_object* v_snd_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1161_; 
v_fst_1135_ = lean_ctor_get(v_a_1134_, 0);
v_snd_1136_ = lean_ctor_get(v_a_1134_, 1);
v_isSharedCheck_1161_ = !lean_is_exclusive(v_a_1134_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1138_ = v_a_1134_;
v_isShared_1139_ = v_isSharedCheck_1161_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_snd_1136_);
lean_inc(v_fst_1135_);
lean_dec(v_a_1134_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1161_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
uint8_t v___x_1140_; 
v___x_1140_ = lean_nat_dec_lt(v_snd_1136_, v___x_1131_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1142_; 
if (v_isShared_1139_ == 0)
{
v___x_1142_ = v___x_1138_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_fst_1135_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_snd_1136_);
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
lean_object* v___x_1144_; lean_object* v___x_1145_; uint32_t v___x_1146_; uint8_t v___x_1147_; 
v___x_1144_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed__const__1;
v___x_1145_ = lean_array_get_borrowed(v___x_1144_, v_edited_1132_, v_snd_1136_);
v___x_1146_ = lean_unbox_uint32(v___x_1145_);
v___x_1147_ = lean_uint32_dec_eq(v___x_1146_, v_a_1133_);
if (v___x_1147_ == 0)
{
uint8_t v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1148_ = 0;
v___x_1149_ = lean_box(v___x_1148_);
lean_inc(v___x_1145_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 1, v___x_1145_);
lean_ctor_set(v___x_1138_, 0, v___x_1149_);
v___x_1151_ = v___x_1138_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v___x_1145_);
v___x_1151_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1152_ = lean_array_push(v_fst_1135_, v___x_1151_);
v___x_1153_ = lean_unsigned_to_nat(1u);
v___x_1154_ = lean_nat_add(v_snd_1136_, v___x_1153_);
lean_dec(v_snd_1136_);
v___x_1155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1152_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v_a_1134_ = v___x_1155_;
goto _start;
}
}
else
{
lean_object* v___x_1159_; 
if (v_isShared_1139_ == 0)
{
v___x_1159_ = v___x_1138_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_fst_1135_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_snd_1136_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg___boxed(lean_object* v___x_1162_, lean_object* v_edited_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_){
_start:
{
uint32_t v_a_boxed_1166_; lean_object* v_res_1167_; 
v_a_boxed_1166_ = lean_unbox_uint32(v_a_1164_);
lean_dec(v_a_1164_);
v_res_1167_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1162_, v_edited_1163_, v_a_boxed_1166_, v_a_1165_);
lean_dec_ref(v_edited_1163_);
lean_dec(v___x_1162_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(lean_object* v___x_1168_, lean_object* v_original_1169_, lean_object* v___x_1170_, lean_object* v_edited_1171_, lean_object* v_as_1172_, size_t v_sz_1173_, size_t v_i_1174_, lean_object* v_b_1175_){
_start:
{
uint8_t v___x_1176_; 
v___x_1176_ = lean_usize_dec_lt(v_i_1174_, v_sz_1173_);
if (v___x_1176_ == 0)
{
return v_b_1175_;
}
else
{
lean_object* v_snd_1177_; lean_object* v_fst_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1227_; 
v_snd_1177_ = lean_ctor_get(v_b_1175_, 1);
v_fst_1178_ = lean_ctor_get(v_b_1175_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_b_1175_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1180_ = v_b_1175_;
v_isShared_1181_ = v_isSharedCheck_1227_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_snd_1177_);
lean_inc(v_fst_1178_);
lean_dec(v_b_1175_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1227_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v_fst_1182_; lean_object* v_snd_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1226_; 
v_fst_1182_ = lean_ctor_get(v_snd_1177_, 0);
v_snd_1183_ = lean_ctor_get(v_snd_1177_, 1);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_snd_1177_);
if (v_isSharedCheck_1226_ == 0)
{
v___x_1185_ = v_snd_1177_;
v_isShared_1186_ = v_isSharedCheck_1226_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_snd_1183_);
lean_inc(v_fst_1182_);
lean_dec(v_snd_1177_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1226_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v_a_1187_; lean_object* v___x_1189_; 
v_a_1187_ = lean_array_uget_borrowed(v_as_1172_, v_i_1174_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 1, v_fst_1182_);
lean_ctor_set(v___x_1185_, 0, v_fst_1178_);
v___x_1189_ = v___x_1185_;
goto v_reusejp_1188_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_fst_1178_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v_fst_1182_);
v___x_1189_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1188_;
}
v_reusejp_1188_:
{
uint32_t v___x_1190_; lean_object* v___x_1191_; lean_object* v_fst_1192_; lean_object* v_snd_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1224_; 
v___x_1190_ = lean_unbox_uint32(v_a_1187_);
v___x_1191_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1168_, v_original_1169_, v___x_1190_, v___x_1189_);
v_fst_1192_ = lean_ctor_get(v___x_1191_, 0);
v_snd_1193_ = lean_ctor_get(v___x_1191_, 1);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1195_ = v___x_1191_;
v_isShared_1196_ = v_isSharedCheck_1224_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_snd_1193_);
lean_inc(v_fst_1192_);
lean_dec(v___x_1191_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1224_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 1, v_snd_1183_);
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_fst_1192_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v_snd_1183_);
v___x_1198_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
uint32_t v___x_1199_; lean_object* v___x_1200_; lean_object* v_fst_1201_; lean_object* v_snd_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1222_; 
v___x_1199_ = lean_unbox_uint32(v_a_1187_);
v___x_1200_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1170_, v_edited_1171_, v___x_1199_, v___x_1198_);
v_fst_1201_ = lean_ctor_get(v___x_1200_, 0);
v_snd_1202_ = lean_ctor_get(v___x_1200_, 1);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1204_ = v___x_1200_;
v_isShared_1205_ = v_isSharedCheck_1222_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_snd_1202_);
lean_inc(v_fst_1201_);
lean_dec(v___x_1200_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1222_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
uint8_t v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; 
v___x_1206_ = 2;
v___x_1207_ = lean_box(v___x_1206_);
lean_inc(v_a_1187_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 1, v_a_1187_);
lean_ctor_set(v___x_1204_, 0, v___x_1207_);
v___x_1209_ = v___x_1204_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1207_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_a_1187_);
v___x_1209_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1215_; 
v___x_1210_ = lean_array_push(v_fst_1201_, v___x_1209_);
v___x_1211_ = lean_unsigned_to_nat(1u);
v___x_1212_ = lean_nat_add(v_snd_1193_, v___x_1211_);
lean_dec(v_snd_1193_);
v___x_1213_ = lean_nat_add(v_snd_1202_, v___x_1211_);
lean_dec(v_snd_1202_);
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 1, v___x_1213_);
lean_ctor_set(v___x_1180_, 0, v___x_1212_);
v___x_1215_ = v___x_1180_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
lean_object* v___x_1216_; size_t v___x_1217_; size_t v___x_1218_; 
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1210_);
lean_ctor_set(v___x_1216_, 1, v___x_1215_);
v___x_1217_ = ((size_t)1ULL);
v___x_1218_ = lean_usize_add(v_i_1174_, v___x_1217_);
v_i_1174_ = v___x_1218_;
v_b_1175_ = v___x_1216_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15___boxed(lean_object* v___x_1228_, lean_object* v_original_1229_, lean_object* v___x_1230_, lean_object* v_edited_1231_, lean_object* v_as_1232_, lean_object* v_sz_1233_, lean_object* v_i_1234_, lean_object* v_b_1235_){
_start:
{
size_t v_sz_boxed_1236_; size_t v_i_boxed_1237_; lean_object* v_res_1238_; 
v_sz_boxed_1236_ = lean_unbox_usize(v_sz_1233_);
lean_dec(v_sz_1233_);
v_i_boxed_1237_ = lean_unbox_usize(v_i_1234_);
lean_dec(v_i_1234_);
v_res_1238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(v___x_1228_, v_original_1229_, v___x_1230_, v_edited_1231_, v_as_1232_, v_sz_boxed_1236_, v_i_boxed_1237_, v_b_1235_);
lean_dec_ref(v_as_1232_);
lean_dec_ref(v_edited_1231_);
lean_dec(v___x_1230_);
lean_dec_ref(v_original_1229_);
lean_dec(v___x_1228_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(lean_object* v___x_1239_, lean_object* v_edited_1240_, lean_object* v___x_1241_, lean_object* v_original_1242_, lean_object* v_as_1243_, size_t v_sz_1244_, size_t v_i_1245_, lean_object* v_b_1246_){
_start:
{
uint8_t v___x_1247_; 
v___x_1247_ = lean_usize_dec_lt(v_i_1245_, v_sz_1244_);
if (v___x_1247_ == 0)
{
return v_b_1246_;
}
else
{
lean_object* v_snd_1248_; lean_object* v_fst_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1298_; 
v_snd_1248_ = lean_ctor_get(v_b_1246_, 1);
v_fst_1249_ = lean_ctor_get(v_b_1246_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_b_1246_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1251_ = v_b_1246_;
v_isShared_1252_ = v_isSharedCheck_1298_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_snd_1248_);
lean_inc(v_fst_1249_);
lean_dec(v_b_1246_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1298_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v_fst_1253_; lean_object* v_snd_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1297_; 
v_fst_1253_ = lean_ctor_get(v_snd_1248_, 0);
v_snd_1254_ = lean_ctor_get(v_snd_1248_, 1);
v_isSharedCheck_1297_ = !lean_is_exclusive(v_snd_1248_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1256_ = v_snd_1248_;
v_isShared_1257_ = v_isSharedCheck_1297_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_snd_1254_);
lean_inc(v_fst_1253_);
lean_dec(v_snd_1248_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1297_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v_a_1258_; lean_object* v___x_1260_; 
v_a_1258_ = lean_array_uget_borrowed(v_as_1243_, v_i_1245_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v_fst_1253_);
lean_ctor_set(v___x_1256_, 0, v_fst_1249_);
v___x_1260_ = v___x_1256_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_fst_1249_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_fst_1253_);
v___x_1260_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
uint32_t v___x_1261_; lean_object* v___x_1262_; lean_object* v_fst_1263_; lean_object* v_snd_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1295_; 
v___x_1261_ = lean_unbox_uint32(v_a_1258_);
v___x_1262_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1241_, v_original_1242_, v___x_1261_, v___x_1260_);
v_fst_1263_ = lean_ctor_get(v___x_1262_, 0);
v_snd_1264_ = lean_ctor_get(v___x_1262_, 1);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1266_ = v___x_1262_;
v_isShared_1267_ = v_isSharedCheck_1295_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_snd_1264_);
lean_inc(v_fst_1263_);
lean_dec(v___x_1262_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1295_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v_snd_1254_);
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_fst_1263_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_snd_1254_);
v___x_1269_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
uint32_t v___x_1270_; lean_object* v___x_1271_; lean_object* v_fst_1272_; lean_object* v_snd_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1293_; 
v___x_1270_ = lean_unbox_uint32(v_a_1258_);
v___x_1271_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1239_, v_edited_1240_, v___x_1270_, v___x_1269_);
v_fst_1272_ = lean_ctor_get(v___x_1271_, 0);
v_snd_1273_ = lean_ctor_get(v___x_1271_, 1);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1275_ = v___x_1271_;
v_isShared_1276_ = v_isSharedCheck_1293_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_snd_1273_);
lean_inc(v_fst_1272_);
lean_dec(v___x_1271_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1293_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
uint8_t v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1277_ = 2;
v___x_1278_ = lean_box(v___x_1277_);
lean_inc(v_a_1258_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 1, v_a_1258_);
lean_ctor_set(v___x_1275_, 0, v___x_1278_);
v___x_1280_ = v___x_1275_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1278_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_a_1258_);
v___x_1280_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1286_; 
v___x_1281_ = lean_array_push(v_fst_1272_, v___x_1280_);
v___x_1282_ = lean_unsigned_to_nat(1u);
v___x_1283_ = lean_nat_add(v_snd_1264_, v___x_1282_);
lean_dec(v_snd_1264_);
v___x_1284_ = lean_nat_add(v_snd_1273_, v___x_1282_);
lean_dec(v_snd_1273_);
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 1, v___x_1284_);
lean_ctor_set(v___x_1251_, 0, v___x_1283_);
v___x_1286_ = v___x_1251_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v___x_1283_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v___x_1284_);
v___x_1286_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1287_; size_t v___x_1288_; size_t v___x_1289_; lean_object* v___x_1290_; 
v___x_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1287_, 0, v___x_1281_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = ((size_t)1ULL);
v___x_1289_ = lean_usize_add(v_i_1245_, v___x_1288_);
v___x_1290_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(v___x_1241_, v_original_1242_, v___x_1239_, v_edited_1240_, v_as_1243_, v_sz_1244_, v___x_1289_, v___x_1287_);
return v___x_1290_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5___boxed(lean_object* v___x_1299_, lean_object* v_edited_1300_, lean_object* v___x_1301_, lean_object* v_original_1302_, lean_object* v_as_1303_, lean_object* v_sz_1304_, lean_object* v_i_1305_, lean_object* v_b_1306_){
_start:
{
size_t v_sz_boxed_1307_; size_t v_i_boxed_1308_; lean_object* v_res_1309_; 
v_sz_boxed_1307_ = lean_unbox_usize(v_sz_1304_);
lean_dec(v_sz_1304_);
v_i_boxed_1308_ = lean_unbox_usize(v_i_1305_);
lean_dec(v_i_1305_);
v_res_1309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v___x_1299_, v_edited_1300_, v___x_1301_, v_original_1302_, v_as_1303_, v_sz_boxed_1307_, v_i_boxed_1308_, v_b_1306_);
lean_dec_ref(v_as_1303_);
lean_dec_ref(v_original_1302_);
lean_dec(v___x_1301_);
lean_dec_ref(v_edited_1300_);
lean_dec(v___x_1299_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(lean_object* v_original_1317_, lean_object* v_edited_1318_){
_start:
{
lean_object* v_i_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v_i_1319_ = lean_unsigned_to_nat(0u);
v___x_1320_ = lean_array_get_size(v_original_1317_);
v___x_1321_ = lean_nat_dec_lt(v_i_1319_, v___x_1320_);
if (v___x_1321_ == 0)
{
size_t v_sz_1322_; size_t v___x_1323_; lean_object* v___x_1324_; 
lean_dec_ref(v_original_1317_);
v_sz_1322_ = lean_array_size(v_edited_1318_);
v___x_1323_ = ((size_t)0ULL);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(v_sz_1322_, v___x_1323_, v_edited_1318_);
return v___x_1324_;
}
else
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = lean_array_get_size(v_edited_1318_);
v___x_1326_ = lean_nat_dec_lt(v_i_1319_, v___x_1325_);
if (v___x_1326_ == 0)
{
size_t v_sz_1327_; size_t v___x_1328_; lean_object* v___x_1329_; 
lean_dec_ref(v_edited_1318_);
v_sz_1327_ = lean_array_size(v_original_1317_);
v___x_1328_ = ((size_t)0ULL);
v___x_1329_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(v_sz_1327_, v___x_1328_, v_original_1317_);
return v___x_1329_;
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v_ds_1332_; lean_object* v___x_1333_; size_t v_sz_1334_; size_t v___x_1335_; lean_object* v___x_1336_; lean_object* v_snd_1337_; lean_object* v_fst_1338_; lean_object* v_fst_1339_; lean_object* v_snd_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1359_; 
lean_inc_ref(v_original_1317_);
v___x_1330_ = l_Array_toSubarray___redArg(v_original_1317_, v_i_1319_, v___x_1320_);
lean_inc_ref(v_edited_1318_);
v___x_1331_ = l_Array_toSubarray___redArg(v_edited_1318_, v_i_1319_, v___x_1325_);
v_ds_1332_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v___x_1330_, v___x_1331_);
v___x_1333_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__2));
v_sz_1334_ = lean_array_size(v_ds_1332_);
v___x_1335_ = ((size_t)0ULL);
v___x_1336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v___x_1325_, v_edited_1318_, v___x_1320_, v_original_1317_, v_ds_1332_, v_sz_1334_, v___x_1335_, v___x_1333_);
lean_dec_ref(v_ds_1332_);
v_snd_1337_ = lean_ctor_get(v___x_1336_, 1);
lean_inc(v_snd_1337_);
v_fst_1338_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_fst_1338_);
lean_dec_ref(v___x_1336_);
v_fst_1339_ = lean_ctor_get(v_snd_1337_, 0);
v_snd_1340_ = lean_ctor_get(v_snd_1337_, 1);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_snd_1337_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1342_ = v_snd_1337_;
v_isShared_1343_ = v_isSharedCheck_1359_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_snd_1340_);
lean_inc(v_fst_1339_);
lean_dec(v_snd_1337_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1359_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 1, v_fst_1339_);
lean_ctor_set(v___x_1342_, 0, v_fst_1338_);
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_fst_1338_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v_fst_1339_);
v___x_1345_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
lean_object* v___x_1346_; lean_object* v_fst_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1356_; 
v___x_1346_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_1320_, v_original_1317_, v___x_1345_);
lean_dec_ref(v_original_1317_);
v_fst_1347_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1356_ == 0)
{
lean_object* v_unused_1357_; 
v_unused_1357_ = lean_ctor_get(v___x_1346_, 1);
lean_dec(v_unused_1357_);
v___x_1349_ = v___x_1346_;
v_isShared_1350_ = v_isSharedCheck_1356_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_fst_1347_);
lean_dec(v___x_1346_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1356_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 1, v_snd_1340_);
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_fst_1347_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_snd_1340_);
v___x_1352_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1353_; lean_object* v_fst_1354_; 
v___x_1353_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1325_, v_edited_1318_, v___x_1352_);
lean_dec_ref(v_edited_1318_);
v_fst_1354_ = lean_ctor_get(v___x_1353_, 0);
lean_inc(v_fst_1354_);
lean_dec_ref(v___x_1353_);
return v_fst_1354_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(lean_object* v_s_1360_, lean_object* v_a_1361_, uint8_t v_b_1362_){
_start:
{
lean_object* v_str_1363_; lean_object* v_startInclusive_1364_; lean_object* v_endExclusive_1365_; lean_object* v___x_1366_; uint8_t v_decide_1367_; 
v_str_1363_ = lean_ctor_get(v_s_1360_, 0);
v_startInclusive_1364_ = lean_ctor_get(v_s_1360_, 1);
v_endExclusive_1365_ = lean_ctor_get(v_s_1360_, 2);
v___x_1366_ = lean_nat_sub(v_endExclusive_1365_, v_startInclusive_1364_);
v_decide_1367_ = lean_nat_dec_eq(v_a_1361_, v___x_1366_);
lean_dec(v___x_1366_);
if (v_decide_1367_ == 0)
{
lean_object* v___x_1368_; uint32_t v___x_1369_; uint32_t v___x_1370_; uint8_t v___x_1371_; 
v___x_1368_ = lean_nat_add(v_startInclusive_1364_, v_a_1361_);
lean_dec(v_a_1361_);
v___x_1369_ = lean_string_utf8_get_fast(v_str_1363_, v___x_1368_);
v___x_1370_ = 10;
v___x_1371_ = lean_uint32_dec_eq(v___x_1369_, v___x_1370_);
if (v___x_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = lean_string_utf8_next_fast(v_str_1363_, v___x_1368_);
lean_dec(v___x_1368_);
v___x_1373_ = lean_nat_sub(v___x_1372_, v_startInclusive_1364_);
v_a_1361_ = v___x_1373_;
v_b_1362_ = v___x_1371_;
goto _start;
}
else
{
lean_dec(v___x_1368_);
return v___x_1371_;
}
}
else
{
lean_dec(v_a_1361_);
return v_b_1362_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg___boxed(lean_object* v_s_1375_, lean_object* v_a_1376_, lean_object* v_b_1377_){
_start:
{
uint8_t v_b_boxed_1378_; uint8_t v_res_1379_; lean_object* v_r_1380_; 
v_b_boxed_1378_ = lean_unbox(v_b_1377_);
v_res_1379_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1375_, v_a_1376_, v_b_boxed_1378_);
lean_dec_ref(v_s_1375_);
v_r_1380_ = lean_box(v_res_1379_);
return v_r_1380_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(lean_object* v_s_1381_){
_start:
{
lean_object* v_searcher_1382_; uint8_t v___x_1383_; uint8_t v___x_1384_; 
v_searcher_1382_ = lean_unsigned_to_nat(0u);
v___x_1383_ = 0;
v___x_1384_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1381_, v_searcher_1382_, v___x_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0___boxed(lean_object* v_s_1385_){
_start:
{
uint8_t v_res_1386_; lean_object* v_r_1387_; 
v_res_1386_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v_s_1385_);
lean_dec_ref(v_s_1385_);
v_r_1387_ = lean_box(v_res_1386_);
return v_r_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(lean_object* v_oldWs_1388_, lean_object* v_newWs_1389_){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; 
v___x_1390_ = lean_unsigned_to_nat(0u);
v___x_1391_ = lean_string_utf8_byte_size(v_oldWs_1388_);
lean_inc_ref(v_oldWs_1388_);
v___x_1392_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1392_, 0, v_oldWs_1388_);
lean_ctor_set(v___x_1392_, 1, v___x_1390_);
lean_ctor_set(v___x_1392_, 2, v___x_1391_);
v___x_1393_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_1392_);
lean_dec_ref_known(v___x_1392_, 3);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1394_ = lean_string_data(v_oldWs_1388_);
v___x_1395_ = lean_array_mk(v___x_1394_);
v___x_1396_ = lean_string_data(v_newWs_1389_);
v___x_1397_ = lean_array_mk(v___x_1396_);
v___x_1398_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_1395_, v___x_1397_);
v___x_1399_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_1398_);
lean_dec_ref(v___x_1398_);
return v___x_1399_;
}
else
{
uint8_t v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_dec_ref(v_oldWs_1388_);
v___x_1400_ = 2;
v___x_1401_ = lean_box(v___x_1400_);
v___x_1402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
lean_ctor_set(v___x_1402_, 1, v_newWs_1389_);
v___x_1403_ = lean_unsigned_to_nat(1u);
v___x_1404_ = lean_mk_empty_array_with_capacity(v___x_1403_);
v___x_1405_ = lean_array_push(v___x_1404_, v___x_1402_);
return v___x_1405_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(lean_object* v_s_1406_, lean_object* v_inst_1407_, lean_object* v_R_1408_, lean_object* v_a_1409_, uint8_t v_b_1410_, lean_object* v_c_1411_){
_start:
{
uint8_t v___x_1412_; 
v___x_1412_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1406_, v_a_1409_, v_b_1410_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___boxed(lean_object* v_s_1413_, lean_object* v_inst_1414_, lean_object* v_R_1415_, lean_object* v_a_1416_, lean_object* v_b_1417_, lean_object* v_c_1418_){
_start:
{
uint8_t v_b_boxed_1419_; uint8_t v_res_1420_; lean_object* v_r_1421_; 
v_b_boxed_1419_ = lean_unbox(v_b_1417_);
v_res_1420_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(v_s_1413_, v_inst_1414_, v_R_1415_, v_a_1416_, v_b_boxed_1419_, v_c_1418_);
lean_dec_ref(v_s_1413_);
v_r_1421_ = lean_box(v_res_1420_);
return v_r_1421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(lean_object* v___x_1422_, lean_object* v_original_1423_, uint32_t v_a_1424_, lean_object* v_inst_1425_, lean_object* v_a_1426_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1422_, v_original_1423_, v_a_1424_, v_a_1426_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___boxed(lean_object* v___x_1428_, lean_object* v_original_1429_, lean_object* v_a_1430_, lean_object* v_inst_1431_, lean_object* v_a_1432_){
_start:
{
uint32_t v_a_boxed_1433_; lean_object* v_res_1434_; 
v_a_boxed_1433_ = lean_unbox_uint32(v_a_1430_);
lean_dec(v_a_1430_);
v_res_1434_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v___x_1428_, v_original_1429_, v_a_boxed_1433_, v_inst_1431_, v_a_1432_);
lean_dec_ref(v_original_1429_);
lean_dec(v___x_1428_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(lean_object* v___x_1435_, lean_object* v_edited_1436_, uint32_t v_a_1437_, lean_object* v_inst_1438_, lean_object* v_a_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1435_, v_edited_1436_, v_a_1437_, v_a_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___boxed(lean_object* v___x_1441_, lean_object* v_edited_1442_, lean_object* v_a_1443_, lean_object* v_inst_1444_, lean_object* v_a_1445_){
_start:
{
uint32_t v_a_boxed_1446_; lean_object* v_res_1447_; 
v_a_boxed_1446_ = lean_unbox_uint32(v_a_1443_);
lean_dec(v_a_1443_);
v_res_1447_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(v___x_1441_, v_edited_1442_, v_a_boxed_1446_, v_inst_1444_, v_a_1445_);
lean_dec_ref(v_edited_1442_);
lean_dec(v___x_1441_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(lean_object* v___x_1448_, lean_object* v_original_1449_, lean_object* v_inst_1450_, lean_object* v_a_1451_){
_start:
{
lean_object* v___x_1452_; 
v___x_1452_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_1448_, v_original_1449_, v_a_1451_);
return v___x_1452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___boxed(lean_object* v___x_1453_, lean_object* v_original_1454_, lean_object* v_inst_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(v___x_1453_, v_original_1454_, v_inst_1455_, v_a_1456_);
lean_dec_ref(v_original_1454_);
lean_dec(v___x_1453_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(lean_object* v___x_1458_, lean_object* v_edited_1459_, lean_object* v_inst_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1458_, v_edited_1459_, v_a_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___boxed(lean_object* v___x_1463_, lean_object* v_edited_1464_, lean_object* v_inst_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(v___x_1463_, v_edited_1464_, v_inst_1465_, v_a_1466_);
lean_dec_ref(v_edited_1464_);
lean_dec(v___x_1463_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7(lean_object* v_as_1468_, lean_object* v_as_x27_1469_, lean_object* v_b_1470_, lean_object* v_a_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(v_as_x27_1469_, v_b_1470_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___boxed(lean_object* v_as_1473_, lean_object* v_as_x27_1474_, lean_object* v_b_1475_, lean_object* v_a_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7(v_as_1473_, v_as_x27_1474_, v_b_1475_, v_a_1476_);
lean_dec(v_as_x27_1474_);
lean_dec(v_as_1473_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10(lean_object* v_lsize_1478_, lean_object* v_rsize_1479_, lean_object* v_histogram_1480_, lean_object* v_index_1481_, uint32_t v_val_1482_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(v_histogram_1480_, v_index_1481_, v_val_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___boxed(lean_object* v_lsize_1484_, lean_object* v_rsize_1485_, lean_object* v_histogram_1486_, lean_object* v_index_1487_, lean_object* v_val_1488_){
_start:
{
uint32_t v_val_boxed_1489_; lean_object* v_res_1490_; 
v_val_boxed_1489_ = lean_unbox_uint32(v_val_1488_);
lean_dec(v_val_1488_);
v_res_1490_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10(v_lsize_1484_, v_rsize_1485_, v_histogram_1486_, v_index_1487_, v_val_boxed_1489_);
lean_dec(v_rsize_1485_);
lean_dec(v_lsize_1484_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11(lean_object* v_upperBound_1491_, lean_object* v___x_1492_, lean_object* v_fst_1493_, lean_object* v___x_1494_, lean_object* v_inst_1495_, lean_object* v_R_1496_, lean_object* v_a_1497_, lean_object* v_b_1498_, lean_object* v_c_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(v_upperBound_1491_, v___x_1492_, v_fst_1493_, v___x_1494_, v_a_1497_, v_b_1498_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___boxed(lean_object* v_upperBound_1501_, lean_object* v___x_1502_, lean_object* v_fst_1503_, lean_object* v___x_1504_, lean_object* v_inst_1505_, lean_object* v_R_1506_, lean_object* v_a_1507_, lean_object* v_b_1508_, lean_object* v_c_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11(v_upperBound_1501_, v___x_1502_, v_fst_1503_, v___x_1504_, v_inst_1505_, v_R_1506_, v_a_1507_, v_b_1508_, v_c_1509_);
lean_dec(v___x_1504_);
lean_dec_ref(v_fst_1503_);
lean_dec(v___x_1502_);
lean_dec(v_upperBound_1501_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12(lean_object* v_lsize_1511_, lean_object* v_rsize_1512_, lean_object* v_histogram_1513_, lean_object* v_index_1514_, uint32_t v_val_1515_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(v_histogram_1513_, v_index_1514_, v_val_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___boxed(lean_object* v_lsize_1517_, lean_object* v_rsize_1518_, lean_object* v_histogram_1519_, lean_object* v_index_1520_, lean_object* v_val_1521_){
_start:
{
uint32_t v_val_boxed_1522_; lean_object* v_res_1523_; 
v_val_boxed_1522_ = lean_unbox_uint32(v_val_1521_);
lean_dec(v_val_1521_);
v_res_1523_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12(v_lsize_1517_, v_rsize_1518_, v_histogram_1519_, v_index_1520_, v_val_boxed_1522_);
lean_dec(v_rsize_1518_);
lean_dec(v_lsize_1517_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13(lean_object* v_upperBound_1524_, lean_object* v_fst_1525_, lean_object* v___x_1526_, lean_object* v_fst_1527_, lean_object* v_inst_1528_, lean_object* v_R_1529_, lean_object* v_a_1530_, lean_object* v_b_1531_, lean_object* v_c_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(v_upperBound_1524_, v_fst_1525_, v___x_1526_, v_fst_1527_, v_a_1530_, v_b_1531_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___boxed(lean_object* v_upperBound_1534_, lean_object* v_fst_1535_, lean_object* v___x_1536_, lean_object* v_fst_1537_, lean_object* v_inst_1538_, lean_object* v_R_1539_, lean_object* v_a_1540_, lean_object* v_b_1541_, lean_object* v_c_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13(v_upperBound_1534_, v_fst_1535_, v___x_1536_, v_fst_1537_, v_inst_1538_, v_R_1539_, v_a_1540_, v_b_1541_, v_c_1542_);
lean_dec_ref(v_fst_1537_);
lean_dec(v___x_1536_);
lean_dec_ref(v_fst_1535_);
lean_dec(v_upperBound_1534_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13(lean_object* v_00_u03b2_1544_, lean_object* v_m_1545_, uint32_t v_a_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_m_1545_, v_a_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___boxed(lean_object* v_00_u03b2_1548_, lean_object* v_m_1549_, lean_object* v_a_1550_){
_start:
{
uint32_t v_a_boxed_1551_; lean_object* v_res_1552_; 
v_a_boxed_1551_ = lean_unbox_uint32(v_a_1550_);
lean_dec(v_a_1550_);
v_res_1552_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13(v_00_u03b2_1548_, v_m_1549_, v_a_boxed_1551_);
lean_dec_ref(v_m_1549_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14(lean_object* v_00_u03b2_1553_, lean_object* v_m_1554_, uint32_t v_a_1555_, lean_object* v_b_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_m_1554_, v_a_1555_, v_b_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___boxed(lean_object* v_00_u03b2_1558_, lean_object* v_m_1559_, lean_object* v_a_1560_, lean_object* v_b_1561_){
_start:
{
uint32_t v_a_boxed_1562_; lean_object* v_res_1563_; 
v_a_boxed_1562_ = lean_unbox_uint32(v_a_1560_);
lean_dec(v_a_1560_);
v_res_1563_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14(v_00_u03b2_1558_, v_m_1559_, v_a_boxed_1562_, v_b_1561_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14(lean_object* v_inst_1564_, lean_object* v_R_1565_, lean_object* v_a_1566_, lean_object* v_b_1567_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(v_a_1566_, v_b_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20(lean_object* v_00_u03b2_1569_, uint32_t v_a_1570_, lean_object* v_x_1571_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg(v_a_1570_, v_x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___boxed(lean_object* v_00_u03b2_1573_, lean_object* v_a_1574_, lean_object* v_x_1575_){
_start:
{
uint32_t v_a_boxed_1576_; lean_object* v_res_1577_; 
v_a_boxed_1576_ = lean_unbox_uint32(v_a_1574_);
lean_dec(v_a_1574_);
v_res_1577_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20(v_00_u03b2_1573_, v_a_boxed_1576_, v_x_1575_);
lean_dec(v_x_1575_);
return v_res_1577_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22(lean_object* v_00_u03b2_1578_, uint32_t v_a_1579_, lean_object* v_x_1580_){
_start:
{
uint8_t v___x_1581_; 
v___x_1581_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(v_a_1579_, v_x_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___boxed(lean_object* v_00_u03b2_1582_, lean_object* v_a_1583_, lean_object* v_x_1584_){
_start:
{
uint32_t v_a_boxed_1585_; uint8_t v_res_1586_; lean_object* v_r_1587_; 
v_a_boxed_1585_ = lean_unbox_uint32(v_a_1583_);
lean_dec(v_a_1583_);
v_res_1586_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22(v_00_u03b2_1582_, v_a_boxed_1585_, v_x_1584_);
lean_dec(v_x_1584_);
v_r_1587_ = lean_box(v_res_1586_);
return v_r_1587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23(lean_object* v_00_u03b2_1588_, lean_object* v_data_1589_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23___redArg(v_data_1589_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24(lean_object* v_00_u03b2_1591_, uint32_t v_a_1592_, lean_object* v_b_1593_, lean_object* v_x_1594_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(v_a_1592_, v_b_1593_, v_x_1594_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___boxed(lean_object* v_00_u03b2_1596_, lean_object* v_a_1597_, lean_object* v_b_1598_, lean_object* v_x_1599_){
_start:
{
uint32_t v_a_boxed_1600_; lean_object* v_res_1601_; 
v_a_boxed_1600_ = lean_unbox_uint32(v_a_1597_);
lean_dec(v_a_1597_);
v_res_1601_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24(v_00_u03b2_1596_, v_a_boxed_1600_, v_b_1598_, v_x_1599_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28(lean_object* v_00_u03b2_1602_, lean_object* v_i_1603_, lean_object* v_source_1604_, lean_object* v_target_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28___redArg(v_i_1603_, v_source_1604_, v_target_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_1607_, lean_object* v_x_1608_, lean_object* v_x_1609_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29___redArg(v_x_1608_, v_x_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(lean_object* v_s_1611_, lean_object* v_stopPos_1612_, lean_object* v_i_1613_){
_start:
{
uint8_t v___y_1615_; lean_object* v___x_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v___x_1618_ = lean_unsigned_to_nat(1u);
v___x_1619_ = lean_nat_add(v_i_1613_, v___x_1618_);
v___x_1620_ = lean_nat_dec_le(v___x_1619_, v_stopPos_1612_);
lean_dec(v___x_1619_);
if (v___x_1620_ == 0)
{
return v_i_1613_;
}
else
{
if (v___x_1620_ == 0)
{
v___y_1615_ = v___x_1620_;
goto v___jp_1614_;
}
else
{
uint32_t v___x_1621_; uint32_t v___x_1622_; uint8_t v___x_1623_; 
v___x_1621_ = lean_string_utf8_get(v_s_1611_, v_i_1613_);
v___x_1622_ = 32;
v___x_1623_ = lean_uint32_dec_eq(v___x_1621_, v___x_1622_);
if (v___x_1623_ == 0)
{
uint32_t v___x_1624_; uint8_t v___x_1625_; 
v___x_1624_ = 9;
v___x_1625_ = lean_uint32_dec_eq(v___x_1621_, v___x_1624_);
if (v___x_1625_ == 0)
{
uint32_t v___x_1626_; uint8_t v___x_1627_; 
v___x_1626_ = 13;
v___x_1627_ = lean_uint32_dec_eq(v___x_1621_, v___x_1626_);
if (v___x_1627_ == 0)
{
uint32_t v___x_1628_; uint8_t v___x_1629_; 
v___x_1628_ = 10;
v___x_1629_ = lean_uint32_dec_eq(v___x_1621_, v___x_1628_);
v___y_1615_ = v___x_1629_;
goto v___jp_1614_;
}
else
{
v___y_1615_ = v___x_1627_;
goto v___jp_1614_;
}
}
else
{
v___y_1615_ = v___x_1625_;
goto v___jp_1614_;
}
}
else
{
v___y_1615_ = v___x_1623_;
goto v___jp_1614_;
}
}
}
v___jp_1614_:
{
if (v___y_1615_ == 0)
{
return v_i_1613_;
}
else
{
lean_object* v___x_1616_; 
v___x_1616_ = lean_string_utf8_next(v_s_1611_, v_i_1613_);
lean_dec(v_i_1613_);
v_i_1613_ = v___x_1616_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0___boxed(lean_object* v_s_1630_, lean_object* v_stopPos_1631_, lean_object* v_i_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1630_, v_stopPos_1631_, v_i_1632_);
lean_dec(v_stopPos_1631_);
lean_dec_ref(v_s_1630_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(lean_object* v_s_1634_, lean_object* v_b_1635_, lean_object* v_i_1636_, lean_object* v_r_1637_, lean_object* v_ws_1638_){
_start:
{
uint8_t v___x_1647_; 
v___x_1647_ = lean_string_utf8_at_end(v_s_1634_, v_i_1636_);
if (v___x_1647_ == 0)
{
uint32_t v___x_1648_; uint32_t v___x_1649_; uint8_t v___x_1650_; 
v___x_1648_ = lean_string_utf8_get(v_s_1634_, v_i_1636_);
v___x_1649_ = 32;
v___x_1650_ = lean_uint32_dec_eq(v___x_1648_, v___x_1649_);
if (v___x_1650_ == 0)
{
uint32_t v___x_1651_; uint8_t v___x_1652_; 
v___x_1651_ = 9;
v___x_1652_ = lean_uint32_dec_eq(v___x_1648_, v___x_1651_);
if (v___x_1652_ == 0)
{
uint32_t v___x_1653_; uint8_t v___x_1654_; 
v___x_1653_ = 13;
v___x_1654_ = lean_uint32_dec_eq(v___x_1648_, v___x_1653_);
if (v___x_1654_ == 0)
{
uint32_t v___x_1655_; uint8_t v___x_1656_; 
v___x_1655_ = 10;
v___x_1656_ = lean_uint32_dec_eq(v___x_1648_, v___x_1655_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; 
v___x_1657_ = lean_string_utf8_next(v_s_1634_, v_i_1636_);
lean_dec(v_i_1636_);
v_i_1636_ = v___x_1657_;
goto _start;
}
else
{
goto v___jp_1639_;
}
}
else
{
goto v___jp_1639_;
}
}
else
{
goto v___jp_1639_;
}
}
else
{
goto v___jp_1639_;
}
}
else
{
lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1659_ = lean_string_utf8_extract(v_s_1634_, v_b_1635_, v_i_1636_);
lean_dec(v_i_1636_);
lean_dec(v_b_1635_);
v___x_1660_ = lean_array_push(v_r_1637_, v___x_1659_);
v___x_1661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1661_, 0, v___x_1660_);
lean_ctor_set(v___x_1661_, 1, v_ws_1638_);
return v___x_1661_;
}
v___jp_1639_:
{
lean_object* v___x_1640_; lean_object* v_e_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v___x_1640_ = lean_string_utf8_byte_size(v_s_1634_);
lean_inc(v_i_1636_);
v_e_1641_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1634_, v___x_1640_, v_i_1636_);
v___x_1642_ = lean_string_utf8_extract(v_s_1634_, v_b_1635_, v_i_1636_);
lean_dec(v_b_1635_);
v___x_1643_ = lean_array_push(v_r_1637_, v___x_1642_);
v___x_1644_ = lean_string_utf8_extract(v_s_1634_, v_i_1636_, v_e_1641_);
lean_dec(v_i_1636_);
v___x_1645_ = lean_array_push(v_ws_1638_, v___x_1644_);
lean_inc(v_e_1641_);
v_b_1635_ = v_e_1641_;
v_i_1636_ = v_e_1641_;
v_r_1637_ = v___x_1643_;
v_ws_1638_ = v___x_1645_;
goto _start;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(lean_object* v_x_1743_, lean_object* v_x_1744_){
_start:
{
if (lean_obj_tag(v_x_1744_) == 0)
{
lean_inc(v_x_1743_);
return v_x_1743_;
}
else
{
lean_object* v_key_1745_; lean_object* v_value_1746_; lean_object* v_tail_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v_key_1745_ = lean_ctor_get(v_x_1744_, 0);
v_value_1746_ = lean_ctor_get(v_x_1744_, 1);
v_tail_1747_ = lean_ctor_get(v_x_1744_, 2);
v___x_1748_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(v_x_1743_, v_tail_1747_);
lean_inc(v_value_1746_);
lean_inc(v_key_1745_);
v___x_1749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1749_, 0, v_key_1745_);
lean_ctor_set(v___x_1749_, 1, v_value_1746_);
v___x_1750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1750_, 0, v___x_1749_);
lean_ctor_set(v___x_1750_, 1, v___x_1748_);
return v___x_1750_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7___boxed(lean_object* v_x_1751_, lean_object* v_x_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(v_x_1751_, v_x_1752_);
lean_dec(v_x_1752_);
lean_dec(v_x_1751_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8(lean_object* v_as_1754_, size_t v_i_1755_, size_t v_stop_1756_, lean_object* v_b_1757_){
_start:
{
uint8_t v___x_1758_; 
v___x_1758_ = lean_usize_dec_eq(v_i_1755_, v_stop_1756_);
if (v___x_1758_ == 0)
{
size_t v___x_1759_; size_t v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1759_ = ((size_t)1ULL);
v___x_1760_ = lean_usize_sub(v_i_1755_, v___x_1759_);
v___x_1761_ = lean_array_uget_borrowed(v_as_1754_, v___x_1760_);
v___x_1762_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(v_b_1757_, v___x_1761_);
lean_dec(v_b_1757_);
v_i_1755_ = v___x_1760_;
v_b_1757_ = v___x_1762_;
goto _start;
}
else
{
return v_b_1757_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8___boxed(lean_object* v_as_1764_, lean_object* v_i_1765_, lean_object* v_stop_1766_, lean_object* v_b_1767_){
_start:
{
size_t v_i_boxed_1768_; size_t v_stop_boxed_1769_; lean_object* v_res_1770_; 
v_i_boxed_1768_ = lean_unbox_usize(v_i_1765_);
lean_dec(v_i_1765_);
v_stop_boxed_1769_ = lean_unbox_usize(v_stop_1766_);
lean_dec(v_stop_1766_);
v_res_1770_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8(v_as_1764_, v_i_boxed_1768_, v_stop_boxed_1769_, v_b_1767_);
lean_dec_ref(v_as_1764_);
return v_res_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4_spec__6(lean_object* v_left_1771_, lean_object* v_right_1772_, lean_object* v_pref_1773_){
_start:
{
lean_object* v_start_1774_; lean_object* v_stop_1775_; lean_object* v_start_1776_; lean_object* v_stop_1777_; lean_object* v_i_1778_; uint8_t v___y_1780_; lean_object* v___x_1794_; uint8_t v___x_1795_; 
v_start_1774_ = lean_ctor_get(v_left_1771_, 1);
v_stop_1775_ = lean_ctor_get(v_left_1771_, 2);
v_start_1776_ = lean_ctor_get(v_right_1772_, 1);
v_stop_1777_ = lean_ctor_get(v_right_1772_, 2);
v_i_1778_ = lean_array_get_size(v_pref_1773_);
v___x_1794_ = lean_nat_sub(v_stop_1775_, v_start_1774_);
v___x_1795_ = lean_nat_dec_lt(v_i_1778_, v___x_1794_);
lean_dec(v___x_1794_);
if (v___x_1795_ == 0)
{
v___y_1780_ = v___x_1795_;
goto v___jp_1779_;
}
else
{
lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1796_ = lean_nat_sub(v_stop_1777_, v_start_1776_);
v___x_1797_ = lean_nat_dec_lt(v_i_1778_, v___x_1796_);
lean_dec(v___x_1796_);
v___y_1780_ = v___x_1797_;
goto v___jp_1779_;
}
v___jp_1779_:
{
if (v___y_1780_ == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1781_ = l_Subarray_drop___redArg(v_left_1771_, v_i_1778_);
v___x_1782_ = l_Subarray_drop___redArg(v_right_1772_, v_i_1778_);
v___x_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1781_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
v___x_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1784_, 0, v_pref_1773_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
return v___x_1784_;
}
else
{
lean_object* v___x_1785_; lean_object* v___x_1786_; uint8_t v___x_1787_; 
v___x_1785_ = l_Subarray_get___redArg(v_left_1771_, v_i_1778_);
v___x_1786_ = l_Subarray_get___redArg(v_right_1772_, v_i_1778_);
v___x_1787_ = lean_string_dec_eq(v___x_1785_, v___x_1786_);
lean_dec(v___x_1786_);
if (v___x_1787_ == 0)
{
lean_object* v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
lean_dec(v___x_1785_);
v___x_1788_ = l_Subarray_drop___redArg(v_left_1771_, v_i_1778_);
v___x_1789_ = l_Subarray_drop___redArg(v_right_1772_, v_i_1778_);
v___x_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1790_, 0, v___x_1788_);
lean_ctor_set(v___x_1790_, 1, v___x_1789_);
v___x_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1791_, 0, v_pref_1773_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
return v___x_1791_;
}
else
{
lean_object* v___x_1792_; 
v___x_1792_ = lean_array_push(v_pref_1773_, v___x_1785_);
v_pref_1773_ = v___x_1792_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4(lean_object* v_left_1798_, lean_object* v_right_1799_){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_1801_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4_spec__6(v_left_1798_, v_right_1799_, v___x_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(lean_object* v_a_1802_, lean_object* v_x_1803_){
_start:
{
if (lean_obj_tag(v_x_1803_) == 0)
{
lean_object* v___x_1804_; 
v___x_1804_ = lean_box(0);
return v___x_1804_;
}
else
{
lean_object* v_key_1805_; lean_object* v_value_1806_; lean_object* v_tail_1807_; uint8_t v___x_1808_; 
v_key_1805_ = lean_ctor_get(v_x_1803_, 0);
v_value_1806_ = lean_ctor_get(v_x_1803_, 1);
v_tail_1807_ = lean_ctor_get(v_x_1803_, 2);
v___x_1808_ = lean_string_dec_eq(v_key_1805_, v_a_1802_);
if (v___x_1808_ == 0)
{
v_x_1803_ = v_tail_1807_;
goto _start;
}
else
{
lean_object* v___x_1810_; 
lean_inc(v_value_1806_);
v___x_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1810_, 0, v_value_1806_);
return v___x_1810_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg___boxed(lean_object* v_a_1811_, lean_object* v_x_1812_){
_start:
{
lean_object* v_res_1813_; 
v_res_1813_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(v_a_1811_, v_x_1812_);
lean_dec(v_x_1812_);
lean_dec_ref(v_a_1811_);
return v_res_1813_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(lean_object* v_m_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v_buckets_1816_; lean_object* v___x_1817_; uint64_t v___x_1818_; uint64_t v___x_1819_; uint64_t v___x_1820_; uint64_t v_fold_1821_; uint64_t v___x_1822_; uint64_t v___x_1823_; uint64_t v___x_1824_; size_t v___x_1825_; size_t v___x_1826_; size_t v___x_1827_; size_t v___x_1828_; size_t v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v_buckets_1816_ = lean_ctor_get(v_m_1814_, 1);
v___x_1817_ = lean_array_get_size(v_buckets_1816_);
v___x_1818_ = lean_string_hash(v_a_1815_);
v___x_1819_ = 32ULL;
v___x_1820_ = lean_uint64_shift_right(v___x_1818_, v___x_1819_);
v_fold_1821_ = lean_uint64_xor(v___x_1818_, v___x_1820_);
v___x_1822_ = 16ULL;
v___x_1823_ = lean_uint64_shift_right(v_fold_1821_, v___x_1822_);
v___x_1824_ = lean_uint64_xor(v_fold_1821_, v___x_1823_);
v___x_1825_ = lean_uint64_to_usize(v___x_1824_);
v___x_1826_ = lean_usize_of_nat(v___x_1817_);
v___x_1827_ = ((size_t)1ULL);
v___x_1828_ = lean_usize_sub(v___x_1826_, v___x_1827_);
v___x_1829_ = lean_usize_land(v___x_1825_, v___x_1828_);
v___x_1830_ = lean_array_uget_borrowed(v_buckets_1816_, v___x_1829_);
v___x_1831_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(v_a_1815_, v___x_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg___boxed(lean_object* v_m_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_m_1832_, v_a_1833_);
lean_dec_ref(v_a_1833_);
lean_dec_ref(v_m_1832_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29___redArg(lean_object* v_x_1835_, lean_object* v_x_1836_){
_start:
{
if (lean_obj_tag(v_x_1836_) == 0)
{
return v_x_1835_;
}
else
{
lean_object* v_key_1837_; lean_object* v_value_1838_; lean_object* v_tail_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1862_; 
v_key_1837_ = lean_ctor_get(v_x_1836_, 0);
v_value_1838_ = lean_ctor_get(v_x_1836_, 1);
v_tail_1839_ = lean_ctor_get(v_x_1836_, 2);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_x_1836_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1841_ = v_x_1836_;
v_isShared_1842_ = v_isSharedCheck_1862_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_tail_1839_);
lean_inc(v_value_1838_);
lean_inc(v_key_1837_);
lean_dec(v_x_1836_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1862_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1843_; uint64_t v___x_1844_; uint64_t v___x_1845_; uint64_t v___x_1846_; uint64_t v_fold_1847_; uint64_t v___x_1848_; uint64_t v___x_1849_; uint64_t v___x_1850_; size_t v___x_1851_; size_t v___x_1852_; size_t v___x_1853_; size_t v___x_1854_; size_t v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1858_; 
v___x_1843_ = lean_array_get_size(v_x_1835_);
v___x_1844_ = lean_string_hash(v_key_1837_);
v___x_1845_ = 32ULL;
v___x_1846_ = lean_uint64_shift_right(v___x_1844_, v___x_1845_);
v_fold_1847_ = lean_uint64_xor(v___x_1844_, v___x_1846_);
v___x_1848_ = 16ULL;
v___x_1849_ = lean_uint64_shift_right(v_fold_1847_, v___x_1848_);
v___x_1850_ = lean_uint64_xor(v_fold_1847_, v___x_1849_);
v___x_1851_ = lean_uint64_to_usize(v___x_1850_);
v___x_1852_ = lean_usize_of_nat(v___x_1843_);
v___x_1853_ = ((size_t)1ULL);
v___x_1854_ = lean_usize_sub(v___x_1852_, v___x_1853_);
v___x_1855_ = lean_usize_land(v___x_1851_, v___x_1854_);
v___x_1856_ = lean_array_uget_borrowed(v_x_1835_, v___x_1855_);
lean_inc(v___x_1856_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 2, v___x_1856_);
v___x_1858_ = v___x_1841_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_key_1837_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_value_1838_);
lean_ctor_set(v_reuseFailAlloc_1861_, 2, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1859_; 
v___x_1859_ = lean_array_uset(v_x_1835_, v___x_1855_, v___x_1858_);
v_x_1835_ = v___x_1859_;
v_x_1836_ = v_tail_1839_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28___redArg(lean_object* v_i_1863_, lean_object* v_source_1864_, lean_object* v_target_1865_){
_start:
{
lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1866_ = lean_array_get_size(v_source_1864_);
v___x_1867_ = lean_nat_dec_lt(v_i_1863_, v___x_1866_);
if (v___x_1867_ == 0)
{
lean_dec_ref(v_source_1864_);
lean_dec(v_i_1863_);
return v_target_1865_;
}
else
{
lean_object* v_es_1868_; lean_object* v___x_1869_; lean_object* v_source_1870_; lean_object* v_target_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v_es_1868_ = lean_array_fget(v_source_1864_, v_i_1863_);
v___x_1869_ = lean_box(0);
v_source_1870_ = lean_array_fset(v_source_1864_, v_i_1863_, v___x_1869_);
v_target_1871_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29___redArg(v_target_1865_, v_es_1868_);
v___x_1872_ = lean_unsigned_to_nat(1u);
v___x_1873_ = lean_nat_add(v_i_1863_, v___x_1872_);
lean_dec(v_i_1863_);
v_i_1863_ = v___x_1873_;
v_source_1864_ = v_source_1870_;
v_target_1865_ = v_target_1871_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23___redArg(lean_object* v_data_1875_){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v_nbuckets_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1876_ = lean_array_get_size(v_data_1875_);
v___x_1877_ = lean_unsigned_to_nat(2u);
v_nbuckets_1878_ = lean_nat_mul(v___x_1876_, v___x_1877_);
v___x_1879_ = lean_unsigned_to_nat(0u);
v___x_1880_ = lean_box(0);
v___x_1881_ = lean_mk_array(v_nbuckets_1878_, v___x_1880_);
v___x_1882_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28___redArg(v___x_1879_, v_data_1875_, v___x_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(lean_object* v_a_1883_, lean_object* v_b_1884_, lean_object* v_x_1885_){
_start:
{
if (lean_obj_tag(v_x_1885_) == 0)
{
lean_dec(v_b_1884_);
lean_dec_ref(v_a_1883_);
return v_x_1885_;
}
else
{
lean_object* v_key_1886_; lean_object* v_value_1887_; lean_object* v_tail_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1900_; 
v_key_1886_ = lean_ctor_get(v_x_1885_, 0);
v_value_1887_ = lean_ctor_get(v_x_1885_, 1);
v_tail_1888_ = lean_ctor_get(v_x_1885_, 2);
v_isSharedCheck_1900_ = !lean_is_exclusive(v_x_1885_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1890_ = v_x_1885_;
v_isShared_1891_ = v_isSharedCheck_1900_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_tail_1888_);
lean_inc(v_value_1887_);
lean_inc(v_key_1886_);
lean_dec(v_x_1885_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1900_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
uint8_t v___x_1892_; 
v___x_1892_ = lean_string_dec_eq(v_key_1886_, v_a_1883_);
if (v___x_1892_ == 0)
{
lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1893_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(v_a_1883_, v_b_1884_, v_tail_1888_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 2, v___x_1893_);
v___x_1895_ = v___x_1890_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_key_1886_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v_value_1887_);
lean_ctor_set(v_reuseFailAlloc_1896_, 2, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
else
{
lean_object* v___x_1898_; 
lean_dec(v_value_1887_);
lean_dec(v_key_1886_);
if (v_isShared_1891_ == 0)
{
lean_ctor_set(v___x_1890_, 1, v_b_1884_);
lean_ctor_set(v___x_1890_, 0, v_a_1883_);
v___x_1898_ = v___x_1890_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1883_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_b_1884_);
lean_ctor_set(v_reuseFailAlloc_1899_, 2, v_tail_1888_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(lean_object* v_a_1901_, lean_object* v_x_1902_){
_start:
{
if (lean_obj_tag(v_x_1902_) == 0)
{
uint8_t v___x_1903_; 
v___x_1903_ = 0;
return v___x_1903_;
}
else
{
lean_object* v_key_1904_; lean_object* v_tail_1905_; uint8_t v___x_1906_; 
v_key_1904_ = lean_ctor_get(v_x_1902_, 0);
v_tail_1905_ = lean_ctor_get(v_x_1902_, 2);
v___x_1906_ = lean_string_dec_eq(v_key_1904_, v_a_1901_);
if (v___x_1906_ == 0)
{
v_x_1902_ = v_tail_1905_;
goto _start;
}
else
{
return v___x_1906_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg___boxed(lean_object* v_a_1908_, lean_object* v_x_1909_){
_start:
{
uint8_t v_res_1910_; lean_object* v_r_1911_; 
v_res_1910_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(v_a_1908_, v_x_1909_);
lean_dec(v_x_1909_);
lean_dec_ref(v_a_1908_);
v_r_1911_ = lean_box(v_res_1910_);
return v_r_1911_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(lean_object* v_m_1912_, lean_object* v_a_1913_, lean_object* v_b_1914_){
_start:
{
lean_object* v_size_1915_; lean_object* v_buckets_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1959_; 
v_size_1915_ = lean_ctor_get(v_m_1912_, 0);
v_buckets_1916_ = lean_ctor_get(v_m_1912_, 1);
v_isSharedCheck_1959_ = !lean_is_exclusive(v_m_1912_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1918_ = v_m_1912_;
v_isShared_1919_ = v_isSharedCheck_1959_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_buckets_1916_);
lean_inc(v_size_1915_);
lean_dec(v_m_1912_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1959_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
lean_object* v___x_1920_; uint64_t v___x_1921_; uint64_t v___x_1922_; uint64_t v___x_1923_; uint64_t v_fold_1924_; uint64_t v___x_1925_; uint64_t v___x_1926_; uint64_t v___x_1927_; size_t v___x_1928_; size_t v___x_1929_; size_t v___x_1930_; size_t v___x_1931_; size_t v___x_1932_; lean_object* v_bkt_1933_; uint8_t v___x_1934_; 
v___x_1920_ = lean_array_get_size(v_buckets_1916_);
v___x_1921_ = lean_string_hash(v_a_1913_);
v___x_1922_ = 32ULL;
v___x_1923_ = lean_uint64_shift_right(v___x_1921_, v___x_1922_);
v_fold_1924_ = lean_uint64_xor(v___x_1921_, v___x_1923_);
v___x_1925_ = 16ULL;
v___x_1926_ = lean_uint64_shift_right(v_fold_1924_, v___x_1925_);
v___x_1927_ = lean_uint64_xor(v_fold_1924_, v___x_1926_);
v___x_1928_ = lean_uint64_to_usize(v___x_1927_);
v___x_1929_ = lean_usize_of_nat(v___x_1920_);
v___x_1930_ = ((size_t)1ULL);
v___x_1931_ = lean_usize_sub(v___x_1929_, v___x_1930_);
v___x_1932_ = lean_usize_land(v___x_1928_, v___x_1931_);
v_bkt_1933_ = lean_array_uget_borrowed(v_buckets_1916_, v___x_1932_);
v___x_1934_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(v_a_1913_, v_bkt_1933_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; lean_object* v_size_x27_1936_; lean_object* v___x_1937_; lean_object* v_buckets_x27_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; uint8_t v___x_1944_; 
v___x_1935_ = lean_unsigned_to_nat(1u);
v_size_x27_1936_ = lean_nat_add(v_size_1915_, v___x_1935_);
lean_dec(v_size_1915_);
lean_inc(v_bkt_1933_);
v___x_1937_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1937_, 0, v_a_1913_);
lean_ctor_set(v___x_1937_, 1, v_b_1914_);
lean_ctor_set(v___x_1937_, 2, v_bkt_1933_);
v_buckets_x27_1938_ = lean_array_uset(v_buckets_1916_, v___x_1932_, v___x_1937_);
v___x_1939_ = lean_unsigned_to_nat(4u);
v___x_1940_ = lean_nat_mul(v_size_x27_1936_, v___x_1939_);
v___x_1941_ = lean_unsigned_to_nat(3u);
v___x_1942_ = lean_nat_div(v___x_1940_, v___x_1941_);
lean_dec(v___x_1940_);
v___x_1943_ = lean_array_get_size(v_buckets_x27_1938_);
v___x_1944_ = lean_nat_dec_le(v___x_1942_, v___x_1943_);
lean_dec(v___x_1942_);
if (v___x_1944_ == 0)
{
lean_object* v_val_1945_; lean_object* v___x_1947_; 
v_val_1945_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23___redArg(v_buckets_x27_1938_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 1, v_val_1945_);
lean_ctor_set(v___x_1918_, 0, v_size_x27_1936_);
v___x_1947_ = v___x_1918_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_size_x27_1936_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_val_1945_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
else
{
lean_object* v___x_1950_; 
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 1, v_buckets_x27_1938_);
lean_ctor_set(v___x_1918_, 0, v_size_x27_1936_);
v___x_1950_ = v___x_1918_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_size_x27_1936_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_buckets_x27_1938_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
else
{
lean_object* v___x_1952_; lean_object* v_buckets_x27_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1957_; 
lean_inc(v_bkt_1933_);
v___x_1952_ = lean_box(0);
v_buckets_x27_1953_ = lean_array_uset(v_buckets_1916_, v___x_1932_, v___x_1952_);
v___x_1954_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(v_a_1913_, v_b_1914_, v_bkt_1933_);
v___x_1955_ = lean_array_uset(v_buckets_x27_1953_, v___x_1932_, v___x_1954_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 1, v___x_1955_);
v___x_1957_ = v___x_1918_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_size_1915_);
lean_ctor_set(v_reuseFailAlloc_1958_, 1, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___redArg(lean_object* v_histogram_1960_, lean_object* v_index_1961_, lean_object* v_val_1962_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_histogram_1960_, v_val_1962_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1964_ = lean_unsigned_to_nat(0u);
v___x_1965_ = lean_box(0);
v___x_1966_ = lean_unsigned_to_nat(1u);
v___x_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1967_, 0, v_index_1961_);
v___x_1968_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1964_);
lean_ctor_set(v___x_1968_, 1, v___x_1965_);
lean_ctor_set(v___x_1968_, 2, v___x_1966_);
lean_ctor_set(v___x_1968_, 3, v___x_1967_);
v___x_1969_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_1960_, v_val_1962_, v___x_1968_);
return v___x_1969_;
}
else
{
lean_object* v_val_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1991_; 
v_val_1970_ = lean_ctor_get(v___x_1963_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1963_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1972_ = v___x_1963_;
v_isShared_1973_ = v_isSharedCheck_1991_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_val_1970_);
lean_dec(v___x_1963_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1991_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_leftCount_1974_; lean_object* v_leftIndex_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1988_; 
v_leftCount_1974_ = lean_ctor_get(v_val_1970_, 0);
v_leftIndex_1975_ = lean_ctor_get(v_val_1970_, 1);
v_isSharedCheck_1988_ = !lean_is_exclusive(v_val_1970_);
if (v_isSharedCheck_1988_ == 0)
{
lean_object* v_unused_1989_; lean_object* v_unused_1990_; 
v_unused_1989_ = lean_ctor_get(v_val_1970_, 3);
lean_dec(v_unused_1989_);
v_unused_1990_ = lean_ctor_get(v_val_1970_, 2);
lean_dec(v_unused_1990_);
v___x_1977_ = v_val_1970_;
v_isShared_1978_ = v_isSharedCheck_1988_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_leftIndex_1975_);
lean_inc(v_leftCount_1974_);
lean_dec(v_val_1970_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1988_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1982_; 
v___x_1979_ = lean_unsigned_to_nat(1u);
v___x_1980_ = lean_nat_add(v_leftCount_1974_, v___x_1979_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v_index_1961_);
v___x_1982_ = v___x_1972_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_index_1961_);
v___x_1982_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1984_; 
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 3, v___x_1982_);
lean_ctor_set(v___x_1977_, 2, v___x_1980_);
v___x_1984_ = v___x_1977_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_leftCount_1974_);
lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_leftIndex_1975_);
lean_ctor_set(v_reuseFailAlloc_1986_, 2, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_1986_, 3, v___x_1982_);
v___x_1984_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1985_; 
v___x_1985_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_1960_, v_val_1962_, v___x_1984_);
return v___x_1985_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(lean_object* v_upperBound_1992_, lean_object* v___x_1993_, lean_object* v_fst_1994_, lean_object* v___x_1995_, lean_object* v_a_1996_, lean_object* v_b_1997_){
_start:
{
uint8_t v___x_1998_; 
v___x_1998_ = lean_nat_dec_lt(v_a_1996_, v_upperBound_1992_);
if (v___x_1998_ == 0)
{
lean_dec(v_a_1996_);
return v_b_1997_;
}
else
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_1999_ = l_Subarray_get___redArg(v_fst_1994_, v_a_1996_);
lean_inc(v_a_1996_);
v___x_2000_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___redArg(v_b_1997_, v_a_1996_, v___x_1999_);
v___x_2001_ = lean_unsigned_to_nat(1u);
v___x_2002_ = lean_nat_add(v_a_1996_, v___x_2001_);
lean_dec(v_a_1996_);
v_a_1996_ = v___x_2002_;
v_b_1997_ = v___x_2000_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg___boxed(lean_object* v_upperBound_2004_, lean_object* v___x_2005_, lean_object* v_fst_2006_, lean_object* v___x_2007_, lean_object* v_a_2008_, lean_object* v_b_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(v_upperBound_2004_, v___x_2005_, v_fst_2006_, v___x_2007_, v_a_2008_, v_b_2009_);
lean_dec(v___x_2007_);
lean_dec_ref(v_fst_2006_);
lean_dec(v___x_2005_);
lean_dec(v_upperBound_2004_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(lean_object* v_as_x27_2011_, lean_object* v_b_2012_){
_start:
{
if (lean_obj_tag(v_as_x27_2011_) == 0)
{
return v_b_2012_;
}
else
{
lean_object* v_head_2013_; lean_object* v_snd_2014_; lean_object* v_leftIndex_2015_; 
v_head_2013_ = lean_ctor_get(v_as_x27_2011_, 0);
v_snd_2014_ = lean_ctor_get(v_head_2013_, 1);
v_leftIndex_2015_ = lean_ctor_get(v_snd_2014_, 1);
if (lean_obj_tag(v_leftIndex_2015_) == 1)
{
lean_object* v_rightIndex_2016_; 
v_rightIndex_2016_ = lean_ctor_get(v_snd_2014_, 3);
if (lean_obj_tag(v_rightIndex_2016_) == 1)
{
if (lean_obj_tag(v_b_2012_) == 0)
{
lean_object* v_tail_2017_; lean_object* v_fst_2018_; lean_object* v_leftCount_2019_; lean_object* v_rightCount_2020_; lean_object* v_val_2021_; lean_object* v_val_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v_tail_2017_ = lean_ctor_get(v_as_x27_2011_, 1);
v_fst_2018_ = lean_ctor_get(v_head_2013_, 0);
v_leftCount_2019_ = lean_ctor_get(v_snd_2014_, 0);
v_rightCount_2020_ = lean_ctor_get(v_snd_2014_, 2);
v_val_2021_ = lean_ctor_get(v_leftIndex_2015_, 0);
v_val_2022_ = lean_ctor_get(v_rightIndex_2016_, 0);
v___x_2023_ = lean_nat_add(v_leftCount_2019_, v_rightCount_2020_);
lean_inc(v_val_2022_);
lean_inc(v_val_2021_);
v___x_2024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2024_, 0, v_val_2021_);
lean_ctor_set(v___x_2024_, 1, v_val_2022_);
lean_inc(v_fst_2018_);
v___x_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2025_, 0, v_fst_2018_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
v___x_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2023_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
v___x_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2026_);
v_as_x27_2011_ = v_tail_2017_;
v_b_2012_ = v___x_2027_;
goto _start;
}
else
{
lean_object* v_val_2029_; lean_object* v_tail_2030_; lean_object* v_fst_2031_; lean_object* v_leftCount_2032_; lean_object* v_rightCount_2033_; lean_object* v_val_2034_; lean_object* v_val_2035_; lean_object* v_fst_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2057_; 
v_val_2029_ = lean_ctor_get(v_b_2012_, 0);
lean_inc(v_val_2029_);
v_tail_2030_ = lean_ctor_get(v_as_x27_2011_, 1);
v_fst_2031_ = lean_ctor_get(v_head_2013_, 0);
v_leftCount_2032_ = lean_ctor_get(v_snd_2014_, 0);
v_rightCount_2033_ = lean_ctor_get(v_snd_2014_, 2);
v_val_2034_ = lean_ctor_get(v_leftIndex_2015_, 0);
v_val_2035_ = lean_ctor_get(v_rightIndex_2016_, 0);
v_fst_2036_ = lean_ctor_get(v_val_2029_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_val_2029_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; 
v_unused_2058_ = lean_ctor_get(v_val_2029_, 1);
lean_dec(v_unused_2058_);
v___x_2038_ = v_val_2029_;
v_isShared_2039_ = v_isSharedCheck_2057_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_fst_2036_);
lean_dec(v_val_2029_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2057_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2040_; uint8_t v___x_2041_; 
v___x_2040_ = lean_nat_add(v_leftCount_2032_, v_rightCount_2033_);
v___x_2041_ = lean_nat_dec_lt(v___x_2040_, v_fst_2036_);
lean_dec(v_fst_2036_);
if (v___x_2041_ == 0)
{
lean_dec(v___x_2040_);
lean_del_object(v___x_2038_);
v_as_x27_2011_ = v_tail_2030_;
goto _start;
}
else
{
lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2055_; 
v_isSharedCheck_2055_ = !lean_is_exclusive(v_b_2012_);
if (v_isSharedCheck_2055_ == 0)
{
lean_object* v_unused_2056_; 
v_unused_2056_ = lean_ctor_get(v_b_2012_, 0);
lean_dec(v_unused_2056_);
v___x_2044_ = v_b_2012_;
v_isShared_2045_ = v_isSharedCheck_2055_;
goto v_resetjp_2043_;
}
else
{
lean_dec(v_b_2012_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2055_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
lean_inc(v_val_2035_);
lean_inc(v_val_2034_);
if (v_isShared_2039_ == 0)
{
lean_ctor_set(v___x_2038_, 1, v_val_2035_);
lean_ctor_set(v___x_2038_, 0, v_val_2034_);
v___x_2047_ = v___x_2038_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_val_2034_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_val_2035_);
v___x_2047_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2051_; 
lean_inc(v_fst_2031_);
v___x_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2048_, 0, v_fst_2031_);
lean_ctor_set(v___x_2048_, 1, v___x_2047_);
v___x_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2040_);
lean_ctor_set(v___x_2049_, 1, v___x_2048_);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v___x_2049_);
v___x_2051_ = v___x_2044_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v___x_2049_);
v___x_2051_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
v_as_x27_2011_ = v_tail_2030_;
v_b_2012_ = v___x_2051_;
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
lean_object* v_tail_2059_; 
v_tail_2059_ = lean_ctor_get(v_as_x27_2011_, 1);
v_as_x27_2011_ = v_tail_2059_;
goto _start;
}
}
else
{
lean_object* v_tail_2061_; 
v_tail_2061_ = lean_ctor_get(v_as_x27_2011_, 1);
v_as_x27_2011_ = v_tail_2061_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_as_x27_2063_, lean_object* v_b_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(v_as_x27_2063_, v_b_2064_);
lean_dec(v_as_x27_2063_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(lean_object* v_a_2066_, lean_object* v_b_2067_){
_start:
{
lean_object* v_array_2068_; lean_object* v_start_2069_; lean_object* v_stop_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2083_; 
v_array_2068_ = lean_ctor_get(v_a_2066_, 0);
v_start_2069_ = lean_ctor_get(v_a_2066_, 1);
v_stop_2070_ = lean_ctor_get(v_a_2066_, 2);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_a_2066_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2072_ = v_a_2066_;
v_isShared_2073_ = v_isSharedCheck_2083_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_stop_2070_);
lean_inc(v_start_2069_);
lean_inc(v_array_2068_);
lean_dec(v_a_2066_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2083_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
uint8_t v___x_2074_; 
v___x_2074_ = lean_nat_dec_lt(v_start_2069_, v_stop_2070_);
if (v___x_2074_ == 0)
{
lean_del_object(v___x_2072_);
lean_dec(v_stop_2070_);
lean_dec(v_start_2069_);
lean_dec_ref(v_array_2068_);
return v_b_2067_;
}
else
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2078_; 
v___x_2075_ = lean_unsigned_to_nat(1u);
v___x_2076_ = lean_nat_add(v_start_2069_, v___x_2075_);
lean_inc_ref(v_array_2068_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 1, v___x_2076_);
v___x_2078_ = v___x_2072_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_array_2068_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v___x_2076_);
lean_ctor_set(v_reuseFailAlloc_2082_, 2, v_stop_2070_);
v___x_2078_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = lean_array_fget(v_array_2068_, v_start_2069_);
lean_dec(v_start_2069_);
lean_dec_ref(v_array_2068_);
v___x_2080_ = lean_array_push(v_b_2067_, v___x_2079_);
v_a_2066_ = v___x_2078_;
v_b_2067_ = v___x_2080_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8(lean_object* v_left_2084_, lean_object* v_right_2085_, lean_object* v_i_2086_){
_start:
{
lean_object* v_start_2087_; lean_object* v_stop_2088_; lean_object* v_start_2089_; lean_object* v_stop_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; lean_object* v___x_2093_; uint8_t v___y_2095_; 
v_start_2087_ = lean_ctor_get(v_left_2084_, 1);
v_stop_2088_ = lean_ctor_get(v_left_2084_, 2);
v_start_2089_ = lean_ctor_get(v_right_2085_, 1);
v_stop_2090_ = lean_ctor_get(v_right_2085_, 2);
v___x_2091_ = lean_nat_sub(v_stop_2088_, v_start_2087_);
v___x_2092_ = lean_nat_dec_lt(v_i_2086_, v___x_2091_);
v___x_2093_ = lean_nat_sub(v_stop_2090_, v_start_2089_);
if (v___x_2092_ == 0)
{
v___y_2095_ = v___x_2092_;
goto v___jp_2094_;
}
else
{
uint8_t v___x_2122_; 
v___x_2122_ = lean_nat_dec_lt(v_i_2086_, v___x_2093_);
v___y_2095_ = v___x_2122_;
goto v___jp_2094_;
}
v___jp_2094_:
{
if (v___y_2095_ == 0)
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2096_ = lean_nat_sub(v___x_2091_, v_i_2086_);
lean_dec(v___x_2091_);
lean_inc_ref(v_left_2084_);
v___x_2097_ = l_Subarray_take___redArg(v_left_2084_, v___x_2096_);
v___x_2098_ = lean_nat_sub(v___x_2093_, v_i_2086_);
lean_dec(v_i_2086_);
lean_dec(v___x_2093_);
v___x_2099_ = l_Subarray_take___redArg(v_right_2085_, v___x_2098_);
lean_dec(v___x_2098_);
v___x_2100_ = l_Subarray_drop___redArg(v_left_2084_, v___x_2096_);
lean_dec(v___x_2096_);
v___x_2101_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2102_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(v___x_2100_, v___x_2101_);
v___x_2103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2099_);
lean_ctor_set(v___x_2103_, 1, v___x_2102_);
v___x_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2097_);
lean_ctor_set(v___x_2104_, 1, v___x_2103_);
return v___x_2104_;
}
else
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; uint8_t v___x_2112_; 
v___x_2105_ = lean_nat_sub(v___x_2091_, v_i_2086_);
lean_dec(v___x_2091_);
v___x_2106_ = lean_unsigned_to_nat(1u);
v___x_2107_ = lean_nat_sub(v___x_2105_, v___x_2106_);
v___x_2108_ = l_Subarray_get___redArg(v_left_2084_, v___x_2107_);
lean_dec(v___x_2107_);
v___x_2109_ = lean_nat_sub(v___x_2093_, v_i_2086_);
lean_dec(v___x_2093_);
v___x_2110_ = lean_nat_sub(v___x_2109_, v___x_2106_);
v___x_2111_ = l_Subarray_get___redArg(v_right_2085_, v___x_2110_);
lean_dec(v___x_2110_);
v___x_2112_ = lean_string_dec_eq(v___x_2108_, v___x_2111_);
lean_dec(v___x_2111_);
lean_dec(v___x_2108_);
if (v___x_2112_ == 0)
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
lean_dec(v_i_2086_);
lean_inc_ref(v_left_2084_);
v___x_2113_ = l_Subarray_take___redArg(v_left_2084_, v___x_2105_);
v___x_2114_ = l_Subarray_take___redArg(v_right_2085_, v___x_2109_);
lean_dec(v___x_2109_);
v___x_2115_ = l_Subarray_drop___redArg(v_left_2084_, v___x_2105_);
lean_dec(v___x_2105_);
v___x_2116_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2117_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(v___x_2115_, v___x_2116_);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2114_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2113_);
lean_ctor_set(v___x_2119_, 1, v___x_2118_);
return v___x_2119_;
}
else
{
lean_object* v___x_2120_; 
lean_dec(v___x_2109_);
lean_dec(v___x_2105_);
v___x_2120_ = lean_nat_add(v_i_2086_, v___x_2106_);
lean_dec(v_i_2086_);
v_i_2086_ = v___x_2120_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5(lean_object* v_left_2123_, lean_object* v_right_2124_){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = lean_unsigned_to_nat(0u);
v___x_2126_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8(v_left_2123_, v_right_2124_, v___x_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___redArg(lean_object* v_histogram_2127_, lean_object* v_index_2128_, lean_object* v_val_2129_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_histogram_2127_, v_val_2129_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2131_ = lean_unsigned_to_nat(1u);
v___x_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2132_, 0, v_index_2128_);
v___x_2133_ = lean_unsigned_to_nat(0u);
v___x_2134_ = lean_box(0);
v___x_2135_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2131_);
lean_ctor_set(v___x_2135_, 1, v___x_2132_);
lean_ctor_set(v___x_2135_, 2, v___x_2133_);
lean_ctor_set(v___x_2135_, 3, v___x_2134_);
v___x_2136_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_2127_, v_val_2129_, v___x_2135_);
return v___x_2136_;
}
else
{
lean_object* v_val_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2158_; 
v_val_2137_ = lean_ctor_get(v___x_2130_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2130_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2139_ = v___x_2130_;
v_isShared_2140_ = v_isSharedCheck_2158_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_val_2137_);
lean_dec(v___x_2130_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2158_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v_leftCount_2141_; lean_object* v_rightCount_2142_; lean_object* v_rightIndex_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2156_; 
v_leftCount_2141_ = lean_ctor_get(v_val_2137_, 0);
v_rightCount_2142_ = lean_ctor_get(v_val_2137_, 2);
v_rightIndex_2143_ = lean_ctor_get(v_val_2137_, 3);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_val_2137_);
if (v_isSharedCheck_2156_ == 0)
{
lean_object* v_unused_2157_; 
v_unused_2157_ = lean_ctor_get(v_val_2137_, 1);
lean_dec(v_unused_2157_);
v___x_2145_ = v_val_2137_;
v_isShared_2146_ = v_isSharedCheck_2156_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_rightIndex_2143_);
lean_inc(v_rightCount_2142_);
lean_inc(v_leftCount_2141_);
lean_dec(v_val_2137_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2156_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2150_; 
v___x_2147_ = lean_unsigned_to_nat(1u);
v___x_2148_ = lean_nat_add(v_leftCount_2141_, v___x_2147_);
lean_dec(v_leftCount_2141_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v_index_2128_);
v___x_2150_ = v___x_2139_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_index_2128_);
v___x_2150_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2152_; 
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 1, v___x_2150_);
lean_ctor_set(v___x_2145_, 0, v___x_2148_);
v___x_2152_ = v___x_2145_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2154_, 1, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2154_, 2, v_rightCount_2142_);
lean_ctor_set(v_reuseFailAlloc_2154_, 3, v_rightIndex_2143_);
v___x_2152_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_2127_, v_val_2129_, v___x_2152_);
return v___x_2153_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(lean_object* v_upperBound_2159_, lean_object* v_fst_2160_, lean_object* v___x_2161_, lean_object* v_fst_2162_, lean_object* v_a_2163_, lean_object* v_b_2164_){
_start:
{
uint8_t v___x_2165_; 
v___x_2165_ = lean_nat_dec_lt(v_a_2163_, v_upperBound_2159_);
if (v___x_2165_ == 0)
{
lean_dec(v_a_2163_);
return v_b_2164_;
}
else
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2166_ = l_Subarray_get___redArg(v_fst_2162_, v_a_2163_);
lean_inc(v_a_2163_);
v___x_2167_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___redArg(v_b_2164_, v_a_2163_, v___x_2166_);
v___x_2168_ = lean_unsigned_to_nat(1u);
v___x_2169_ = lean_nat_add(v_a_2163_, v___x_2168_);
lean_dec(v_a_2163_);
v_a_2163_ = v___x_2169_;
v_b_2164_ = v___x_2167_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg___boxed(lean_object* v_upperBound_2171_, lean_object* v_fst_2172_, lean_object* v___x_2173_, lean_object* v_fst_2174_, lean_object* v_a_2175_, lean_object* v_b_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(v_upperBound_2171_, v_fst_2172_, v___x_2173_, v_fst_2174_, v_a_2175_, v_b_2176_);
lean_dec_ref(v_fst_2174_);
lean_dec(v___x_2173_);
lean_dec_ref(v_fst_2172_);
lean_dec(v_upperBound_2171_);
return v_res_2177_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2178_ = lean_box(0);
v___x_2179_ = lean_unsigned_to_nat(16u);
v___x_2180_ = lean_mk_array(v___x_2179_, v___x_2178_);
return v___x_2180_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v_hist_2183_; 
v___x_2181_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0);
v___x_2182_ = lean_unsigned_to_nat(0u);
v_hist_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_2183_, 0, v___x_2182_);
lean_ctor_set(v_hist_2183_, 1, v___x_2181_);
return v_hist_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(lean_object* v_left_2184_, lean_object* v_right_2185_){
_start:
{
lean_object* v___x_2186_; lean_object* v_snd_2187_; lean_object* v_fst_2188_; lean_object* v_fst_2189_; lean_object* v_snd_2190_; lean_object* v___x_2191_; lean_object* v_snd_2192_; lean_object* v_fst_2193_; lean_object* v_fst_2194_; lean_object* v_snd_2195_; lean_object* v_start_2196_; lean_object* v_stop_2197_; lean_object* v___x_2198_; lean_object* v_hist_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v_start_2202_; lean_object* v_stop_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v_buckets_2206_; lean_object* v___x_2207_; lean_object* v___y_2209_; lean_object* v___x_2235_; lean_object* v___x_2236_; uint8_t v___x_2237_; 
v___x_2186_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4(v_left_2184_, v_right_2185_);
v_snd_2187_ = lean_ctor_get(v___x_2186_, 1);
lean_inc(v_snd_2187_);
v_fst_2188_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_fst_2188_);
lean_dec_ref(v___x_2186_);
v_fst_2189_ = lean_ctor_get(v_snd_2187_, 0);
lean_inc(v_fst_2189_);
v_snd_2190_ = lean_ctor_get(v_snd_2187_, 1);
lean_inc(v_snd_2190_);
lean_dec(v_snd_2187_);
v___x_2191_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5(v_fst_2189_, v_snd_2190_);
v_snd_2192_ = lean_ctor_get(v___x_2191_, 1);
lean_inc(v_snd_2192_);
v_fst_2193_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_fst_2193_);
lean_dec_ref(v___x_2191_);
v_fst_2194_ = lean_ctor_get(v_snd_2192_, 0);
lean_inc(v_fst_2194_);
v_snd_2195_ = lean_ctor_get(v_snd_2192_, 1);
lean_inc(v_snd_2195_);
lean_dec(v_snd_2192_);
v_start_2196_ = lean_ctor_get(v_fst_2193_, 1);
v_stop_2197_ = lean_ctor_get(v_fst_2193_, 2);
v___x_2198_ = lean_unsigned_to_nat(0u);
v_hist_2199_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1);
v___x_2200_ = lean_nat_sub(v_stop_2197_, v_start_2196_);
v___x_2201_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(v___x_2200_, v_fst_2194_, v___x_2200_, v_fst_2193_, v___x_2198_, v_hist_2199_);
v_start_2202_ = lean_ctor_get(v_fst_2194_, 1);
v_stop_2203_ = lean_ctor_get(v_fst_2194_, 2);
v___x_2204_ = lean_nat_sub(v_stop_2203_, v_start_2202_);
v___x_2205_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(v___x_2204_, v___x_2204_, v_fst_2194_, v___x_2200_, v___x_2198_, v___x_2201_);
lean_dec(v___x_2200_);
lean_dec(v___x_2204_);
v_buckets_2206_ = lean_ctor_get(v___x_2205_, 1);
lean_inc_ref(v_buckets_2206_);
lean_dec_ref(v___x_2205_);
v___x_2207_ = lean_box(0);
v___x_2235_ = lean_box(0);
v___x_2236_ = lean_array_get_size(v_buckets_2206_);
v___x_2237_ = lean_nat_dec_lt(v___x_2198_, v___x_2236_);
if (v___x_2237_ == 0)
{
lean_dec_ref(v_buckets_2206_);
v___y_2209_ = v___x_2235_;
goto v___jp_2208_;
}
else
{
size_t v___x_2238_; size_t v___x_2239_; lean_object* v___x_2240_; 
v___x_2238_ = lean_usize_of_nat(v___x_2236_);
v___x_2239_ = ((size_t)0ULL);
v___x_2240_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8(v_buckets_2206_, v___x_2238_, v___x_2239_, v___x_2235_);
lean_dec_ref(v_buckets_2206_);
v___y_2209_ = v___x_2240_;
goto v___jp_2208_;
}
v___jp_2208_:
{
lean_object* v___x_2210_; 
v___x_2210_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(v___y_2209_, v___x_2207_);
lean_dec(v___y_2209_);
if (lean_obj_tag(v___x_2210_) == 1)
{
lean_object* v_val_2211_; lean_object* v_snd_2212_; lean_object* v_snd_2213_; lean_object* v_fst_2214_; lean_object* v_fst_2215_; lean_object* v_snd_2216_; lean_object* v___x_2217_; lean_object* v_fst_2218_; lean_object* v_snd_2219_; lean_object* v___x_2220_; lean_object* v_fst_2221_; lean_object* v_snd_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v_val_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_val_2211_);
lean_dec_ref_known(v___x_2210_, 1);
v_snd_2212_ = lean_ctor_get(v_val_2211_, 1);
lean_inc(v_snd_2212_);
lean_dec(v_val_2211_);
v_snd_2213_ = lean_ctor_get(v_snd_2212_, 1);
lean_inc(v_snd_2213_);
v_fst_2214_ = lean_ctor_get(v_snd_2212_, 0);
lean_inc(v_fst_2214_);
lean_dec(v_snd_2212_);
v_fst_2215_ = lean_ctor_get(v_snd_2213_, 0);
lean_inc(v_fst_2215_);
v_snd_2216_ = lean_ctor_get(v_snd_2213_, 1);
lean_inc(v_snd_2216_);
lean_dec(v_snd_2213_);
v___x_2217_ = l_Subarray_split___redArg(v_fst_2193_, v_fst_2215_);
lean_dec(v_fst_2215_);
v_fst_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_fst_2218_);
v_snd_2219_ = lean_ctor_get(v___x_2217_, 1);
lean_inc(v_snd_2219_);
lean_dec_ref(v___x_2217_);
v___x_2220_ = l_Subarray_split___redArg(v_fst_2194_, v_snd_2216_);
lean_dec(v_snd_2216_);
v_fst_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_fst_2221_);
v_snd_2222_ = lean_ctor_get(v___x_2220_, 1);
lean_inc(v_snd_2222_);
lean_dec_ref(v___x_2220_);
v___x_2223_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v_fst_2218_, v_fst_2221_);
v___x_2224_ = l_Array_append___redArg(v_fst_2188_, v___x_2223_);
lean_dec_ref(v___x_2223_);
v___x_2225_ = lean_unsigned_to_nat(1u);
v___x_2226_ = lean_mk_empty_array_with_capacity(v___x_2225_);
v___x_2227_ = lean_array_push(v___x_2226_, v_fst_2214_);
v___x_2228_ = l_Array_append___redArg(v___x_2224_, v___x_2227_);
lean_dec_ref(v___x_2227_);
v___x_2229_ = l_Subarray_drop___redArg(v_snd_2219_, v___x_2225_);
v___x_2230_ = l_Subarray_drop___redArg(v_snd_2222_, v___x_2225_);
v___x_2231_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v___x_2229_, v___x_2230_);
v___x_2232_ = l_Array_append___redArg(v___x_2228_, v___x_2231_);
lean_dec_ref(v___x_2231_);
v___x_2233_ = l_Array_append___redArg(v___x_2232_, v_snd_2195_);
lean_dec(v_snd_2195_);
return v___x_2233_;
}
else
{
lean_object* v___x_2234_; 
lean_dec(v___x_2210_);
lean_dec(v_fst_2194_);
lean_dec(v_fst_2193_);
v___x_2234_ = l_Array_append___redArg(v_fst_2188_, v_snd_2195_);
lean_dec(v_snd_2195_);
return v___x_2234_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(lean_object* v___x_2241_, lean_object* v_original_2242_, lean_object* v_a_2243_){
_start:
{
lean_object* v_fst_2244_; lean_object* v_snd_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2264_; 
v_fst_2244_ = lean_ctor_get(v_a_2243_, 0);
v_snd_2245_ = lean_ctor_get(v_a_2243_, 1);
v_isSharedCheck_2264_ = !lean_is_exclusive(v_a_2243_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2247_ = v_a_2243_;
v_isShared_2248_ = v_isSharedCheck_2264_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_snd_2245_);
lean_inc(v_fst_2244_);
lean_dec(v_a_2243_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2264_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
uint8_t v___x_2249_; 
v___x_2249_ = lean_nat_dec_lt(v_snd_2245_, v___x_2241_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2251_; 
if (v_isShared_2248_ == 0)
{
v___x_2251_ = v___x_2247_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_fst_2244_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_snd_2245_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
else
{
uint8_t v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2257_; 
v___x_2253_ = 1;
v___x_2254_ = lean_array_fget_borrowed(v_original_2242_, v_snd_2245_);
v___x_2255_ = lean_box(v___x_2253_);
lean_inc(v___x_2254_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 1, v___x_2254_);
lean_ctor_set(v___x_2247_, 0, v___x_2255_);
v___x_2257_ = v___x_2247_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2255_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v___x_2254_);
v___x_2257_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2258_ = lean_array_push(v_fst_2244_, v___x_2257_);
v___x_2259_ = lean_unsigned_to_nat(1u);
v___x_2260_ = lean_nat_add(v_snd_2245_, v___x_2259_);
lean_dec(v_snd_2245_);
v___x_2261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2258_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
v_a_2243_ = v___x_2261_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg___boxed(lean_object* v___x_2265_, lean_object* v_original_2266_, lean_object* v_a_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2265_, v_original_2266_, v_a_2267_);
lean_dec_ref(v_original_2266_);
lean_dec(v___x_2265_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(lean_object* v___x_2269_, lean_object* v_edited_2270_, lean_object* v_a_2271_){
_start:
{
lean_object* v_fst_2272_; lean_object* v_snd_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2292_; 
v_fst_2272_ = lean_ctor_get(v_a_2271_, 0);
v_snd_2273_ = lean_ctor_get(v_a_2271_, 1);
v_isSharedCheck_2292_ = !lean_is_exclusive(v_a_2271_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2275_ = v_a_2271_;
v_isShared_2276_ = v_isSharedCheck_2292_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_snd_2273_);
lean_inc(v_fst_2272_);
lean_dec(v_a_2271_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2292_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
uint8_t v___x_2277_; 
v___x_2277_ = lean_nat_dec_lt(v_snd_2273_, v___x_2269_);
if (v___x_2277_ == 0)
{
lean_object* v___x_2279_; 
if (v_isShared_2276_ == 0)
{
v___x_2279_ = v___x_2275_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_fst_2272_);
lean_ctor_set(v_reuseFailAlloc_2280_, 1, v_snd_2273_);
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
uint8_t v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2285_; 
v___x_2281_ = 0;
v___x_2282_ = lean_array_fget_borrowed(v_edited_2270_, v_snd_2273_);
v___x_2283_ = lean_box(v___x_2281_);
lean_inc(v___x_2282_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 1, v___x_2282_);
lean_ctor_set(v___x_2275_, 0, v___x_2283_);
v___x_2285_ = v___x_2275_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2283_);
lean_ctor_set(v_reuseFailAlloc_2291_, 1, v___x_2282_);
v___x_2285_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2286_ = lean_array_push(v_fst_2272_, v___x_2285_);
v___x_2287_ = lean_unsigned_to_nat(1u);
v___x_2288_ = lean_nat_add(v_snd_2273_, v___x_2287_);
lean_dec(v_snd_2273_);
v___x_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2286_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
v_a_2271_ = v___x_2289_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg___boxed(lean_object* v___x_2293_, lean_object* v_edited_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2293_, v_edited_2294_, v_a_2295_);
lean_dec_ref(v_edited_2294_);
lean_dec(v___x_2293_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(lean_object* v___x_2297_, lean_object* v_original_2298_, lean_object* v_a_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v_fst_2301_; lean_object* v_snd_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2326_; 
v_fst_2301_ = lean_ctor_get(v_a_2300_, 0);
v_snd_2302_ = lean_ctor_get(v_a_2300_, 1);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_a_2300_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2304_ = v_a_2300_;
v_isShared_2305_ = v_isSharedCheck_2326_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_snd_2302_);
lean_inc(v_fst_2301_);
lean_dec(v_a_2300_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2326_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
uint8_t v___x_2306_; 
v___x_2306_ = lean_nat_dec_lt(v_snd_2302_, v___x_2297_);
if (v___x_2306_ == 0)
{
lean_object* v___x_2308_; 
if (v_isShared_2305_ == 0)
{
v___x_2308_ = v___x_2304_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_fst_2301_);
lean_ctor_set(v_reuseFailAlloc_2309_, 1, v_snd_2302_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
else
{
lean_object* v___x_2310_; lean_object* v___x_2311_; uint8_t v___x_2312_; 
v___x_2310_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2311_ = lean_array_get_borrowed(v___x_2310_, v_original_2298_, v_snd_2302_);
v___x_2312_ = lean_string_dec_eq(v___x_2311_, v_a_2299_);
if (v___x_2312_ == 0)
{
uint8_t v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2316_; 
v___x_2313_ = 1;
v___x_2314_ = lean_box(v___x_2313_);
lean_inc(v___x_2311_);
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 1, v___x_2311_);
lean_ctor_set(v___x_2304_, 0, v___x_2314_);
v___x_2316_ = v___x_2304_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2314_);
lean_ctor_set(v_reuseFailAlloc_2322_, 1, v___x_2311_);
v___x_2316_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2317_ = lean_array_push(v_fst_2301_, v___x_2316_);
v___x_2318_ = lean_unsigned_to_nat(1u);
v___x_2319_ = lean_nat_add(v_snd_2302_, v___x_2318_);
lean_dec(v_snd_2302_);
v___x_2320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2317_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
v_a_2300_ = v___x_2320_;
goto _start;
}
}
else
{
lean_object* v___x_2324_; 
if (v_isShared_2305_ == 0)
{
v___x_2324_ = v___x_2304_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_fst_2301_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v_snd_2302_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg___boxed(lean_object* v___x_2327_, lean_object* v_original_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2327_, v_original_2328_, v_a_2329_, v_a_2330_);
lean_dec_ref(v_a_2329_);
lean_dec_ref(v_original_2328_);
lean_dec(v___x_2327_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(lean_object* v___x_2332_, lean_object* v_edited_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_){
_start:
{
lean_object* v_fst_2336_; lean_object* v_snd_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2361_; 
v_fst_2336_ = lean_ctor_get(v_a_2335_, 0);
v_snd_2337_ = lean_ctor_get(v_a_2335_, 1);
v_isSharedCheck_2361_ = !lean_is_exclusive(v_a_2335_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2339_ = v_a_2335_;
v_isShared_2340_ = v_isSharedCheck_2361_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_snd_2337_);
lean_inc(v_fst_2336_);
lean_dec(v_a_2335_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2361_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
uint8_t v___x_2341_; 
v___x_2341_ = lean_nat_dec_lt(v_snd_2337_, v___x_2332_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2343_; 
if (v_isShared_2340_ == 0)
{
v___x_2343_ = v___x_2339_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_fst_2336_);
lean_ctor_set(v_reuseFailAlloc_2344_, 1, v_snd_2337_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
else
{
lean_object* v___x_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; 
v___x_2345_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2346_ = lean_array_get_borrowed(v___x_2345_, v_edited_2333_, v_snd_2337_);
v___x_2347_ = lean_string_dec_eq(v___x_2346_, v_a_2334_);
if (v___x_2347_ == 0)
{
uint8_t v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2351_; 
v___x_2348_ = 0;
v___x_2349_ = lean_box(v___x_2348_);
lean_inc(v___x_2346_);
if (v_isShared_2340_ == 0)
{
lean_ctor_set(v___x_2339_, 1, v___x_2346_);
lean_ctor_set(v___x_2339_, 0, v___x_2349_);
v___x_2351_ = v___x_2339_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2349_);
lean_ctor_set(v_reuseFailAlloc_2357_, 1, v___x_2346_);
v___x_2351_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2352_ = lean_array_push(v_fst_2336_, v___x_2351_);
v___x_2353_ = lean_unsigned_to_nat(1u);
v___x_2354_ = lean_nat_add(v_snd_2337_, v___x_2353_);
lean_dec(v_snd_2337_);
v___x_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2352_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
v_a_2335_ = v___x_2355_;
goto _start;
}
}
else
{
lean_object* v___x_2359_; 
if (v_isShared_2340_ == 0)
{
v___x_2359_ = v___x_2339_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_fst_2336_);
lean_ctor_set(v_reuseFailAlloc_2360_, 1, v_snd_2337_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg___boxed(lean_object* v___x_2362_, lean_object* v_edited_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2362_, v_edited_2363_, v_a_2364_, v_a_2365_);
lean_dec_ref(v_a_2364_);
lean_dec_ref(v_edited_2363_);
lean_dec(v___x_2362_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(lean_object* v___x_2367_, lean_object* v_original_2368_, lean_object* v___x_2369_, lean_object* v_edited_2370_, lean_object* v_as_2371_, size_t v_sz_2372_, size_t v_i_2373_, lean_object* v_b_2374_){
_start:
{
uint8_t v___x_2375_; 
v___x_2375_ = lean_usize_dec_lt(v_i_2373_, v_sz_2372_);
if (v___x_2375_ == 0)
{
return v_b_2374_;
}
else
{
lean_object* v_snd_2376_; lean_object* v_fst_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2424_; 
v_snd_2376_ = lean_ctor_get(v_b_2374_, 1);
v_fst_2377_ = lean_ctor_get(v_b_2374_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v_b_2374_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2379_ = v_b_2374_;
v_isShared_2380_ = v_isSharedCheck_2424_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_snd_2376_);
lean_inc(v_fst_2377_);
lean_dec(v_b_2374_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2424_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v_fst_2381_; lean_object* v_snd_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2423_; 
v_fst_2381_ = lean_ctor_get(v_snd_2376_, 0);
v_snd_2382_ = lean_ctor_get(v_snd_2376_, 1);
v_isSharedCheck_2423_ = !lean_is_exclusive(v_snd_2376_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2384_ = v_snd_2376_;
v_isShared_2385_ = v_isSharedCheck_2423_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_snd_2382_);
lean_inc(v_fst_2381_);
lean_dec(v_snd_2376_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2423_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v_a_2386_; lean_object* v___x_2388_; 
v_a_2386_ = lean_array_uget_borrowed(v_as_2371_, v_i_2373_);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 1, v_fst_2381_);
lean_ctor_set(v___x_2384_, 0, v_fst_2377_);
v___x_2388_ = v___x_2384_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_fst_2377_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_fst_2381_);
v___x_2388_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2389_; lean_object* v_fst_2390_; lean_object* v_snd_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2421_; 
v___x_2389_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2367_, v_original_2368_, v_a_2386_, v___x_2388_);
v_fst_2390_ = lean_ctor_get(v___x_2389_, 0);
v_snd_2391_ = lean_ctor_get(v___x_2389_, 1);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2393_ = v___x_2389_;
v_isShared_2394_ = v_isSharedCheck_2421_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_snd_2391_);
lean_inc(v_fst_2390_);
lean_dec(v___x_2389_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2421_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 1, v_snd_2382_);
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_fst_2390_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_snd_2382_);
v___x_2396_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
lean_object* v___x_2397_; lean_object* v_fst_2398_; lean_object* v_snd_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2419_; 
v___x_2397_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2369_, v_edited_2370_, v_a_2386_, v___x_2396_);
v_fst_2398_ = lean_ctor_get(v___x_2397_, 0);
v_snd_2399_ = lean_ctor_get(v___x_2397_, 1);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2401_ = v___x_2397_;
v_isShared_2402_ = v_isSharedCheck_2419_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_snd_2399_);
lean_inc(v_fst_2398_);
lean_dec(v___x_2397_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2419_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
uint8_t v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2406_; 
v___x_2403_ = 2;
v___x_2404_ = lean_box(v___x_2403_);
lean_inc(v_a_2386_);
if (v_isShared_2402_ == 0)
{
lean_ctor_set(v___x_2401_, 1, v_a_2386_);
lean_ctor_set(v___x_2401_, 0, v___x_2404_);
v___x_2406_ = v___x_2401_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2404_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_a_2386_);
v___x_2406_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2412_; 
v___x_2407_ = lean_array_push(v_fst_2398_, v___x_2406_);
v___x_2408_ = lean_unsigned_to_nat(1u);
v___x_2409_ = lean_nat_add(v_snd_2391_, v___x_2408_);
lean_dec(v_snd_2391_);
v___x_2410_ = lean_nat_add(v_snd_2399_, v___x_2408_);
lean_dec(v_snd_2399_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 1, v___x_2410_);
lean_ctor_set(v___x_2379_, 0, v___x_2409_);
v___x_2412_ = v___x_2379_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2409_);
lean_ctor_set(v_reuseFailAlloc_2417_, 1, v___x_2410_);
v___x_2412_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
lean_object* v___x_2413_; size_t v___x_2414_; size_t v___x_2415_; 
v___x_2413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2407_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
v___x_2414_ = ((size_t)1ULL);
v___x_2415_ = lean_usize_add(v_i_2373_, v___x_2414_);
v_i_2373_ = v___x_2415_;
v_b_2374_ = v___x_2413_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14___boxed(lean_object* v___x_2425_, lean_object* v_original_2426_, lean_object* v___x_2427_, lean_object* v_edited_2428_, lean_object* v_as_2429_, lean_object* v_sz_2430_, lean_object* v_i_2431_, lean_object* v_b_2432_){
_start:
{
size_t v_sz_boxed_2433_; size_t v_i_boxed_2434_; lean_object* v_res_2435_; 
v_sz_boxed_2433_ = lean_unbox_usize(v_sz_2430_);
lean_dec(v_sz_2430_);
v_i_boxed_2434_ = lean_unbox_usize(v_i_2431_);
lean_dec(v_i_2431_);
v_res_2435_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v___x_2425_, v_original_2426_, v___x_2427_, v_edited_2428_, v_as_2429_, v_sz_boxed_2433_, v_i_boxed_2434_, v_b_2432_);
lean_dec_ref(v_as_2429_);
lean_dec_ref(v_edited_2428_);
lean_dec(v___x_2427_);
lean_dec_ref(v_original_2426_);
lean_dec(v___x_2425_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(lean_object* v___x_2436_, lean_object* v_edited_2437_, lean_object* v___x_2438_, lean_object* v_original_2439_, lean_object* v_as_2440_, size_t v_sz_2441_, size_t v_i_2442_, lean_object* v_b_2443_){
_start:
{
uint8_t v___x_2444_; 
v___x_2444_ = lean_usize_dec_lt(v_i_2442_, v_sz_2441_);
if (v___x_2444_ == 0)
{
return v_b_2443_;
}
else
{
lean_object* v_snd_2445_; lean_object* v_fst_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2493_; 
v_snd_2445_ = lean_ctor_get(v_b_2443_, 1);
v_fst_2446_ = lean_ctor_get(v_b_2443_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v_b_2443_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2448_ = v_b_2443_;
v_isShared_2449_ = v_isSharedCheck_2493_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_snd_2445_);
lean_inc(v_fst_2446_);
lean_dec(v_b_2443_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2493_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v_fst_2450_; lean_object* v_snd_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2492_; 
v_fst_2450_ = lean_ctor_get(v_snd_2445_, 0);
v_snd_2451_ = lean_ctor_get(v_snd_2445_, 1);
v_isSharedCheck_2492_ = !lean_is_exclusive(v_snd_2445_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2453_ = v_snd_2445_;
v_isShared_2454_ = v_isSharedCheck_2492_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_snd_2451_);
lean_inc(v_fst_2450_);
lean_dec(v_snd_2445_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2492_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v_a_2455_; lean_object* v___x_2457_; 
v_a_2455_ = lean_array_uget_borrowed(v_as_2440_, v_i_2442_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 1, v_fst_2450_);
lean_ctor_set(v___x_2453_, 0, v_fst_2446_);
v___x_2457_ = v___x_2453_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_fst_2446_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v_fst_2450_);
v___x_2457_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2458_; lean_object* v_fst_2459_; lean_object* v_snd_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2490_; 
v___x_2458_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2438_, v_original_2439_, v_a_2455_, v___x_2457_);
v_fst_2459_ = lean_ctor_get(v___x_2458_, 0);
v_snd_2460_ = lean_ctor_get(v___x_2458_, 1);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2462_ = v___x_2458_;
v_isShared_2463_ = v_isSharedCheck_2490_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_snd_2460_);
lean_inc(v_fst_2459_);
lean_dec(v___x_2458_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2490_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
lean_ctor_set(v___x_2462_, 1, v_snd_2451_);
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_fst_2459_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v_snd_2451_);
v___x_2465_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
lean_object* v___x_2466_; lean_object* v_fst_2467_; lean_object* v_snd_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2488_; 
v___x_2466_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2436_, v_edited_2437_, v_a_2455_, v___x_2465_);
v_fst_2467_ = lean_ctor_get(v___x_2466_, 0);
v_snd_2468_ = lean_ctor_get(v___x_2466_, 1);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2470_ = v___x_2466_;
v_isShared_2471_ = v_isSharedCheck_2488_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_snd_2468_);
lean_inc(v_fst_2467_);
lean_dec(v___x_2466_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2488_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
uint8_t v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2475_; 
v___x_2472_ = 2;
v___x_2473_ = lean_box(v___x_2472_);
lean_inc(v_a_2455_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 1, v_a_2455_);
lean_ctor_set(v___x_2470_, 0, v___x_2473_);
v___x_2475_ = v___x_2470_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v_a_2455_);
v___x_2475_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2481_; 
v___x_2476_ = lean_array_push(v_fst_2467_, v___x_2475_);
v___x_2477_ = lean_unsigned_to_nat(1u);
v___x_2478_ = lean_nat_add(v_snd_2460_, v___x_2477_);
lean_dec(v_snd_2460_);
v___x_2479_ = lean_nat_add(v_snd_2468_, v___x_2477_);
lean_dec(v_snd_2468_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 1, v___x_2479_);
lean_ctor_set(v___x_2448_, 0, v___x_2478_);
v___x_2481_ = v___x_2448_;
goto v_reusejp_2480_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v___x_2478_);
lean_ctor_set(v_reuseFailAlloc_2486_, 1, v___x_2479_);
v___x_2481_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2480_;
}
v_reusejp_2480_:
{
lean_object* v___x_2482_; size_t v___x_2483_; size_t v___x_2484_; lean_object* v___x_2485_; 
v___x_2482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2476_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
v___x_2483_ = ((size_t)1ULL);
v___x_2484_ = lean_usize_add(v_i_2442_, v___x_2483_);
v___x_2485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v___x_2438_, v_original_2439_, v___x_2436_, v_edited_2437_, v_as_2440_, v_sz_2441_, v___x_2484_, v___x_2482_);
return v___x_2485_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4___boxed(lean_object* v___x_2494_, lean_object* v_edited_2495_, lean_object* v___x_2496_, lean_object* v_original_2497_, lean_object* v_as_2498_, lean_object* v_sz_2499_, lean_object* v_i_2500_, lean_object* v_b_2501_){
_start:
{
size_t v_sz_boxed_2502_; size_t v_i_boxed_2503_; lean_object* v_res_2504_; 
v_sz_boxed_2502_ = lean_unbox_usize(v_sz_2499_);
lean_dec(v_sz_2499_);
v_i_boxed_2503_ = lean_unbox_usize(v_i_2500_);
lean_dec(v_i_2500_);
v_res_2504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v___x_2494_, v_edited_2495_, v___x_2496_, v_original_2497_, v_as_2498_, v_sz_boxed_2502_, v_i_boxed_2503_, v_b_2501_);
lean_dec_ref(v_as_2498_);
lean_dec_ref(v_original_2497_);
lean_dec(v___x_2496_);
lean_dec_ref(v_edited_2495_);
lean_dec(v___x_2494_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(size_t v_sz_2505_, size_t v_i_2506_, lean_object* v_bs_2507_){
_start:
{
uint8_t v___x_2508_; 
v___x_2508_ = lean_usize_dec_lt(v_i_2506_, v_sz_2505_);
if (v___x_2508_ == 0)
{
return v_bs_2507_;
}
else
{
lean_object* v_v_2509_; lean_object* v___x_2510_; lean_object* v_bs_x27_2511_; uint8_t v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; size_t v___x_2515_; size_t v___x_2516_; lean_object* v___x_2517_; 
v_v_2509_ = lean_array_uget(v_bs_2507_, v_i_2506_);
v___x_2510_ = lean_unsigned_to_nat(0u);
v_bs_x27_2511_ = lean_array_uset(v_bs_2507_, v_i_2506_, v___x_2510_);
v___x_2512_ = 1;
v___x_2513_ = lean_box(v___x_2512_);
v___x_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2514_, 0, v___x_2513_);
lean_ctor_set(v___x_2514_, 1, v_v_2509_);
v___x_2515_ = ((size_t)1ULL);
v___x_2516_ = lean_usize_add(v_i_2506_, v___x_2515_);
v___x_2517_ = lean_array_uset(v_bs_x27_2511_, v_i_2506_, v___x_2514_);
v_i_2506_ = v___x_2516_;
v_bs_2507_ = v___x_2517_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7___boxed(lean_object* v_sz_2519_, lean_object* v_i_2520_, lean_object* v_bs_2521_){
_start:
{
size_t v_sz_boxed_2522_; size_t v_i_boxed_2523_; lean_object* v_res_2524_; 
v_sz_boxed_2522_ = lean_unbox_usize(v_sz_2519_);
lean_dec(v_sz_2519_);
v_i_boxed_2523_ = lean_unbox_usize(v_i_2520_);
lean_dec(v_i_2520_);
v_res_2524_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_boxed_2522_, v_i_boxed_2523_, v_bs_2521_);
return v_res_2524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(lean_object* v_original_2530_, lean_object* v_edited_2531_){
_start:
{
lean_object* v_i_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v_i_2532_ = lean_unsigned_to_nat(0u);
v___x_2533_ = lean_array_get_size(v_original_2530_);
v___x_2534_ = lean_nat_dec_lt(v_i_2532_, v___x_2533_);
if (v___x_2534_ == 0)
{
size_t v_sz_2535_; size_t v___x_2536_; lean_object* v___x_2537_; 
lean_dec_ref(v_original_2530_);
v_sz_2535_ = lean_array_size(v_edited_2531_);
v___x_2536_ = ((size_t)0ULL);
v___x_2537_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_2535_, v___x_2536_, v_edited_2531_);
return v___x_2537_;
}
else
{
lean_object* v___x_2538_; uint8_t v___x_2539_; 
v___x_2538_ = lean_array_get_size(v_edited_2531_);
v___x_2539_ = lean_nat_dec_lt(v_i_2532_, v___x_2538_);
if (v___x_2539_ == 0)
{
size_t v_sz_2540_; size_t v___x_2541_; lean_object* v___x_2542_; 
lean_dec_ref(v_edited_2531_);
v_sz_2540_ = lean_array_size(v_original_2530_);
v___x_2541_ = ((size_t)0ULL);
v___x_2542_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_2540_, v___x_2541_, v_original_2530_);
return v___x_2542_;
}
else
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v_ds_2545_; lean_object* v___x_2546_; size_t v_sz_2547_; size_t v___x_2548_; lean_object* v___x_2549_; lean_object* v_snd_2550_; lean_object* v_fst_2551_; lean_object* v_fst_2552_; lean_object* v_snd_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2572_; 
lean_inc_ref(v_original_2530_);
v___x_2543_ = l_Array_toSubarray___redArg(v_original_2530_, v_i_2532_, v___x_2533_);
lean_inc_ref(v_edited_2531_);
v___x_2544_ = l_Array_toSubarray___redArg(v_edited_2531_, v_i_2532_, v___x_2538_);
v_ds_2545_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v___x_2543_, v___x_2544_);
v___x_2546_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__1));
v_sz_2547_ = lean_array_size(v_ds_2545_);
v___x_2548_ = ((size_t)0ULL);
v___x_2549_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v___x_2538_, v_edited_2531_, v___x_2533_, v_original_2530_, v_ds_2545_, v_sz_2547_, v___x_2548_, v___x_2546_);
lean_dec_ref(v_ds_2545_);
v_snd_2550_ = lean_ctor_get(v___x_2549_, 1);
lean_inc(v_snd_2550_);
v_fst_2551_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_fst_2551_);
lean_dec_ref(v___x_2549_);
v_fst_2552_ = lean_ctor_get(v_snd_2550_, 0);
v_snd_2553_ = lean_ctor_get(v_snd_2550_, 1);
v_isSharedCheck_2572_ = !lean_is_exclusive(v_snd_2550_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2555_ = v_snd_2550_;
v_isShared_2556_ = v_isSharedCheck_2572_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_snd_2553_);
lean_inc(v_fst_2552_);
lean_dec(v_snd_2550_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2572_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 1, v_fst_2552_);
lean_ctor_set(v___x_2555_, 0, v_fst_2551_);
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_fst_2551_);
lean_ctor_set(v_reuseFailAlloc_2571_, 1, v_fst_2552_);
v___x_2558_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
lean_object* v___x_2559_; lean_object* v_fst_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2569_; 
v___x_2559_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2533_, v_original_2530_, v___x_2558_);
lean_dec_ref(v_original_2530_);
v_fst_2560_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2569_ == 0)
{
lean_object* v_unused_2570_; 
v_unused_2570_ = lean_ctor_get(v___x_2559_, 1);
lean_dec(v_unused_2570_);
v___x_2562_ = v___x_2559_;
v_isShared_2563_ = v_isSharedCheck_2569_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_fst_2560_);
lean_dec(v___x_2559_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2569_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 1, v_snd_2553_);
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_fst_2560_);
lean_ctor_set(v_reuseFailAlloc_2568_, 1, v_snd_2553_);
v___x_2565_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
lean_object* v___x_2566_; lean_object* v_fst_2567_; 
v___x_2566_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2538_, v_edited_2531_, v___x_2565_);
lean_dec_ref(v_edited_2531_);
v_fst_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_fst_2567_);
lean_dec_ref(v___x_2566_);
return v_fst_2567_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(lean_object* v___x_2573_, uint8_t v_inSubst_2574_, lean_object* v___x_2575_, lean_object* v_____r_2576_, lean_object* v_wssIdx_2577_){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2578_ = lean_box(v_inSubst_2574_);
v___x_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2573_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
v___x_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2580_, 0, v_wssIdx_2577_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
v___x_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2575_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
v___x_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2581_);
return v___x_2582_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1___boxed(lean_object* v___x_2583_, lean_object* v_inSubst_2584_, lean_object* v___x_2585_, lean_object* v_____r_2586_, lean_object* v_wssIdx_2587_){
_start:
{
uint8_t v_inSubst_boxed_2588_; lean_object* v_res_2589_; 
v_inSubst_boxed_2588_ = lean_unbox(v_inSubst_2584_);
v_res_2589_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2583_, v_inSubst_boxed_2588_, v___x_2585_, v_____r_2586_, v_wssIdx_2587_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(lean_object* v_fst_2590_, uint8_t v___x_2591_, lean_object* v_fst_2592_, lean_object* v___x_2593_, lean_object* v_00___2594_){
_start:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; 
v___x_2595_ = lean_box(v___x_2591_);
v___x_2596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2596_, 0, v_fst_2590_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
v___x_2597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2597_, 0, v_fst_2592_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
v___x_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2593_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
v___x_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2598_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0___boxed(lean_object* v_fst_2600_, lean_object* v___x_2601_, lean_object* v_fst_2602_, lean_object* v___x_2603_, lean_object* v_00___2604_){
_start:
{
uint8_t v___x_9128__boxed_2605_; lean_object* v_res_2606_; 
v___x_9128__boxed_2605_ = lean_unbox(v___x_2601_);
v_res_2606_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2600_, v___x_9128__boxed_2605_, v_fst_2602_, v___x_2603_, v_00___2604_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(uint8_t v_inSubst_2607_, lean_object* v_snd_2608_, lean_object* v_fst_2609_, lean_object* v_____r_2610_, lean_object* v_withWs_2611_, lean_object* v_wssIdx_2612_){
_start:
{
lean_object* v_wss_x27Idx_2614_; uint8_t v___x_2620_; 
v___x_2620_ = lean_unbox(v_snd_2608_);
if (v___x_2620_ == 0)
{
v_wss_x27Idx_2614_ = v_fst_2609_;
goto v___jp_2613_;
}
else
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2621_ = lean_unsigned_to_nat(1u);
v___x_2622_ = lean_nat_add(v_fst_2609_, v___x_2621_);
lean_dec(v_fst_2609_);
v_wss_x27Idx_2614_ = v___x_2622_;
goto v___jp_2613_;
}
v___jp_2613_:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2615_ = lean_box(v_inSubst_2607_);
v___x_2616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2616_, 0, v_wss_x27Idx_2614_);
lean_ctor_set(v___x_2616_, 1, v___x_2615_);
v___x_2617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2617_, 0, v_wssIdx_2612_);
lean_ctor_set(v___x_2617_, 1, v___x_2616_);
v___x_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2618_, 0, v_withWs_2611_);
lean_ctor_set(v___x_2618_, 1, v___x_2617_);
v___x_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2618_);
return v___x_2619_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2___boxed(lean_object* v_inSubst_2623_, lean_object* v_snd_2624_, lean_object* v_fst_2625_, lean_object* v_____r_2626_, lean_object* v_withWs_2627_, lean_object* v_wssIdx_2628_){
_start:
{
uint8_t v_inSubst_boxed_2629_; lean_object* v_res_2630_; 
v_inSubst_boxed_2629_ = lean_unbox(v_inSubst_2623_);
v_res_2630_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_boxed_2629_, v_snd_2624_, v_fst_2625_, v_____r_2626_, v_withWs_2627_, v_wssIdx_2628_);
lean_dec(v_snd_2624_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(lean_object* v_upperBound_2631_, lean_object* v_diff_2632_, lean_object* v_snd_2633_, lean_object* v_snd_2634_, lean_object* v_a_2635_, lean_object* v_b_2636_){
_start:
{
lean_object* v_a_2638_; lean_object* v___y_2643_; uint8_t v___x_2646_; 
v___x_2646_ = lean_nat_dec_lt(v_a_2635_, v_upperBound_2631_);
if (v___x_2646_ == 0)
{
lean_dec(v_a_2635_);
return v_b_2636_;
}
else
{
lean_object* v___x_2647_; lean_object* v_snd_2648_; lean_object* v_snd_2649_; lean_object* v_fst_2650_; lean_object* v_fst_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2791_; 
v___x_2647_ = lean_array_fget_borrowed(v_diff_2632_, v_a_2635_);
v_snd_2648_ = lean_ctor_get(v_b_2636_, 1);
lean_inc(v_snd_2648_);
v_snd_2649_ = lean_ctor_get(v_snd_2648_, 1);
lean_inc(v_snd_2649_);
v_fst_2650_ = lean_ctor_get(v___x_2647_, 0);
v_fst_2651_ = lean_ctor_get(v_b_2636_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v_b_2636_);
if (v_isSharedCheck_2791_ == 0)
{
lean_object* v_unused_2792_; 
v_unused_2792_ = lean_ctor_get(v_b_2636_, 1);
lean_dec(v_unused_2792_);
v___x_2653_ = v_b_2636_;
v_isShared_2654_ = v_isSharedCheck_2791_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_fst_2651_);
lean_dec(v_b_2636_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2791_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v_fst_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2789_; 
v_fst_2655_ = lean_ctor_get(v_snd_2648_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_snd_2648_);
if (v_isSharedCheck_2789_ == 0)
{
lean_object* v_unused_2790_; 
v_unused_2790_ = lean_ctor_get(v_snd_2648_, 1);
lean_dec(v_unused_2790_);
v___x_2657_ = v_snd_2648_;
v_isShared_2658_ = v_isSharedCheck_2789_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_fst_2655_);
lean_dec(v_snd_2648_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2789_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v_fst_2659_; lean_object* v_snd_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2788_; 
v_fst_2659_ = lean_ctor_get(v_snd_2649_, 0);
v_snd_2660_ = lean_ctor_get(v_snd_2649_, 1);
v_isSharedCheck_2788_ = !lean_is_exclusive(v_snd_2649_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2662_ = v_snd_2649_;
v_isShared_2663_ = v_isSharedCheck_2788_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_snd_2660_);
lean_inc(v_fst_2659_);
lean_dec(v_snd_2649_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2788_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2664_; lean_object* v___y_2666_; lean_object* v___y_2681_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; uint8_t v___x_2692_; 
lean_inc(v___x_2647_);
v___x_2664_ = lean_array_push(v_fst_2651_, v___x_2647_);
v___x_2689_ = lean_unsigned_to_nat(1u);
v___x_2690_ = lean_nat_add(v_a_2635_, v___x_2689_);
v___x_2691_ = lean_array_get_size(v_diff_2632_);
v___x_2692_ = lean_nat_dec_lt(v___x_2690_, v___x_2691_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
lean_dec(v___x_2690_);
lean_del_object(v___x_2662_);
lean_del_object(v___x_2657_);
lean_del_object(v___x_2653_);
v___x_2693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2693_, 0, v_fst_2659_);
lean_ctor_set(v___x_2693_, 1, v_snd_2660_);
v___x_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2694_, 0, v_fst_2655_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
v___x_2695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2664_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v_a_2638_ = v___x_2695_;
goto v___jp_2637_;
}
else
{
lean_object* v___x_2696_; lean_object* v_fst_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2786_; 
v___x_2696_ = lean_array_fget(v_diff_2632_, v___x_2690_);
lean_dec(v___x_2690_);
v_fst_2697_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2786_ == 0)
{
lean_object* v_unused_2787_; 
v_unused_2787_ = lean_ctor_get(v___x_2696_, 1);
lean_dec(v_unused_2787_);
v___x_2699_ = v___x_2696_;
v_isShared_2700_ = v_isSharedCheck_2786_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_fst_2697_);
lean_dec(v___x_2696_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2786_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
uint8_t v_inSubst_2701_; lean_object* v___y_2703_; lean_object* v___x_2712_; uint8_t v___x_2713_; 
v_inSubst_2701_ = 0;
v___x_2712_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2713_ = lean_unbox(v_fst_2650_);
switch(v___x_2713_)
{
case 0:
{
uint8_t v___x_2714_; 
lean_del_object(v___x_2662_);
lean_del_object(v___x_2657_);
lean_del_object(v___x_2653_);
v___x_2714_ = lean_unbox(v_fst_2697_);
switch(v___x_2714_)
{
case 0:
{
lean_object* v___x_2715_; lean_object* v___x_2717_; 
v___x_2715_ = lean_array_get_borrowed(v___x_2712_, v_snd_2633_, v_fst_2659_);
lean_inc(v___x_2715_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 1, v___x_2715_);
v___x_2717_ = v___x_2699_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_fst_2697_);
lean_ctor_set(v_reuseFailAlloc_2723_, 1, v___x_2715_);
v___x_2717_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2718_ = lean_array_push(v___x_2664_, v___x_2717_);
v___x_2719_ = lean_nat_add(v_fst_2659_, v___x_2689_);
lean_dec(v_fst_2659_);
v___x_2720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2719_);
lean_ctor_set(v___x_2720_, 1, v_snd_2660_);
v___x_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2721_, 0, v_fst_2655_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2718_);
lean_ctor_set(v___x_2722_, 1, v___x_2721_);
v_a_2638_ = v___x_2722_;
goto v___jp_2637_;
}
}
case 1:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
lean_del_object(v___x_2699_);
lean_dec(v_fst_2697_);
lean_dec(v_snd_2660_);
v___x_2724_ = lean_box(0);
v___x_2725_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2659_, v___x_2646_, v_fst_2655_, v___x_2664_, v___x_2724_);
v___y_2643_ = v___x_2725_;
goto v___jp_2642_;
}
default: 
{
lean_object* v___x_2726_; uint8_t v___x_2727_; 
lean_dec(v_fst_2697_);
v___x_2726_ = lean_array_get_borrowed(v___x_2712_, v_snd_2633_, v_fst_2659_);
v___x_2727_ = lean_unbox(v_snd_2660_);
if (v___x_2727_ == 0)
{
lean_object* v___x_2729_; 
lean_inc(v___x_2726_);
lean_inc(v_fst_2650_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 1, v___x_2726_);
lean_ctor_set(v___x_2699_, 0, v_fst_2650_);
v___x_2729_ = v___x_2699_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v_fst_2650_);
lean_ctor_set(v_reuseFailAlloc_2732_, 1, v___x_2726_);
v___x_2729_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2730_ = lean_mk_empty_array_with_capacity(v___x_2689_);
v___x_2731_ = lean_array_push(v___x_2730_, v___x_2729_);
v___y_2703_ = v___x_2731_;
goto v___jp_2702_;
}
}
else
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
lean_del_object(v___x_2699_);
v___x_2733_ = lean_array_get_borrowed(v___x_2712_, v_snd_2634_, v_fst_2655_);
lean_inc(v___x_2726_);
lean_inc(v___x_2733_);
v___x_2734_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2733_, v___x_2726_);
v___y_2703_ = v___x_2734_;
goto v___jp_2702_;
}
}
}
}
case 1:
{
uint8_t v___x_2735_; 
lean_del_object(v___x_2662_);
lean_del_object(v___x_2657_);
lean_del_object(v___x_2653_);
v___x_2735_ = lean_unbox(v_fst_2697_);
switch(v___x_2735_)
{
case 0:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
lean_del_object(v___x_2699_);
lean_dec(v_fst_2697_);
lean_dec(v_snd_2660_);
v___x_2736_ = lean_box(0);
v___x_2737_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2659_, v___x_2646_, v_fst_2655_, v___x_2664_, v___x_2736_);
v___y_2643_ = v___x_2737_;
goto v___jp_2642_;
}
case 1:
{
lean_object* v___x_2738_; lean_object* v___x_2740_; 
v___x_2738_ = lean_array_get_borrowed(v___x_2712_, v_snd_2634_, v_fst_2655_);
lean_inc(v___x_2738_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 1, v___x_2738_);
v___x_2740_ = v___x_2699_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_fst_2697_);
lean_ctor_set(v_reuseFailAlloc_2746_, 1, v___x_2738_);
v___x_2740_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2741_ = lean_array_push(v___x_2664_, v___x_2740_);
v___x_2742_ = lean_nat_add(v_fst_2655_, v___x_2689_);
lean_dec(v_fst_2655_);
v___x_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2743_, 0, v_fst_2659_);
lean_ctor_set(v___x_2743_, 1, v_snd_2660_);
v___x_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2744_, 0, v___x_2742_);
lean_ctor_set(v___x_2744_, 1, v___x_2743_);
v___x_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2741_);
lean_ctor_set(v___x_2745_, 1, v___x_2744_);
v_a_2638_ = v___x_2745_;
goto v___jp_2637_;
}
}
default: 
{
uint8_t v___x_2750_; 
lean_dec(v_fst_2697_);
v___x_2750_ = lean_unbox(v_snd_2660_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; 
v___x_2751_ = lean_array_get_borrowed(v___x_2712_, v_snd_2634_, v_fst_2655_);
v___x_2752_ = lean_unsigned_to_nat(0u);
v___x_2753_ = lean_string_utf8_byte_size(v___x_2751_);
lean_inc(v___x_2751_);
v___x_2754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2751_);
lean_ctor_set(v___x_2754_, 1, v___x_2752_);
lean_ctor_set(v___x_2754_, 2, v___x_2753_);
v___x_2755_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_2754_);
lean_dec_ref_known(v___x_2754_, 3);
if (v___x_2755_ == 0)
{
lean_object* v___x_2757_; 
lean_inc(v___x_2751_);
lean_inc(v_fst_2650_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 1, v___x_2751_);
lean_ctor_set(v___x_2699_, 0, v_fst_2650_);
v___x_2757_ = v___x_2699_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_fst_2650_);
lean_ctor_set(v_reuseFailAlloc_2762_, 1, v___x_2751_);
v___x_2757_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2758_ = lean_array_push(v___x_2664_, v___x_2757_);
v___x_2759_ = lean_nat_add(v_fst_2655_, v___x_2689_);
lean_dec(v_fst_2655_);
v___x_2760_ = lean_box(0);
v___x_2761_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2701_, v_snd_2660_, v_fst_2659_, v___x_2760_, v___x_2758_, v___x_2759_);
lean_dec(v_snd_2660_);
v___y_2643_ = v___x_2761_;
goto v___jp_2642_;
}
}
else
{
lean_del_object(v___x_2699_);
goto v___jp_2747_;
}
}
else
{
lean_del_object(v___x_2699_);
goto v___jp_2747_;
}
v___jp_2747_:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2748_ = lean_box(0);
v___x_2749_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2701_, v_snd_2660_, v_fst_2659_, v___x_2748_, v___x_2664_, v_fst_2655_);
lean_dec(v_snd_2660_);
v___y_2643_ = v___x_2749_;
goto v___jp_2642_;
}
}
}
}
default: 
{
uint8_t v___x_2763_; 
v___x_2763_ = lean_unbox(v_fst_2697_);
if (v___x_2763_ == 1)
{
lean_object* v___x_2764_; lean_object* v___x_2765_; uint8_t v___x_2766_; 
v___x_2764_ = lean_array_get_borrowed(v___x_2712_, v_snd_2634_, v_fst_2655_);
v___x_2765_ = lean_array_get_size(v_snd_2633_);
v___x_2766_ = lean_nat_dec_lt(v_fst_2659_, v___x_2765_);
if (v___x_2766_ == 0)
{
lean_object* v___x_2768_; 
lean_inc(v___x_2764_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 1, v___x_2764_);
v___x_2768_ = v___x_2699_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_fst_2697_);
lean_ctor_set(v_reuseFailAlloc_2771_, 1, v___x_2764_);
v___x_2768_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2769_ = lean_mk_empty_array_with_capacity(v___x_2689_);
v___x_2770_ = lean_array_push(v___x_2769_, v___x_2768_);
v___y_2666_ = v___x_2770_;
goto v___jp_2665_;
}
}
else
{
lean_object* v___x_2772_; lean_object* v___x_2773_; 
lean_del_object(v___x_2699_);
lean_dec(v_fst_2697_);
v___x_2772_ = lean_array_fget_borrowed(v_snd_2633_, v_fst_2659_);
lean_inc(v___x_2772_);
lean_inc(v___x_2764_);
v___x_2773_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2764_, v___x_2772_);
v___y_2666_ = v___x_2773_;
goto v___jp_2665_;
}
}
else
{
lean_object* v___x_2774_; lean_object* v___x_2775_; uint8_t v___x_2776_; 
lean_dec(v_fst_2697_);
lean_del_object(v___x_2662_);
lean_del_object(v___x_2657_);
lean_del_object(v___x_2653_);
v___x_2774_ = lean_array_get_borrowed(v___x_2712_, v_snd_2633_, v_fst_2659_);
v___x_2775_ = lean_array_get_size(v_snd_2634_);
v___x_2776_ = lean_nat_dec_lt(v_fst_2655_, v___x_2775_);
if (v___x_2776_ == 0)
{
uint8_t v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2780_; 
v___x_2777_ = 0;
v___x_2778_ = lean_box(v___x_2777_);
lean_inc(v___x_2774_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 1, v___x_2774_);
lean_ctor_set(v___x_2699_, 0, v___x_2778_);
v___x_2780_ = v___x_2699_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2778_);
lean_ctor_set(v_reuseFailAlloc_2783_, 1, v___x_2774_);
v___x_2780_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; 
v___x_2781_ = lean_mk_empty_array_with_capacity(v___x_2689_);
v___x_2782_ = lean_array_push(v___x_2781_, v___x_2780_);
v___y_2681_ = v___x_2782_;
goto v___jp_2680_;
}
}
else
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
lean_del_object(v___x_2699_);
v___x_2784_ = lean_array_fget_borrowed(v_snd_2634_, v_fst_2655_);
lean_inc(v___x_2774_);
lean_inc(v___x_2784_);
v___x_2785_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2784_, v___x_2774_);
v___y_2681_ = v___x_2785_;
goto v___jp_2680_;
}
}
}
}
v___jp_2702_:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; uint8_t v___x_2706_; 
v___x_2704_ = l_Array_append___redArg(v___x_2664_, v___y_2703_);
lean_dec_ref(v___y_2703_);
v___x_2705_ = lean_nat_add(v_fst_2659_, v___x_2689_);
lean_dec(v_fst_2659_);
v___x_2706_ = lean_unbox(v_snd_2660_);
lean_dec(v_snd_2660_);
if (v___x_2706_ == 0)
{
lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2707_ = lean_box(0);
v___x_2708_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2705_, v_inSubst_2701_, v___x_2704_, v___x_2707_, v_fst_2655_);
v___y_2643_ = v___x_2708_;
goto v___jp_2642_;
}
else
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2709_ = lean_nat_add(v_fst_2655_, v___x_2689_);
lean_dec(v_fst_2655_);
v___x_2710_ = lean_box(0);
v___x_2711_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2705_, v_inSubst_2701_, v___x_2704_, v___x_2710_, v___x_2709_);
v___y_2643_ = v___x_2711_;
goto v___jp_2642_;
}
}
}
}
v___jp_2665_:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2672_; 
v___x_2667_ = l_Array_append___redArg(v___x_2664_, v___y_2666_);
lean_dec_ref(v___y_2666_);
v___x_2668_ = lean_unsigned_to_nat(1u);
v___x_2669_ = lean_nat_add(v_fst_2655_, v___x_2668_);
lean_dec(v_fst_2655_);
v___x_2670_ = lean_nat_add(v_fst_2659_, v___x_2668_);
lean_dec(v_fst_2659_);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v___x_2670_);
v___x_2672_ = v___x_2662_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2670_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v_snd_2660_);
v___x_2672_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2674_; 
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 1, v___x_2672_);
lean_ctor_set(v___x_2657_, 0, v___x_2669_);
v___x_2674_ = v___x_2657_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2669_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v___x_2672_);
v___x_2674_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
lean_object* v___x_2676_; 
if (v_isShared_2654_ == 0)
{
lean_ctor_set(v___x_2653_, 1, v___x_2674_);
lean_ctor_set(v___x_2653_, 0, v___x_2667_);
v___x_2676_ = v___x_2653_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2667_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
v_a_2638_ = v___x_2676_;
goto v___jp_2637_;
}
}
}
}
v___jp_2680_:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2682_ = l_Array_append___redArg(v___x_2664_, v___y_2681_);
lean_dec_ref(v___y_2681_);
v___x_2683_ = lean_unsigned_to_nat(1u);
v___x_2684_ = lean_nat_add(v_fst_2655_, v___x_2683_);
lean_dec(v_fst_2655_);
v___x_2685_ = lean_nat_add(v_fst_2659_, v___x_2683_);
lean_dec(v_fst_2659_);
v___x_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2685_);
lean_ctor_set(v___x_2686_, 1, v_snd_2660_);
v___x_2687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2684_);
lean_ctor_set(v___x_2687_, 1, v___x_2686_);
v___x_2688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2682_);
lean_ctor_set(v___x_2688_, 1, v___x_2687_);
v_a_2638_ = v___x_2688_;
goto v___jp_2637_;
}
}
}
}
}
v___jp_2637_:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2639_ = lean_unsigned_to_nat(1u);
v___x_2640_ = lean_nat_add(v_a_2635_, v___x_2639_);
lean_dec(v_a_2635_);
v_a_2635_ = v___x_2640_;
v_b_2636_ = v_a_2638_;
goto _start;
}
v___jp_2642_:
{
if (lean_obj_tag(v___y_2643_) == 0)
{
lean_object* v_a_2644_; 
lean_dec(v_a_2635_);
v_a_2644_ = lean_ctor_get(v___y_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v___y_2643_, 1);
return v_a_2644_;
}
else
{
lean_object* v_a_2645_; 
v_a_2645_ = lean_ctor_get(v___y_2643_, 0);
lean_inc(v_a_2645_);
lean_dec_ref_known(v___y_2643_, 1);
v_a_2638_ = v_a_2645_;
goto v___jp_2637_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___boxed(lean_object* v_upperBound_2793_, lean_object* v_diff_2794_, lean_object* v_snd_2795_, lean_object* v_snd_2796_, lean_object* v_a_2797_, lean_object* v_b_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2793_, v_diff_2794_, v_snd_2795_, v_snd_2796_, v_a_2797_, v_b_2798_);
lean_dec_ref(v_snd_2796_);
lean_dec_ref(v_snd_2795_);
lean_dec_ref(v_diff_2794_);
lean_dec(v_upperBound_2793_);
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(lean_object* v_s_2810_, lean_object* v_s_x27_2811_){
_start:
{
lean_object* v___x_2812_; lean_object* v_fst_2813_; lean_object* v_snd_2814_; lean_object* v___x_2815_; lean_object* v_fst_2816_; lean_object* v_snd_2817_; lean_object* v_diff_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v_fst_2823_; lean_object* v___x_2824_; size_t v_sz_2825_; size_t v___x_2826_; lean_object* v___x_2827_; 
v___x_2812_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_2810_);
v_fst_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_fst_2813_);
v_snd_2814_ = lean_ctor_get(v___x_2812_, 1);
lean_inc(v_snd_2814_);
lean_dec_ref(v___x_2812_);
v___x_2815_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_x27_2811_);
v_fst_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_fst_2816_);
v_snd_2817_ = lean_ctor_get(v___x_2815_, 1);
lean_inc(v_snd_2817_);
lean_dec_ref(v___x_2815_);
v_diff_2818_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(v_fst_2813_, v_fst_2816_);
v___x_2819_ = lean_unsigned_to_nat(0u);
v___x_2820_ = lean_array_get_size(v_diff_2818_);
v___x_2821_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__2));
v___x_2822_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v___x_2820_, v_diff_2818_, v_snd_2817_, v_snd_2814_, v___x_2819_, v___x_2821_);
lean_dec(v_snd_2814_);
lean_dec(v_snd_2817_);
lean_dec_ref(v_diff_2818_);
v_fst_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_fst_2823_);
lean_dec_ref(v___x_2822_);
v___x_2824_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_fst_2823_);
lean_dec(v_fst_2823_);
v_sz_2825_ = lean_array_size(v___x_2824_);
v___x_2826_ = ((size_t)0ULL);
v___x_2827_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_2825_, v___x_2826_, v___x_2824_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___boxed(lean_object* v_s_2828_, lean_object* v_s_x27_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_2828_, v_s_x27_2829_);
lean_dec_ref(v_s_x27_2829_);
lean_dec_ref(v_s_2828_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(lean_object* v_upperBound_2831_, lean_object* v_diff_2832_, lean_object* v_snd_2833_, lean_object* v_snd_2834_, lean_object* v_inst_2835_, lean_object* v_R_2836_, lean_object* v_a_2837_, lean_object* v_b_2838_, lean_object* v_c_2839_){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2831_, v_diff_2832_, v_snd_2833_, v_snd_2834_, v_a_2837_, v_b_2838_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___boxed(lean_object* v_upperBound_2841_, lean_object* v_diff_2842_, lean_object* v_snd_2843_, lean_object* v_snd_2844_, lean_object* v_inst_2845_, lean_object* v_R_2846_, lean_object* v_a_2847_, lean_object* v_b_2848_, lean_object* v_c_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(v_upperBound_2841_, v_diff_2842_, v_snd_2843_, v_snd_2844_, v_inst_2845_, v_R_2846_, v_a_2847_, v_b_2848_, v_c_2849_);
lean_dec_ref(v_snd_2844_);
lean_dec_ref(v_snd_2843_);
lean_dec_ref(v_diff_2842_);
lean_dec(v_upperBound_2841_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(lean_object* v___x_2851_, lean_object* v_original_2852_, lean_object* v_a_2853_, lean_object* v_inst_2854_, lean_object* v_a_2855_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2851_, v_original_2852_, v_a_2853_, v_a_2855_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___boxed(lean_object* v___x_2857_, lean_object* v_original_2858_, lean_object* v_a_2859_, lean_object* v_inst_2860_, lean_object* v_a_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v___x_2857_, v_original_2858_, v_a_2859_, v_inst_2860_, v_a_2861_);
lean_dec_ref(v_a_2859_);
lean_dec_ref(v_original_2858_);
lean_dec(v___x_2857_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(lean_object* v___x_2863_, lean_object* v_edited_2864_, lean_object* v_a_2865_, lean_object* v_inst_2866_, lean_object* v_a_2867_){
_start:
{
lean_object* v___x_2868_; 
v___x_2868_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2863_, v_edited_2864_, v_a_2865_, v_a_2867_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___boxed(lean_object* v___x_2869_, lean_object* v_edited_2870_, lean_object* v_a_2871_, lean_object* v_inst_2872_, lean_object* v_a_2873_){
_start:
{
lean_object* v_res_2874_; 
v_res_2874_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(v___x_2869_, v_edited_2870_, v_a_2871_, v_inst_2872_, v_a_2873_);
lean_dec_ref(v_a_2871_);
lean_dec_ref(v_edited_2870_);
lean_dec(v___x_2869_);
return v_res_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(lean_object* v___x_2875_, lean_object* v_original_2876_, lean_object* v_inst_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v___x_2879_; 
v___x_2879_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2875_, v_original_2876_, v_a_2878_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___boxed(lean_object* v___x_2880_, lean_object* v_original_2881_, lean_object* v_inst_2882_, lean_object* v_a_2883_){
_start:
{
lean_object* v_res_2884_; 
v_res_2884_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(v___x_2880_, v_original_2881_, v_inst_2882_, v_a_2883_);
lean_dec_ref(v_original_2881_);
lean_dec(v___x_2880_);
return v_res_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(lean_object* v___x_2885_, lean_object* v_edited_2886_, lean_object* v_inst_2887_, lean_object* v_a_2888_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2885_, v_edited_2886_, v_a_2888_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___boxed(lean_object* v___x_2890_, lean_object* v_edited_2891_, lean_object* v_inst_2892_, lean_object* v_a_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(v___x_2890_, v_edited_2891_, v_inst_2892_, v_a_2893_);
lean_dec_ref(v_edited_2891_);
lean_dec(v___x_2890_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6(lean_object* v_as_2895_, lean_object* v_as_x27_2896_, lean_object* v_b_2897_, lean_object* v_a_2898_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(v_as_x27_2896_, v_b_2897_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___boxed(lean_object* v_as_2900_, lean_object* v_as_x27_2901_, lean_object* v_b_2902_, lean_object* v_a_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6(v_as_2900_, v_as_x27_2901_, v_b_2902_, v_a_2903_);
lean_dec(v_as_x27_2901_);
lean_dec(v_as_2900_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9(lean_object* v_lsize_2905_, lean_object* v_rsize_2906_, lean_object* v_histogram_2907_, lean_object* v_index_2908_, lean_object* v_val_2909_){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___redArg(v_histogram_2907_, v_index_2908_, v_val_2909_);
return v___x_2910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___boxed(lean_object* v_lsize_2911_, lean_object* v_rsize_2912_, lean_object* v_histogram_2913_, lean_object* v_index_2914_, lean_object* v_val_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9(v_lsize_2911_, v_rsize_2912_, v_histogram_2913_, v_index_2914_, v_val_2915_);
lean_dec(v_rsize_2912_);
lean_dec(v_lsize_2911_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10(lean_object* v_upperBound_2917_, lean_object* v___x_2918_, lean_object* v_fst_2919_, lean_object* v___x_2920_, lean_object* v_inst_2921_, lean_object* v_R_2922_, lean_object* v_a_2923_, lean_object* v_b_2924_, lean_object* v_c_2925_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(v_upperBound_2917_, v___x_2918_, v_fst_2919_, v___x_2920_, v_a_2923_, v_b_2924_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___boxed(lean_object* v_upperBound_2927_, lean_object* v___x_2928_, lean_object* v_fst_2929_, lean_object* v___x_2930_, lean_object* v_inst_2931_, lean_object* v_R_2932_, lean_object* v_a_2933_, lean_object* v_b_2934_, lean_object* v_c_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10(v_upperBound_2927_, v___x_2928_, v_fst_2929_, v___x_2930_, v_inst_2931_, v_R_2932_, v_a_2933_, v_b_2934_, v_c_2935_);
lean_dec(v___x_2930_);
lean_dec_ref(v_fst_2929_);
lean_dec(v___x_2928_);
lean_dec(v_upperBound_2927_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11(lean_object* v_lsize_2937_, lean_object* v_rsize_2938_, lean_object* v_histogram_2939_, lean_object* v_index_2940_, lean_object* v_val_2941_){
_start:
{
lean_object* v___x_2942_; 
v___x_2942_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___redArg(v_histogram_2939_, v_index_2940_, v_val_2941_);
return v___x_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___boxed(lean_object* v_lsize_2943_, lean_object* v_rsize_2944_, lean_object* v_histogram_2945_, lean_object* v_index_2946_, lean_object* v_val_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11(v_lsize_2943_, v_rsize_2944_, v_histogram_2945_, v_index_2946_, v_val_2947_);
lean_dec(v_rsize_2944_);
lean_dec(v_lsize_2943_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12(lean_object* v_upperBound_2949_, lean_object* v_fst_2950_, lean_object* v___x_2951_, lean_object* v_fst_2952_, lean_object* v_inst_2953_, lean_object* v_R_2954_, lean_object* v_a_2955_, lean_object* v_b_2956_, lean_object* v_c_2957_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(v_upperBound_2949_, v_fst_2950_, v___x_2951_, v_fst_2952_, v_a_2955_, v_b_2956_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___boxed(lean_object* v_upperBound_2959_, lean_object* v_fst_2960_, lean_object* v___x_2961_, lean_object* v_fst_2962_, lean_object* v_inst_2963_, lean_object* v_R_2964_, lean_object* v_a_2965_, lean_object* v_b_2966_, lean_object* v_c_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12(v_upperBound_2959_, v_fst_2960_, v___x_2961_, v_fst_2962_, v_inst_2963_, v_R_2964_, v_a_2965_, v_b_2966_, v_c_2967_);
lean_dec_ref(v_fst_2962_);
lean_dec(v___x_2961_);
lean_dec_ref(v_fst_2960_);
lean_dec(v_upperBound_2959_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13(lean_object* v_00_u03b2_2969_, lean_object* v_m_2970_, lean_object* v_a_2971_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_m_2970_, v_a_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___boxed(lean_object* v_00_u03b2_2973_, lean_object* v_m_2974_, lean_object* v_a_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13(v_00_u03b2_2973_, v_m_2974_, v_a_2975_);
lean_dec_ref(v_a_2975_);
lean_dec_ref(v_m_2974_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_2977_, lean_object* v_m_2978_, lean_object* v_a_2979_, lean_object* v_b_2980_){
_start:
{
lean_object* v___x_2981_; 
v___x_2981_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_m_2978_, v_a_2979_, v_b_2980_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14(lean_object* v_inst_2982_, lean_object* v_R_2983_, lean_object* v_a_2984_, lean_object* v_b_2985_){
_start:
{
lean_object* v___x_2986_; 
v___x_2986_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(v_a_2984_, v_b_2985_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20(lean_object* v_00_u03b2_2987_, lean_object* v_a_2988_, lean_object* v_x_2989_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(v_a_2988_, v_x_2989_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___boxed(lean_object* v_00_u03b2_2991_, lean_object* v_a_2992_, lean_object* v_x_2993_){
_start:
{
lean_object* v_res_2994_; 
v_res_2994_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20(v_00_u03b2_2991_, v_a_2992_, v_x_2993_);
lean_dec(v_x_2993_);
lean_dec_ref(v_a_2992_);
return v_res_2994_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22(lean_object* v_00_u03b2_2995_, lean_object* v_a_2996_, lean_object* v_x_2997_){
_start:
{
uint8_t v___x_2998_; 
v___x_2998_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(v_a_2996_, v_x_2997_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___boxed(lean_object* v_00_u03b2_2999_, lean_object* v_a_3000_, lean_object* v_x_3001_){
_start:
{
uint8_t v_res_3002_; lean_object* v_r_3003_; 
v_res_3002_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22(v_00_u03b2_2999_, v_a_3000_, v_x_3001_);
lean_dec(v_x_3001_);
lean_dec_ref(v_a_3000_);
v_r_3003_ = lean_box(v_res_3002_);
return v_r_3003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23(lean_object* v_00_u03b2_3004_, lean_object* v_data_3005_){
_start:
{
lean_object* v___x_3006_; 
v___x_3006_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23___redArg(v_data_3005_);
return v___x_3006_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24(lean_object* v_00_u03b2_3007_, lean_object* v_a_3008_, lean_object* v_b_3009_, lean_object* v_x_3010_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(v_a_3008_, v_b_3009_, v_x_3010_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28(lean_object* v_00_u03b2_3012_, lean_object* v_i_3013_, lean_object* v_source_3014_, lean_object* v_target_3015_){
_start:
{
lean_object* v___x_3016_; 
v___x_3016_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28___redArg(v_i_3013_, v_source_3014_, v_target_3015_);
return v___x_3016_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_3017_, lean_object* v_x_3018_, lean_object* v_x_3019_){
_start:
{
lean_object* v___x_3020_; 
v___x_3020_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29___redArg(v_x_3018_, v_x_3019_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(lean_object* v_s_3021_){
_start:
{
lean_object* v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = lean_string_data(v_s_3021_);
v___x_3023_ = lean_array_mk(v___x_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(lean_object* v_s_3024_, lean_object* v_s_x27_3025_){
_start:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3026_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3024_);
v___x_3027_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3025_);
v___x_3028_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3026_, v___x_3027_);
v___x_3029_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_3028_);
lean_dec_ref(v___x_3028_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(lean_object* v_s_3030_, lean_object* v_s_x27_3031_){
_start:
{
uint8_t v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; uint8_t v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3032_ = 1;
v___x_3033_ = lean_box(v___x_3032_);
v___x_3034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3034_, 0, v___x_3033_);
lean_ctor_set(v___x_3034_, 1, v_s_3030_);
v___x_3035_ = 0;
v___x_3036_ = lean_box(v___x_3035_);
v___x_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
lean_ctor_set(v___x_3037_, 1, v_s_x27_3031_);
v___x_3038_ = lean_unsigned_to_nat(2u);
v___x_3039_ = lean_mk_empty_array_with_capacity(v___x_3038_);
v___x_3040_ = lean_array_push(v___x_3039_, v___x_3034_);
v___x_3041_ = lean_array_push(v___x_3040_, v___x_3037_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(lean_object* v_as_3042_, size_t v_i_3043_, size_t v_stop_3044_, lean_object* v_b_3045_){
_start:
{
lean_object* v___y_3047_; uint8_t v___x_3051_; 
v___x_3051_ = lean_usize_dec_eq(v_i_3043_, v_stop_3044_);
if (v___x_3051_ == 0)
{
lean_object* v___x_3052_; lean_object* v_fst_3053_; uint8_t v___x_3054_; uint8_t v___x_3055_; uint8_t v___x_3056_; 
v___x_3052_ = lean_array_uget_borrowed(v_as_3042_, v_i_3043_);
v_fst_3053_ = lean_ctor_get(v___x_3052_, 0);
v___x_3054_ = 2;
v___x_3055_ = lean_unbox(v_fst_3053_);
v___x_3056_ = l_Lean_Diff_instBEqAction_beq(v___x_3055_, v___x_3054_);
if (v___x_3056_ == 0)
{
lean_object* v___x_3057_; 
lean_inc(v___x_3052_);
v___x_3057_ = lean_array_push(v_b_3045_, v___x_3052_);
v___y_3047_ = v___x_3057_;
goto v___jp_3046_;
}
else
{
v___y_3047_ = v_b_3045_;
goto v___jp_3046_;
}
}
else
{
return v_b_3045_;
}
v___jp_3046_:
{
size_t v___x_3048_; size_t v___x_3049_; 
v___x_3048_ = ((size_t)1ULL);
v___x_3049_ = lean_usize_add(v_i_3043_, v___x_3048_);
v_i_3043_ = v___x_3049_;
v_b_3045_ = v___y_3047_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0___boxed(lean_object* v_as_3058_, lean_object* v_i_3059_, lean_object* v_stop_3060_, lean_object* v_b_3061_){
_start:
{
size_t v_i_boxed_3062_; size_t v_stop_boxed_3063_; lean_object* v_res_3064_; 
v_i_boxed_3062_ = lean_unbox_usize(v_i_3059_);
lean_dec(v_i_3059_);
v_stop_boxed_3063_ = lean_unbox_usize(v_stop_3060_);
lean_dec(v_stop_3060_);
v_res_3064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_as_3058_, v_i_boxed_3062_, v_stop_boxed_3063_, v_b_3061_);
lean_dec_ref(v_as_3058_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff(lean_object* v_s_3065_, lean_object* v_s_x27_3066_, uint8_t v_granularity_3067_){
_start:
{
lean_object* v___y_3069_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3088_; lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; 
switch(v_granularity_3067_)
{
case 0:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___y_3111_; uint8_t v___x_3117_; 
v___x_3108_ = lean_string_length(v_s_3065_);
v___x_3109_ = lean_string_length(v_s_x27_3066_);
v___x_3117_ = lean_nat_dec_le(v___x_3108_, v___x_3109_);
if (v___x_3117_ == 0)
{
v___y_3111_ = v___x_3109_;
goto v___jp_3110_;
}
else
{
v___y_3111_ = v___x_3108_;
goto v___jp_3110_;
}
v___jp_3110_:
{
lean_object* v___x_3112_; lean_object* v_maxCharDiffDistance_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; uint8_t v___x_3116_; 
v___x_3112_ = lean_unsigned_to_nat(5u);
v_maxCharDiffDistance_3113_ = lean_nat_div(v___y_3111_, v___x_3112_);
v___x_3114_ = lean_unsigned_to_nat(1u);
v___x_3115_ = lean_nat_shiftr(v___y_3111_, v___x_3114_);
lean_dec(v___y_3111_);
v___x_3116_ = lean_nat_dec_le(v___x_3108_, v___x_3109_);
if (v___x_3116_ == 0)
{
v___y_3088_ = v___x_3114_;
v___y_3089_ = v___x_3115_;
v___y_3090_ = v_maxCharDiffDistance_3113_;
v___y_3091_ = v___x_3108_;
goto v___jp_3087_;
}
else
{
v___y_3088_ = v___x_3114_;
v___y_3089_ = v___x_3115_;
v___y_3090_ = v_maxCharDiffDistance_3113_;
v___y_3091_ = v___x_3109_;
goto v___jp_3087_;
}
}
}
case 1:
{
lean_object* v___x_3118_; 
v___x_3118_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(v_s_3065_, v_s_x27_3066_);
return v___x_3118_;
}
case 2:
{
lean_object* v___x_3119_; 
v___x_3119_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3065_, v_s_x27_3066_);
lean_dec_ref(v_s_x27_3066_);
lean_dec_ref(v_s_3065_);
return v___x_3119_;
}
case 3:
{
lean_object* v___x_3120_; 
v___x_3120_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3065_, v_s_x27_3066_);
return v___x_3120_;
}
default: 
{
uint8_t v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; 
lean_dec_ref(v_s_3065_);
v___x_3121_ = 0;
v___x_3122_ = lean_box(v___x_3121_);
v___x_3123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3123_, 0, v___x_3122_);
lean_ctor_set(v___x_3123_, 1, v_s_x27_3066_);
v___x_3124_ = lean_unsigned_to_nat(1u);
v___x_3125_ = lean_mk_empty_array_with_capacity(v___x_3124_);
v___x_3126_ = lean_array_push(v___x_3125_, v___x_3123_);
return v___x_3126_;
}
}
v___jp_3068_:
{
size_t v_sz_3070_; size_t v___x_3071_; lean_object* v___x_3072_; 
v_sz_3070_ = lean_array_size(v___y_3069_);
v___x_3071_ = ((size_t)0ULL);
v___x_3072_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_3070_, v___x_3071_, v___y_3069_);
return v___x_3072_;
}
v___jp_3073_:
{
lean_object* v_charArrDiff_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; uint8_t v___x_3081_; 
v_charArrDiff_3078_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v___y_3074_);
lean_dec_ref(v___y_3074_);
v___x_3079_ = lean_array_get_size(v_charArrDiff_3078_);
v___x_3080_ = lean_unsigned_to_nat(3u);
v___x_3081_ = lean_nat_dec_le(v___x_3079_, v___x_3080_);
if (v___x_3081_ == 0)
{
lean_object* v_approxEditDistance_3082_; uint8_t v___x_3083_; 
v_approxEditDistance_3082_ = lean_array_get_size(v___y_3077_);
lean_dec_ref(v___y_3077_);
v___x_3083_ = lean_nat_dec_le(v_approxEditDistance_3082_, v___y_3075_);
lean_dec(v___y_3075_);
if (v___x_3083_ == 0)
{
uint8_t v___x_3084_; 
lean_dec_ref(v_charArrDiff_3078_);
v___x_3084_ = lean_nat_dec_le(v_approxEditDistance_3082_, v___y_3076_);
lean_dec(v___y_3076_);
if (v___x_3084_ == 0)
{
lean_object* v___x_3085_; 
v___x_3085_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3065_, v_s_x27_3066_);
return v___x_3085_;
}
else
{
lean_object* v___x_3086_; 
v___x_3086_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3065_, v_s_x27_3066_);
lean_dec_ref(v_s_x27_3066_);
lean_dec_ref(v_s_3065_);
return v___x_3086_;
}
}
else
{
lean_dec(v___y_3076_);
lean_dec_ref(v_s_x27_3066_);
lean_dec_ref(v_s_3065_);
v___y_3069_ = v_charArrDiff_3078_;
goto v___jp_3068_;
}
}
else
{
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v_s_x27_3066_);
lean_dec_ref(v_s_3065_);
v___y_3069_ = v_charArrDiff_3078_;
goto v___jp_3068_;
}
}
v___jp_3087_:
{
lean_object* v___x_3092_; lean_object* v_maxWordDiffDistance_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v_charDiffRaw_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; uint8_t v___x_3100_; 
v___x_3092_ = lean_nat_shiftr(v___y_3091_, v___y_3088_);
lean_dec(v___y_3091_);
v_maxWordDiffDistance_3093_ = lean_nat_add(v___y_3089_, v___x_3092_);
lean_dec(v___x_3092_);
lean_dec(v___y_3089_);
lean_inc_ref(v_s_3065_);
v___x_3094_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3065_);
lean_inc_ref(v_s_x27_3066_);
v___x_3095_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3066_);
v_charDiffRaw_3096_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3094_, v___x_3095_);
v___x_3097_ = lean_unsigned_to_nat(0u);
v___x_3098_ = lean_array_get_size(v_charDiffRaw_3096_);
v___x_3099_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0));
v___x_3100_ = lean_nat_dec_lt(v___x_3097_, v___x_3098_);
if (v___x_3100_ == 0)
{
v___y_3074_ = v_charDiffRaw_3096_;
v___y_3075_ = v___y_3090_;
v___y_3076_ = v_maxWordDiffDistance_3093_;
v___y_3077_ = v___x_3099_;
goto v___jp_3073_;
}
else
{
uint8_t v___x_3101_; 
v___x_3101_ = lean_nat_dec_le(v___x_3098_, v___x_3098_);
if (v___x_3101_ == 0)
{
if (v___x_3100_ == 0)
{
v___y_3074_ = v_charDiffRaw_3096_;
v___y_3075_ = v___y_3090_;
v___y_3076_ = v_maxWordDiffDistance_3093_;
v___y_3077_ = v___x_3099_;
goto v___jp_3073_;
}
else
{
size_t v___x_3102_; size_t v___x_3103_; lean_object* v___x_3104_; 
v___x_3102_ = ((size_t)0ULL);
v___x_3103_ = lean_usize_of_nat(v___x_3098_);
v___x_3104_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3096_, v___x_3102_, v___x_3103_, v___x_3099_);
v___y_3074_ = v_charDiffRaw_3096_;
v___y_3075_ = v___y_3090_;
v___y_3076_ = v_maxWordDiffDistance_3093_;
v___y_3077_ = v___x_3104_;
goto v___jp_3073_;
}
}
else
{
size_t v___x_3105_; size_t v___x_3106_; lean_object* v___x_3107_; 
v___x_3105_ = ((size_t)0ULL);
v___x_3106_ = lean_usize_of_nat(v___x_3098_);
v___x_3107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3096_, v___x_3105_, v___x_3106_, v___x_3099_);
v___y_3074_ = v_charDiffRaw_3096_;
v___y_3075_ = v___y_3090_;
v___y_3076_ = v_maxWordDiffDistance_3093_;
v___y_3077_ = v___x_3107_;
goto v___jp_3073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff___boxed(lean_object* v_s_3127_, lean_object* v_s_x27_3128_, lean_object* v_granularity_3129_){
_start:
{
uint8_t v_granularity_boxed_3130_; lean_object* v_res_3131_; 
v_granularity_boxed_3130_ = lean_unbox(v_granularity_3129_);
v_res_3131_ = l_Lean_Meta_Hint_readableDiff(v_s_3127_, v_s_x27_3128_, v_granularity_boxed_3130_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(lean_object* v_as_3132_, size_t v_i_3133_, size_t v_stop_3134_, lean_object* v_b_3135_){
_start:
{
uint8_t v___x_3136_; 
v___x_3136_ = lean_usize_dec_eq(v_i_3133_, v_stop_3134_);
if (v___x_3136_ == 0)
{
lean_object* v___x_3137_; lean_object* v_snd_3138_; lean_object* v___x_3139_; size_t v___x_3140_; size_t v___x_3141_; 
v___x_3137_ = lean_array_uget_borrowed(v_as_3132_, v_i_3133_);
v_snd_3138_ = lean_ctor_get(v___x_3137_, 1);
v___x_3139_ = lean_string_append(v_b_3135_, v_snd_3138_);
v___x_3140_ = ((size_t)1ULL);
v___x_3141_ = lean_usize_add(v_i_3133_, v___x_3140_);
v_i_3133_ = v___x_3141_;
v_b_3135_ = v___x_3139_;
goto _start;
}
else
{
return v_b_3135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0___boxed(lean_object* v_as_3143_, lean_object* v_i_3144_, lean_object* v_stop_3145_, lean_object* v_b_3146_){
_start:
{
size_t v_i_boxed_3147_; size_t v_stop_boxed_3148_; lean_object* v_res_3149_; 
v_i_boxed_3147_ = lean_unbox_usize(v_i_3144_);
lean_dec(v_i_3144_);
v_stop_boxed_3148_ = lean_unbox_usize(v_stop_3145_);
lean_dec(v_stop_3145_);
v_res_3149_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v_as_3143_, v_i_boxed_3147_, v_stop_boxed_3148_, v_b_3146_);
lean_dec_ref(v_as_3143_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(lean_object* v_t_3150_, lean_object* v___y_3151_){
_start:
{
lean_object* v___x_3153_; lean_object* v_infoState_3154_; uint8_t v_enabled_3155_; 
v___x_3153_ = lean_st_ref_get(v___y_3151_);
v_infoState_3154_ = lean_ctor_get(v___x_3153_, 7);
lean_inc_ref(v_infoState_3154_);
lean_dec(v___x_3153_);
v_enabled_3155_ = lean_ctor_get_uint8(v_infoState_3154_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3154_);
if (v_enabled_3155_ == 0)
{
lean_object* v___x_3156_; lean_object* v___x_3157_; 
lean_dec_ref(v_t_3150_);
v___x_3156_ = lean_box(0);
v___x_3157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3157_, 0, v___x_3156_);
return v___x_3157_;
}
else
{
lean_object* v___x_3158_; lean_object* v_infoState_3159_; lean_object* v_env_3160_; lean_object* v_nextMacroScope_3161_; lean_object* v_ngen_3162_; lean_object* v_auxDeclNGen_3163_; lean_object* v_traceState_3164_; lean_object* v_cache_3165_; lean_object* v_messages_3166_; lean_object* v_snapshotTasks_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3189_; 
v___x_3158_ = lean_st_ref_take(v___y_3151_);
v_infoState_3159_ = lean_ctor_get(v___x_3158_, 7);
v_env_3160_ = lean_ctor_get(v___x_3158_, 0);
v_nextMacroScope_3161_ = lean_ctor_get(v___x_3158_, 1);
v_ngen_3162_ = lean_ctor_get(v___x_3158_, 2);
v_auxDeclNGen_3163_ = lean_ctor_get(v___x_3158_, 3);
v_traceState_3164_ = lean_ctor_get(v___x_3158_, 4);
v_cache_3165_ = lean_ctor_get(v___x_3158_, 5);
v_messages_3166_ = lean_ctor_get(v___x_3158_, 6);
v_snapshotTasks_3167_ = lean_ctor_get(v___x_3158_, 8);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3169_ = v___x_3158_;
v_isShared_3170_ = v_isSharedCheck_3189_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_snapshotTasks_3167_);
lean_inc(v_infoState_3159_);
lean_inc(v_messages_3166_);
lean_inc(v_cache_3165_);
lean_inc(v_traceState_3164_);
lean_inc(v_auxDeclNGen_3163_);
lean_inc(v_ngen_3162_);
lean_inc(v_nextMacroScope_3161_);
lean_inc(v_env_3160_);
lean_dec(v___x_3158_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3189_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
uint8_t v_enabled_3171_; lean_object* v_assignment_3172_; lean_object* v_lazyAssignment_3173_; lean_object* v_trees_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3188_; 
v_enabled_3171_ = lean_ctor_get_uint8(v_infoState_3159_, sizeof(void*)*3);
v_assignment_3172_ = lean_ctor_get(v_infoState_3159_, 0);
v_lazyAssignment_3173_ = lean_ctor_get(v_infoState_3159_, 1);
v_trees_3174_ = lean_ctor_get(v_infoState_3159_, 2);
v_isSharedCheck_3188_ = !lean_is_exclusive(v_infoState_3159_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3176_ = v_infoState_3159_;
v_isShared_3177_ = v_isSharedCheck_3188_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_trees_3174_);
lean_inc(v_lazyAssignment_3173_);
lean_inc(v_assignment_3172_);
lean_dec(v_infoState_3159_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3188_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3178_; lean_object* v___x_3180_; 
v___x_3178_ = l_Lean_PersistentArray_push___redArg(v_trees_3174_, v_t_3150_);
if (v_isShared_3177_ == 0)
{
lean_ctor_set(v___x_3176_, 2, v___x_3178_);
v___x_3180_ = v___x_3176_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_assignment_3172_);
lean_ctor_set(v_reuseFailAlloc_3187_, 1, v_lazyAssignment_3173_);
lean_ctor_set(v_reuseFailAlloc_3187_, 2, v___x_3178_);
lean_ctor_set_uint8(v_reuseFailAlloc_3187_, sizeof(void*)*3, v_enabled_3171_);
v___x_3180_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
lean_object* v___x_3182_; 
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 7, v___x_3180_);
v___x_3182_ = v___x_3169_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_env_3160_);
lean_ctor_set(v_reuseFailAlloc_3186_, 1, v_nextMacroScope_3161_);
lean_ctor_set(v_reuseFailAlloc_3186_, 2, v_ngen_3162_);
lean_ctor_set(v_reuseFailAlloc_3186_, 3, v_auxDeclNGen_3163_);
lean_ctor_set(v_reuseFailAlloc_3186_, 4, v_traceState_3164_);
lean_ctor_set(v_reuseFailAlloc_3186_, 5, v_cache_3165_);
lean_ctor_set(v_reuseFailAlloc_3186_, 6, v_messages_3166_);
lean_ctor_set(v_reuseFailAlloc_3186_, 7, v___x_3180_);
lean_ctor_set(v_reuseFailAlloc_3186_, 8, v_snapshotTasks_3167_);
v___x_3182_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3183_ = lean_st_ref_put(v___y_3151_, v___x_3182_);
v___x_3184_ = lean_box(0);
v___x_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3185_, 0, v___x_3184_);
return v___x_3185_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg___boxed(lean_object* v_t_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3190_, v___y_3191_);
lean_dec(v___y_3191_);
return v_res_3193_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3194_ = lean_unsigned_to_nat(32u);
v___x_3195_ = lean_mk_empty_array_with_capacity(v___x_3194_);
v___x_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3195_);
return v___x_3196_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1(void){
_start:
{
size_t v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3197_ = ((size_t)5ULL);
v___x_3198_ = lean_unsigned_to_nat(0u);
v___x_3199_ = lean_unsigned_to_nat(32u);
v___x_3200_ = lean_mk_empty_array_with_capacity(v___x_3199_);
v___x_3201_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0);
v___x_3202_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3202_, 0, v___x_3201_);
lean_ctor_set(v___x_3202_, 1, v___x_3200_);
lean_ctor_set(v___x_3202_, 2, v___x_3198_);
lean_ctor_set(v___x_3202_, 3, v___x_3198_);
lean_ctor_set_usize(v___x_3202_, 4, v___x_3197_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(lean_object* v_t_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_){
_start:
{
lean_object* v___x_3207_; lean_object* v_infoState_3208_; uint8_t v_enabled_3209_; 
v___x_3207_ = lean_st_ref_get(v___y_3205_);
v_infoState_3208_ = lean_ctor_get(v___x_3207_, 7);
lean_inc_ref(v_infoState_3208_);
lean_dec(v___x_3207_);
v_enabled_3209_ = lean_ctor_get_uint8(v_infoState_3208_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3208_);
if (v_enabled_3209_ == 0)
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
lean_dec_ref(v_t_3203_);
v___x_3210_ = lean_box(0);
v___x_3211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3211_, 0, v___x_3210_);
return v___x_3211_;
}
else
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3212_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1);
v___x_3213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3213_, 0, v_t_3203_);
lean_ctor_set(v___x_3213_, 1, v___x_3212_);
v___x_3214_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v___x_3213_, v___y_3205_);
return v___x_3214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___boxed(lean_object* v_t_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v_res_3219_; 
v_res_3219_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v_t_3215_, v___y_3216_, v___y_3217_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0(lean_object* v___x_3220_, lean_object* v___y_3221_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3222_, 0, v___x_3220_);
lean_ctor_set(v___x_3222_, 1, v___y_3221_);
return v___x_3222_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__0));
v___x_3225_ = l_Lean_stringToMessageData(v___x_3224_);
return v___x_3225_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__2));
v___x_3228_ = l_Lean_stringToMessageData(v___x_3227_);
return v___x_3228_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29(void){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3277_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__28));
v___x_3278_ = l_Lean_Json_mkObj(v___x_3277_);
return v___x_3278_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30(void){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3279_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29);
v___x_3280_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__19));
v___x_3281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
lean_ctor_set(v___x_3281_, 1, v___x_3279_);
return v___x_3281_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31(void){
_start:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3282_ = lean_box(0);
v___x_3283_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30);
v___x_3284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3283_);
lean_ctor_set(v___x_3284_, 1, v___x_3282_);
return v___x_3284_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33(void){
_start:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; 
v___x_3287_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__32));
v___x_3288_ = l_Lean_MessageData_ofFormat(v___x_3287_);
return v___x_3288_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35(void){
_start:
{
lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3290_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__34));
v___x_3291_ = l_Lean_stringToMessageData(v___x_3290_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(lean_object* v_suggestions_3293_, uint8_t v_forceList_3294_, lean_object* v_codeActionPrefix_x3f_3295_, lean_object* v_ref_3296_, lean_object* v_as_3297_, size_t v_sz_3298_, size_t v_i_3299_, lean_object* v_b_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_){
_start:
{
lean_object* v_a_3305_; lean_object* v___y_3310_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3321_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; uint8_t v___x_3349_; 
v___x_3349_ = lean_usize_dec_lt(v_i_3299_, v_sz_3298_);
if (v___x_3349_ == 0)
{
lean_object* v___x_3350_; 
lean_dec(v_ref_3296_);
lean_dec(v_codeActionPrefix_x3f_3295_);
v___x_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3350_, 0, v_b_3300_);
return v___x_3350_;
}
else
{
lean_object* v_a_3351_; lean_object* v_span_x3f_3352_; lean_object* v___x_3353_; lean_object* v___y_3355_; lean_object* v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; uint8_t v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; uint8_t v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; uint8_t v___y_3441_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; uint8_t v___y_3447_; uint8_t v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v_postInfo_x3f_3456_; uint8_t v___y_3457_; lean_object* v___y_3458_; uint8_t v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3465_; lean_object* v___y_3466_; uint8_t v___y_3467_; uint8_t v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v_edits_3471_; lean_object* v___y_3477_; lean_object* v___y_3478_; uint8_t v___y_3479_; lean_object* v___y_3480_; lean_object* v_stop_3481_; lean_object* v___y_3482_; uint8_t v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v_edits_3486_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; uint8_t v___y_3502_; lean_object* v___y_3503_; uint8_t v___y_3504_; lean_object* v___y_3505_; lean_object* v_edits_3506_; lean_object* v___y_3507_; lean_object* v___x_3533_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; uint8_t v___y_3538_; lean_object* v___y_3539_; uint8_t v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; uint8_t v___y_3584_; lean_object* v___y_3585_; uint8_t v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___y_3599_; 
v_a_3351_ = lean_array_uget_borrowed(v_as_3297_, v_i_3299_);
v_span_x3f_3352_ = lean_ctor_get(v_a_3351_, 1);
v___x_3353_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_3533_ = l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_;
if (lean_obj_tag(v_span_x3f_3352_) == 0)
{
lean_inc(v_ref_3296_);
v___y_3599_ = v_ref_3296_;
goto v___jp_3598_;
}
else
{
lean_object* v_val_3620_; 
v_val_3620_ = lean_ctor_get(v_span_x3f_3352_, 0);
lean_inc(v_val_3620_);
v___y_3599_ = v_val_3620_;
goto v___jp_3598_;
}
v___jp_3354_:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___f_3375_; 
lean_inc_ref(v___y_3360_);
v___x_3361_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson(v___y_3360_);
v___x_3362_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__9));
v___x_3363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3362_);
lean_ctor_set(v___x_3363_, 1, v___x_3361_);
v___x_3364_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3365_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3365_, 0, v___y_3358_);
v___x_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3364_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
v___x_3367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3368_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3355_);
v___x_3369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3367_);
lean_ctor_set(v___x_3369_, 1, v___x_3368_);
v___x_3370_ = lean_box(0);
v___x_3371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3369_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
v___x_3372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3366_);
lean_ctor_set(v___x_3372_, 1, v___x_3371_);
v___x_3373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3363_);
lean_ctor_set(v___x_3373_, 1, v___x_3372_);
v___x_3374_ = l_Lean_Json_mkObj(v___x_3373_);
lean_dec_ref_known(v___x_3373_, 2);
v___f_3375_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3375_, 0, v___x_3374_);
if (v___y_3359_ == 0)
{
lean_object* v___x_3376_; 
v___x_3376_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString(v___y_3360_);
v___y_3329_ = v___y_3356_;
v___y_3330_ = v___f_3375_;
v___y_3331_ = v___y_3357_;
v___y_3332_ = v___x_3376_;
goto v___jp_3328_;
}
else
{
lean_object* v___x_3377_; lean_object* v___x_3378_; uint8_t v___x_3379_; 
v___x_3377_ = lean_unsigned_to_nat(0u);
v___x_3378_ = lean_array_get_size(v___y_3360_);
v___x_3379_ = lean_nat_dec_lt(v___x_3377_, v___x_3378_);
if (v___x_3379_ == 0)
{
lean_dec_ref(v___y_3360_);
v___y_3329_ = v___y_3356_;
v___y_3330_ = v___f_3375_;
v___y_3331_ = v___y_3357_;
v___y_3332_ = v___x_3353_;
goto v___jp_3328_;
}
else
{
uint8_t v___x_3380_; 
v___x_3380_ = lean_nat_dec_le(v___x_3378_, v___x_3378_);
if (v___x_3380_ == 0)
{
if (v___x_3379_ == 0)
{
lean_dec_ref(v___y_3360_);
v___y_3329_ = v___y_3356_;
v___y_3330_ = v___f_3375_;
v___y_3331_ = v___y_3357_;
v___y_3332_ = v___x_3353_;
goto v___jp_3328_;
}
else
{
size_t v___x_3381_; size_t v___x_3382_; lean_object* v___x_3383_; 
v___x_3381_ = ((size_t)0ULL);
v___x_3382_ = lean_usize_of_nat(v___x_3378_);
v___x_3383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3360_, v___x_3381_, v___x_3382_, v___x_3353_);
lean_dec_ref(v___y_3360_);
v___y_3329_ = v___y_3356_;
v___y_3330_ = v___f_3375_;
v___y_3331_ = v___y_3357_;
v___y_3332_ = v___x_3383_;
goto v___jp_3328_;
}
}
else
{
size_t v___x_3384_; size_t v___x_3385_; lean_object* v___x_3386_; 
v___x_3384_ = ((size_t)0ULL);
v___x_3385_ = lean_usize_of_nat(v___x_3378_);
v___x_3386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3360_, v___x_3384_, v___x_3385_, v___x_3353_);
lean_dec_ref(v___y_3360_);
v___y_3329_ = v___y_3356_;
v___y_3330_ = v___f_3375_;
v___y_3331_ = v___y_3357_;
v___y_3332_ = v___x_3386_;
goto v___jp_3328_;
}
}
}
}
v___jp_3387_:
{
if (lean_obj_tag(v___y_3395_) == 0)
{
lean_object* v___x_3396_; uint64_t v_javascriptHash_3397_; lean_object* v_suggestion_3398_; lean_object* v_messageData_x3f_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___f_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; 
lean_dec_ref(v___y_3393_);
v___x_3396_ = l_Lean_Meta_Hint_textInsertionWidget;
v_javascriptHash_3397_ = lean_ctor_get_uint64(v___x_3396_, sizeof(void*)*1);
v_suggestion_3398_ = lean_ctor_get(v___y_3389_, 0);
lean_inc_ref(v_suggestion_3398_);
v_messageData_x3f_3399_ = lean_ctor_get(v___y_3389_, 4);
lean_inc(v_messageData_x3f_3399_);
lean_dec_ref(v___y_3389_);
v___x_3400_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18));
v___x_3401_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3402_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3388_);
v___x_3403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3403_, 0, v___x_3401_);
lean_ctor_set(v___x_3403_, 1, v___x_3402_);
v___x_3404_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3405_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3405_, 0, v___y_3392_);
v___x_3406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3404_);
lean_ctor_set(v___x_3406_, 1, v___x_3405_);
v___x_3407_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31);
v___x_3408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3406_);
lean_ctor_set(v___x_3408_, 1, v___x_3407_);
v___x_3409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3403_);
lean_ctor_set(v___x_3409_, 1, v___x_3408_);
v___x_3410_ = l_Lean_Json_mkObj(v___x_3409_);
lean_dec_ref_known(v___x_3409_, 2);
v___f_3411_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3411_, 0, v___x_3410_);
v___x_3412_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3412_, 0, v___x_3400_);
lean_ctor_set(v___x_3412_, 1, v___f_3411_);
lean_ctor_set_uint64(v___x_3412_, sizeof(void*)*2, v_javascriptHash_3397_);
v___x_3413_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33);
v___x_3414_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3412_);
lean_ctor_set(v___x_3414_, 1, v___x_3413_);
v___x_3415_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3415_);
lean_ctor_set(v___x_3416_, 1, v___x_3414_);
v___x_3417_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35);
v___x_3418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3416_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
v___x_3419_ = l_Lean_stringToMessageData(v___y_3390_);
v___x_3420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3418_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
if (lean_obj_tag(v_messageData_x3f_3399_) == 0)
{
if (lean_obj_tag(v_suggestion_3398_) == 0)
{
lean_object* v_a_3421_; lean_object* v___x_3422_; 
v_a_3421_ = lean_ctor_get(v_suggestion_3398_, 1);
lean_inc(v_a_3421_);
lean_dec_ref_known(v_suggestion_3398_, 2);
v___x_3422_ = l_Lean_MessageData_ofSyntax(v_a_3421_);
v___y_3314_ = v___y_3391_;
v___y_3315_ = v___x_3420_;
v___y_3316_ = v___x_3422_;
goto v___jp_3313_;
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3431_; 
v_a_3423_ = lean_ctor_get(v_suggestion_3398_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v_suggestion_3398_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3425_ = v_suggestion_3398_;
v_isShared_3426_ = v_isSharedCheck_3431_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v_suggestion_3398_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3431_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
lean_ctor_set_tag(v___x_3425_, 3);
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
lean_object* v___x_3429_; 
v___x_3429_ = l_Lean_MessageData_ofFormat(v___x_3428_);
v___y_3314_ = v___y_3391_;
v___y_3315_ = v___x_3420_;
v___y_3316_ = v___x_3429_;
goto v___jp_3313_;
}
}
}
}
else
{
lean_object* v_val_3432_; 
lean_dec_ref(v_suggestion_3398_);
v_val_3432_ = lean_ctor_get(v_messageData_x3f_3399_, 0);
lean_inc(v_val_3432_);
lean_dec_ref_known(v_messageData_x3f_3399_, 1);
v___y_3314_ = v___y_3391_;
v___y_3315_ = v___x_3420_;
v___y_3316_ = v_val_3432_;
goto v___jp_3313_;
}
}
else
{
lean_dec_ref_known(v___y_3395_, 1);
lean_dec_ref(v___y_3389_);
v___y_3355_ = v___y_3388_;
v___y_3356_ = v___y_3390_;
v___y_3357_ = v___y_3391_;
v___y_3358_ = v___y_3392_;
v___y_3359_ = v___y_3394_;
v___y_3360_ = v___y_3393_;
goto v___jp_3354_;
}
}
v___jp_3433_:
{
if (v___y_3441_ == 0)
{
lean_object* v_messageData_x3f_3442_; 
v_messageData_x3f_3442_ = lean_ctor_get(v___y_3435_, 4);
if (lean_obj_tag(v_messageData_x3f_3442_) == 0)
{
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3435_);
v___y_3355_ = v___y_3434_;
v___y_3356_ = v___y_3436_;
v___y_3357_ = v___y_3437_;
v___y_3358_ = v___y_3438_;
v___y_3359_ = v___y_3441_;
v___y_3360_ = v___y_3439_;
goto v___jp_3354_;
}
else
{
v___y_3388_ = v___y_3434_;
v___y_3389_ = v___y_3435_;
v___y_3390_ = v___y_3436_;
v___y_3391_ = v___y_3437_;
v___y_3392_ = v___y_3438_;
v___y_3393_ = v___y_3439_;
v___y_3394_ = v___y_3441_;
v___y_3395_ = v___y_3440_;
goto v___jp_3387_;
}
}
else
{
v___y_3388_ = v___y_3434_;
v___y_3389_ = v___y_3435_;
v___y_3390_ = v___y_3436_;
v___y_3391_ = v___y_3437_;
v___y_3392_ = v___y_3438_;
v___y_3393_ = v___y_3439_;
v___y_3394_ = v___y_3441_;
v___y_3395_ = v___y_3440_;
goto v___jp_3387_;
}
}
v___jp_3443_:
{
if (v___y_3448_ == 4)
{
v___y_3434_ = v___y_3444_;
v___y_3435_ = v___y_3446_;
v___y_3436_ = v___y_3445_;
v___y_3437_ = v___y_3452_;
v___y_3438_ = v___y_3449_;
v___y_3439_ = v___y_3450_;
v___y_3440_ = v___y_3451_;
v___y_3441_ = v___x_3349_;
goto v___jp_3433_;
}
else
{
v___y_3434_ = v___y_3444_;
v___y_3435_ = v___y_3446_;
v___y_3436_ = v___y_3445_;
v___y_3437_ = v___y_3452_;
v___y_3438_ = v___y_3449_;
v___y_3439_ = v___y_3450_;
v___y_3440_ = v___y_3451_;
v___y_3441_ = v___y_3447_;
goto v___jp_3433_;
}
}
v___jp_3453_:
{
if (lean_obj_tag(v_postInfo_x3f_3456_) == 0)
{
v___y_3444_ = v___y_3454_;
v___y_3445_ = v___y_3462_;
v___y_3446_ = v___y_3455_;
v___y_3447_ = v___y_3457_;
v___y_3448_ = v___y_3459_;
v___y_3449_ = v___y_3458_;
v___y_3450_ = v___y_3460_;
v___y_3451_ = v___y_3461_;
v___y_3452_ = v___x_3353_;
goto v___jp_3443_;
}
else
{
lean_object* v_val_3463_; 
v_val_3463_ = lean_ctor_get(v_postInfo_x3f_3456_, 0);
lean_inc(v_val_3463_);
lean_dec_ref_known(v_postInfo_x3f_3456_, 1);
v___y_3444_ = v___y_3454_;
v___y_3445_ = v___y_3462_;
v___y_3446_ = v___y_3455_;
v___y_3447_ = v___y_3457_;
v___y_3448_ = v___y_3459_;
v___y_3449_ = v___y_3458_;
v___y_3450_ = v___y_3460_;
v___y_3451_ = v___y_3461_;
v___y_3452_ = v_val_3463_;
goto v___jp_3443_;
}
}
v___jp_3464_:
{
lean_object* v_preInfo_x3f_3472_; 
v_preInfo_x3f_3472_ = lean_ctor_get(v___y_3466_, 1);
if (lean_obj_tag(v_preInfo_x3f_3472_) == 0)
{
lean_object* v_postInfo_x3f_3473_; 
v_postInfo_x3f_3473_ = lean_ctor_get(v___y_3466_, 2);
lean_inc(v_postInfo_x3f_3473_);
v___y_3454_ = v___y_3465_;
v___y_3455_ = v___y_3466_;
v_postInfo_x3f_3456_ = v_postInfo_x3f_3473_;
v___y_3457_ = v___y_3467_;
v___y_3458_ = v___y_3469_;
v___y_3459_ = v___y_3468_;
v___y_3460_ = v_edits_3471_;
v___y_3461_ = v___y_3470_;
v___y_3462_ = v___x_3353_;
goto v___jp_3453_;
}
else
{
lean_object* v_postInfo_x3f_3474_; lean_object* v_val_3475_; 
v_postInfo_x3f_3474_ = lean_ctor_get(v___y_3466_, 2);
lean_inc(v_postInfo_x3f_3474_);
v_val_3475_ = lean_ctor_get(v_preInfo_x3f_3472_, 0);
lean_inc(v_val_3475_);
v___y_3454_ = v___y_3465_;
v___y_3455_ = v___y_3466_;
v_postInfo_x3f_3456_ = v_postInfo_x3f_3474_;
v___y_3457_ = v___y_3467_;
v___y_3458_ = v___y_3469_;
v___y_3459_ = v___y_3468_;
v___y_3460_ = v_edits_3471_;
v___y_3461_ = v___y_3470_;
v___y_3462_ = v_val_3475_;
goto v___jp_3453_;
}
}
v___jp_3476_:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; uint8_t v___x_3489_; 
v___x_3487_ = lean_unsigned_to_nat(1u);
v___x_3488_ = lean_nat_add(v___y_3480_, v___x_3487_);
v___x_3489_ = lean_nat_dec_le(v___x_3488_, v_stop_3481_);
lean_dec(v___x_3488_);
if (v___x_3489_ == 0)
{
lean_dec(v_stop_3481_);
lean_dec(v___y_3480_);
v___y_3465_ = v___y_3477_;
v___y_3466_ = v___y_3478_;
v___y_3467_ = v___y_3479_;
v___y_3468_ = v___y_3483_;
v___y_3469_ = v___y_3482_;
v___y_3470_ = v___y_3485_;
v_edits_3471_ = v_edits_3486_;
goto v___jp_3464_;
}
else
{
lean_object* v_source_3490_; uint8_t v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v_source_3490_ = lean_ctor_get(v___y_3484_, 0);
v___x_3491_ = 2;
v___x_3492_ = lean_string_utf8_extract(v_source_3490_, v___y_3480_, v_stop_3481_);
lean_dec(v_stop_3481_);
lean_dec(v___y_3480_);
v___x_3493_ = lean_box(v___x_3491_);
v___x_3494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3494_, 0, v___x_3493_);
lean_ctor_set(v___x_3494_, 1, v___x_3492_);
v___x_3495_ = lean_array_push(v_edits_3486_, v___x_3494_);
v___y_3465_ = v___y_3477_;
v___y_3466_ = v___y_3478_;
v___y_3467_ = v___y_3479_;
v___y_3468_ = v___y_3483_;
v___y_3469_ = v___y_3482_;
v___y_3470_ = v___y_3485_;
v_edits_3471_ = v___x_3495_;
goto v___jp_3464_;
}
}
v___jp_3496_:
{
if (lean_obj_tag(v___y_3505_) == 0)
{
lean_dec(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
v___y_3465_ = v___y_3497_;
v___y_3466_ = v___y_3498_;
v___y_3467_ = v___y_3502_;
v___y_3468_ = v___y_3504_;
v___y_3469_ = v___y_3503_;
v___y_3470_ = v___y_3505_;
v_edits_3471_ = v_edits_3506_;
goto v___jp_3464_;
}
else
{
lean_object* v_val_3508_; lean_object* v___x_3509_; 
v_val_3508_ = lean_ctor_get(v___y_3505_, 0);
v___x_3509_ = l_Lean_Syntax_getRange_x3f(v_val_3508_, v___y_3502_);
if (lean_obj_tag(v___x_3509_) == 1)
{
lean_object* v_val_3510_; uint8_t v___x_3511_; 
v_val_3510_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_val_3510_);
lean_dec_ref_known(v___x_3509_, 1);
v___x_3511_ = l_Lean_Syntax_Range_includes(v_val_3510_, v___y_3499_, v___y_3502_, v___y_3502_);
lean_dec_ref(v___y_3499_);
if (v___x_3511_ == 0)
{
lean_dec(v_val_3510_);
lean_dec(v___y_3501_);
lean_dec(v___y_3500_);
v___y_3465_ = v___y_3497_;
v___y_3466_ = v___y_3498_;
v___y_3467_ = v___y_3502_;
v___y_3468_ = v___y_3504_;
v___y_3469_ = v___y_3503_;
v___y_3470_ = v___y_3505_;
v_edits_3471_ = v_edits_3506_;
goto v___jp_3464_;
}
else
{
lean_object* v_toCold_3512_; lean_object* v_fileMap_3513_; lean_object* v_start_3514_; lean_object* v_stop_3515_; lean_object* v___x_3517_; uint8_t v_isShared_3518_; uint8_t v_isSharedCheck_3532_; 
v_toCold_3512_ = lean_ctor_get(v___y_3507_, 0);
v_fileMap_3513_ = lean_ctor_get(v_toCold_3512_, 1);
v_start_3514_ = lean_ctor_get(v_val_3510_, 0);
v_stop_3515_ = lean_ctor_get(v_val_3510_, 1);
v_isSharedCheck_3532_ = !lean_is_exclusive(v_val_3510_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3517_ = v_val_3510_;
v_isShared_3518_ = v_isSharedCheck_3532_;
goto v_resetjp_3516_;
}
else
{
lean_inc(v_stop_3515_);
lean_inc(v_start_3514_);
lean_dec(v_val_3510_);
v___x_3517_ = lean_box(0);
v_isShared_3518_ = v_isSharedCheck_3532_;
goto v_resetjp_3516_;
}
v_resetjp_3516_:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; uint8_t v___x_3521_; 
v___x_3519_ = lean_unsigned_to_nat(1u);
v___x_3520_ = lean_nat_add(v_start_3514_, v___x_3519_);
v___x_3521_ = lean_nat_dec_le(v___x_3520_, v___y_3500_);
lean_dec(v___x_3520_);
if (v___x_3521_ == 0)
{
lean_del_object(v___x_3517_);
lean_dec(v_start_3514_);
lean_dec(v___y_3500_);
v___y_3477_ = v___y_3497_;
v___y_3478_ = v___y_3498_;
v___y_3479_ = v___y_3502_;
v___y_3480_ = v___y_3501_;
v_stop_3481_ = v_stop_3515_;
v___y_3482_ = v___y_3503_;
v___y_3483_ = v___y_3504_;
v___y_3484_ = v_fileMap_3513_;
v___y_3485_ = v___y_3505_;
v_edits_3486_ = v_edits_3506_;
goto v___jp_3476_;
}
else
{
lean_object* v_source_3522_; uint8_t v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3527_; 
v_source_3522_ = lean_ctor_get(v_fileMap_3513_, 0);
v___x_3523_ = 2;
v___x_3524_ = lean_string_utf8_extract(v_source_3522_, v_start_3514_, v___y_3500_);
lean_dec(v___y_3500_);
lean_dec(v_start_3514_);
v___x_3525_ = lean_box(v___x_3523_);
if (v_isShared_3518_ == 0)
{
lean_ctor_set(v___x_3517_, 1, v___x_3524_);
lean_ctor_set(v___x_3517_, 0, v___x_3525_);
v___x_3527_ = v___x_3517_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3525_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v___x_3524_);
v___x_3527_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3528_ = lean_mk_empty_array_with_capacity(v___x_3519_);
v___x_3529_ = lean_array_push(v___x_3528_, v___x_3527_);
v___x_3530_ = l_Array_append___redArg(v___x_3529_, v_edits_3506_);
lean_dec_ref(v_edits_3506_);
v___y_3477_ = v___y_3497_;
v___y_3478_ = v___y_3498_;
v___y_3479_ = v___y_3502_;
v___y_3480_ = v___y_3501_;
v_stop_3481_ = v_stop_3515_;
v___y_3482_ = v___y_3503_;
v___y_3483_ = v___y_3504_;
v___y_3484_ = v_fileMap_3513_;
v___y_3485_ = v___y_3505_;
v_edits_3486_ = v___x_3530_;
goto v___jp_3476_;
}
}
}
}
}
else
{
lean_dec(v___x_3509_);
lean_dec(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
v___y_3465_ = v___y_3497_;
v___y_3466_ = v___y_3498_;
v___y_3467_ = v___y_3502_;
v___y_3468_ = v___y_3504_;
v___y_3469_ = v___y_3503_;
v___y_3470_ = v___y_3505_;
v_edits_3471_ = v_edits_3506_;
goto v___jp_3464_;
}
}
}
v___jp_3534_:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
lean_inc_ref(v___y_3536_);
v___x_3545_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3545_, 0, v___y_3543_);
lean_ctor_set(v___x_3545_, 1, v___y_3544_);
lean_ctor_set(v___x_3545_, 2, v___y_3536_);
v___x_3546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3533_);
lean_ctor_set(v___x_3546_, 1, v___x_3545_);
v___x_3547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3547_, 0, v___y_3539_);
lean_ctor_set(v___x_3547_, 1, v___x_3546_);
v___x_3548_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3547_);
v___x_3549_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v___x_3548_, v___y_3301_, v___y_3302_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v_messageData_x3f_3550_; 
lean_dec_ref_known(v___x_3549_, 1);
v_messageData_x3f_3550_ = lean_ctor_get(v___y_3536_, 4);
if (lean_obj_tag(v_messageData_x3f_3550_) == 1)
{
lean_object* v_start_3551_; lean_object* v_stop_3552_; lean_object* v_val_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; uint8_t v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v_start_3551_ = lean_ctor_get(v___y_3537_, 0);
lean_inc(v_start_3551_);
v_stop_3552_ = lean_ctor_get(v___y_3537_, 1);
lean_inc(v_stop_3552_);
v_val_3553_ = lean_ctor_get(v_messageData_x3f_3550_, 0);
v___x_3554_ = lean_box(0);
lean_inc(v_val_3553_);
v___x_3555_ = l_Lean_MessageData_format(v_val_3553_, v___x_3554_);
v___x_3556_ = 0;
v___x_3557_ = l_Std_Format_defWidth;
v___x_3558_ = lean_unsigned_to_nat(0u);
v___x_3559_ = l_Std_Format_pretty(v___x_3555_, v___x_3557_, v___x_3558_, v___x_3558_);
v___x_3560_ = lean_box(v___x_3556_);
v___x_3561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3560_);
lean_ctor_set(v___x_3561_, 1, v___x_3559_);
v___x_3562_ = lean_unsigned_to_nat(1u);
v___x_3563_ = lean_mk_empty_array_with_capacity(v___x_3562_);
v___x_3564_ = lean_array_push(v___x_3563_, v___x_3561_);
v___y_3497_ = v___y_3535_;
v___y_3498_ = v___y_3536_;
v___y_3499_ = v___y_3537_;
v___y_3500_ = v_start_3551_;
v___y_3501_ = v_stop_3552_;
v___y_3502_ = v___y_3538_;
v___y_3503_ = v___y_3541_;
v___y_3504_ = v___y_3540_;
v___y_3505_ = v___y_3542_;
v_edits_3506_ = v___x_3564_;
v___y_3507_ = v___y_3301_;
goto v___jp_3496_;
}
else
{
lean_object* v_toCold_3565_; lean_object* v_fileMap_3566_; lean_object* v_start_3567_; lean_object* v_stop_3568_; lean_object* v_source_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v_toCold_3565_ = lean_ctor_get(v___y_3301_, 0);
v_fileMap_3566_ = lean_ctor_get(v_toCold_3565_, 1);
v_start_3567_ = lean_ctor_get(v___y_3537_, 0);
lean_inc(v_start_3567_);
v_stop_3568_ = lean_ctor_get(v___y_3537_, 1);
lean_inc(v_stop_3568_);
v_source_3569_ = lean_ctor_get(v_fileMap_3566_, 0);
v___x_3570_ = lean_string_utf8_extract(v_source_3569_, v_start_3567_, v_stop_3568_);
lean_inc_ref(v___y_3541_);
v___x_3571_ = l_Lean_Meta_Hint_readableDiff(v___x_3570_, v___y_3541_, v___y_3540_);
v___y_3497_ = v___y_3535_;
v___y_3498_ = v___y_3536_;
v___y_3499_ = v___y_3537_;
v___y_3500_ = v_start_3567_;
v___y_3501_ = v_stop_3568_;
v___y_3502_ = v___y_3538_;
v___y_3503_ = v___y_3541_;
v___y_3504_ = v___y_3540_;
v___y_3505_ = v___y_3542_;
v_edits_3506_ = v___x_3571_;
v___y_3507_ = v___y_3301_;
goto v___jp_3496_;
}
}
else
{
lean_object* v_a_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3579_; 
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec_ref(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec_ref(v___y_3535_);
lean_dec_ref(v_b_3300_);
lean_dec(v_ref_3296_);
lean_dec(v_codeActionPrefix_x3f_3295_);
v_a_3572_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3579_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3579_ == 0)
{
v___x_3574_ = v___x_3549_;
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_a_3572_);
lean_dec(v___x_3549_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3579_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3577_; 
if (v_isShared_3575_ == 0)
{
v___x_3577_ = v___x_3574_;
goto v_reusejp_3576_;
}
else
{
lean_object* v_reuseFailAlloc_3578_; 
v_reuseFailAlloc_3578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3578_, 0, v_a_3572_);
v___x_3577_ = v_reuseFailAlloc_3578_;
goto v_reusejp_3576_;
}
v_reusejp_3576_:
{
return v___x_3577_;
}
}
}
}
v___jp_3580_:
{
lean_object* v_toCodeActionTitle_x3f_3590_; lean_object* v___x_3591_; 
v_toCodeActionTitle_x3f_3590_ = lean_ctor_get(v___y_3582_, 5);
v___x_3591_ = l_Lean_Syntax_ofRange(v___y_3589_, v___x_3349_);
if (lean_obj_tag(v_toCodeActionTitle_x3f_3590_) == 0)
{
if (lean_obj_tag(v_codeActionPrefix_x3f_3295_) == 0)
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3592_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__36));
v___x_3593_ = lean_string_append(v___x_3592_, v___y_3585_);
v___y_3535_ = v___y_3581_;
v___y_3536_ = v___y_3582_;
v___y_3537_ = v___y_3583_;
v___y_3538_ = v___y_3584_;
v___y_3539_ = v___x_3591_;
v___y_3540_ = v___y_3586_;
v___y_3541_ = v___y_3585_;
v___y_3542_ = v___y_3588_;
v___y_3543_ = v___y_3587_;
v___y_3544_ = v___x_3593_;
goto v___jp_3534_;
}
else
{
lean_object* v_val_3594_; lean_object* v___x_3595_; 
v_val_3594_ = lean_ctor_get(v_codeActionPrefix_x3f_3295_, 0);
lean_inc(v_val_3594_);
v___x_3595_ = lean_string_append(v_val_3594_, v___y_3585_);
v___y_3535_ = v___y_3581_;
v___y_3536_ = v___y_3582_;
v___y_3537_ = v___y_3583_;
v___y_3538_ = v___y_3584_;
v___y_3539_ = v___x_3591_;
v___y_3540_ = v___y_3586_;
v___y_3541_ = v___y_3585_;
v___y_3542_ = v___y_3588_;
v___y_3543_ = v___y_3587_;
v___y_3544_ = v___x_3595_;
goto v___jp_3534_;
}
}
else
{
lean_object* v_val_3596_; lean_object* v___x_3597_; 
v_val_3596_ = lean_ctor_get(v_toCodeActionTitle_x3f_3590_, 0);
lean_inc(v_val_3596_);
lean_inc_ref(v___y_3585_);
v___x_3597_ = lean_apply_1(v_val_3596_, v___y_3585_);
v___y_3535_ = v___y_3581_;
v___y_3536_ = v___y_3582_;
v___y_3537_ = v___y_3583_;
v___y_3538_ = v___y_3584_;
v___y_3539_ = v___x_3591_;
v___y_3540_ = v___y_3586_;
v___y_3541_ = v___y_3585_;
v___y_3542_ = v___y_3588_;
v___y_3543_ = v___y_3587_;
v___y_3544_ = v___x_3597_;
goto v___jp_3534_;
}
}
v___jp_3598_:
{
uint8_t v___x_3600_; lean_object* v___x_3601_; 
v___x_3600_ = 0;
v___x_3601_ = l_Lean_Syntax_getRange_x3f(v___y_3599_, v___x_3600_);
lean_dec(v___y_3599_);
if (lean_obj_tag(v___x_3601_) == 1)
{
lean_object* v_val_3602_; lean_object* v_toTryThisSuggestion_3603_; lean_object* v_previewSpan_x3f_3604_; uint8_t v_diffGranularity_3605_; lean_object* v___x_3606_; 
v_val_3602_ = lean_ctor_get(v___x_3601_, 0);
lean_inc_n(v_val_3602_, 2);
lean_dec_ref_known(v___x_3601_, 1);
v_toTryThisSuggestion_3603_ = lean_ctor_get(v_a_3351_, 0);
v_previewSpan_x3f_3604_ = lean_ctor_get(v_a_3351_, 2);
v_diffGranularity_3605_ = lean_ctor_get_uint8(v_a_3351_, sizeof(void*)*3);
lean_inc_ref(v_toTryThisSuggestion_3603_);
v___x_3606_ = l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(v_toTryThisSuggestion_3603_, v_val_3602_, v___y_3301_, v___y_3302_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; lean_object* v_range_3608_; lean_object* v_newText_3609_; lean_object* v___x_3610_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
lean_inc(v_a_3607_);
lean_dec_ref_known(v___x_3606_, 1);
v_range_3608_ = lean_ctor_get(v_a_3607_, 0);
lean_inc_ref(v_range_3608_);
v_newText_3609_ = lean_ctor_get(v_a_3607_, 1);
lean_inc_ref(v_newText_3609_);
v___x_3610_ = l_Lean_Syntax_getRange_x3f(v_ref_3296_, v___x_3600_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_inc(v_previewSpan_x3f_3604_);
lean_inc(v_val_3602_);
lean_inc_ref(v_toTryThisSuggestion_3603_);
v___y_3581_ = v_range_3608_;
v___y_3582_ = v_toTryThisSuggestion_3603_;
v___y_3583_ = v_val_3602_;
v___y_3584_ = v___x_3600_;
v___y_3585_ = v_newText_3609_;
v___y_3586_ = v_diffGranularity_3605_;
v___y_3587_ = v_a_3607_;
v___y_3588_ = v_previewSpan_x3f_3604_;
v___y_3589_ = v_val_3602_;
goto v___jp_3580_;
}
else
{
lean_object* v_val_3611_; 
v_val_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_val_3611_);
lean_dec_ref_known(v___x_3610_, 1);
lean_inc(v_previewSpan_x3f_3604_);
lean_inc_ref(v_toTryThisSuggestion_3603_);
v___y_3581_ = v_range_3608_;
v___y_3582_ = v_toTryThisSuggestion_3603_;
v___y_3583_ = v_val_3602_;
v___y_3584_ = v___x_3600_;
v___y_3585_ = v_newText_3609_;
v___y_3586_ = v_diffGranularity_3605_;
v___y_3587_ = v_a_3607_;
v___y_3588_ = v_previewSpan_x3f_3604_;
v___y_3589_ = v_val_3611_;
goto v___jp_3580_;
}
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
lean_dec(v_val_3602_);
lean_dec_ref(v_b_3300_);
lean_dec(v_ref_3296_);
lean_dec(v_codeActionPrefix_x3f_3295_);
v_a_3612_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3614_ = v___x_3606_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3606_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
else
{
lean_dec(v___x_3601_);
v_a_3305_ = v_b_3300_;
goto v___jp_3304_;
}
}
}
v___jp_3304_:
{
size_t v___x_3306_; size_t v___x_3307_; 
v___x_3306_ = ((size_t)1ULL);
v___x_3307_ = lean_usize_add(v_i_3299_, v___x_3306_);
v_i_3299_ = v___x_3307_;
v_b_3300_ = v_a_3305_;
goto _start;
}
v___jp_3309_:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3311_ = l_Lean_MessageData_nestD(v___y_3310_);
v___x_3312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3312_, 0, v_b_3300_);
lean_ctor_set(v___x_3312_, 1, v___x_3311_);
v_a_3305_ = v___x_3312_;
goto v___jp_3304_;
}
v___jp_3313_:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3317_, 0, v___y_3315_);
lean_ctor_set(v___x_3317_, 1, v___y_3316_);
v___x_3318_ = l_Lean_stringToMessageData(v___y_3314_);
v___x_3319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3317_);
lean_ctor_set(v___x_3319_, 1, v___x_3318_);
v___y_3310_ = v___x_3319_;
goto v___jp_3309_;
}
v___jp_3320_:
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3322_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3323_ = lean_unsigned_to_nat(2u);
v___x_3324_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3);
v___x_3325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
lean_ctor_set(v___x_3325_, 1, v___y_3321_);
v___x_3326_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3323_);
lean_ctor_set(v___x_3326_, 1, v___x_3325_);
v___x_3327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3322_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
v___y_3310_ = v___x_3327_;
goto v___jp_3309_;
}
v___jp_3328_:
{
lean_object* v___x_3333_; uint64_t v_javascriptHash_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; uint8_t v___x_3346_; 
v___x_3333_ = l_Lean_Meta_Hint_tryThisDiffWidget;
v_javascriptHash_3334_ = lean_ctor_get_uint64(v___x_3333_, sizeof(void*)*1);
v___x_3335_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8));
v___x_3336_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3336_, 0, v___x_3335_);
lean_ctor_set(v___x_3336_, 1, v___y_3330_);
lean_ctor_set_uint64(v___x_3336_, sizeof(void*)*2, v_javascriptHash_3334_);
v___x_3337_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3337_, 0, v___y_3332_);
v___x_3338_ = l_Lean_MessageData_ofFormat(v___x_3337_);
v___x_3339_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3336_);
lean_ctor_set(v___x_3339_, 1, v___x_3338_);
v___x_3340_ = l_Lean_stringToMessageData(v___y_3329_);
v___x_3341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3340_);
lean_ctor_set(v___x_3341_, 1, v___x_3339_);
v___x_3342_ = l_Lean_stringToMessageData(v___y_3331_);
v___x_3343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3341_);
lean_ctor_set(v___x_3343_, 1, v___x_3342_);
v___x_3344_ = lean_array_get_size(v_suggestions_3293_);
v___x_3345_ = lean_unsigned_to_nat(1u);
v___x_3346_ = lean_nat_dec_eq(v___x_3344_, v___x_3345_);
if (v___x_3346_ == 0)
{
v___y_3321_ = v___x_3343_;
goto v___jp_3320_;
}
else
{
if (v_forceList_3294_ == 0)
{
lean_object* v___x_3347_; lean_object* v___x_3348_; 
v___x_3347_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3347_);
lean_ctor_set(v___x_3348_, 1, v___x_3343_);
v___y_3310_ = v___x_3348_;
goto v___jp_3309_;
}
else
{
v___y_3321_ = v___x_3343_;
goto v___jp_3320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___boxed(lean_object* v_suggestions_3621_, lean_object* v_forceList_3622_, lean_object* v_codeActionPrefix_x3f_3623_, lean_object* v_ref_3624_, lean_object* v_as_3625_, lean_object* v_sz_3626_, lean_object* v_i_3627_, lean_object* v_b_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
uint8_t v_forceList_boxed_3632_; size_t v_sz_boxed_3633_; size_t v_i_boxed_3634_; lean_object* v_res_3635_; 
v_forceList_boxed_3632_ = lean_unbox(v_forceList_3622_);
v_sz_boxed_3633_ = lean_unbox_usize(v_sz_3626_);
lean_dec(v_sz_3626_);
v_i_boxed_3634_ = lean_unbox_usize(v_i_3627_);
lean_dec(v_i_3627_);
v_res_3635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3621_, v_forceList_boxed_3632_, v_codeActionPrefix_x3f_3623_, v_ref_3624_, v_as_3625_, v_sz_boxed_3633_, v_i_boxed_3634_, v_b_3628_, v___y_3629_, v___y_3630_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec_ref(v_as_3625_);
lean_dec_ref(v_suggestions_3621_);
return v_res_3635_;
}
}
static lean_object* _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0(void){
_start:
{
lean_object* v___x_3636_; lean_object* v_msg_3637_; 
v___x_3636_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v_msg_3637_ = l_Lean_stringToMessageData(v___x_3636_);
return v_msg_3637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage(lean_object* v_suggestions_3638_, lean_object* v_ref_3639_, lean_object* v_codeActionPrefix_x3f_3640_, uint8_t v_forceList_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_){
_start:
{
lean_object* v_msg_3645_; size_t v_sz_3646_; size_t v___x_3647_; lean_object* v___x_3648_; 
v_msg_3645_ = lean_obj_once(&l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0, &l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0_once, _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0);
v_sz_3646_ = lean_array_size(v_suggestions_3638_);
v___x_3647_ = ((size_t)0ULL);
v___x_3648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3638_, v_forceList_3641_, v_codeActionPrefix_x3f_3640_, v_ref_3639_, v_suggestions_3638_, v_sz_3646_, v___x_3647_, v_msg_3645_, v_a_3642_, v_a_3643_);
return v___x_3648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage___boxed(lean_object* v_suggestions_3649_, lean_object* v_ref_3650_, lean_object* v_codeActionPrefix_x3f_3651_, lean_object* v_forceList_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_){
_start:
{
uint8_t v_forceList_boxed_3656_; lean_object* v_res_3657_; 
v_forceList_boxed_3656_ = lean_unbox(v_forceList_3652_);
v_res_3657_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3649_, v_ref_3650_, v_codeActionPrefix_x3f_3651_, v_forceList_boxed_3656_, v_a_3653_, v_a_3654_);
lean_dec(v_a_3654_);
lean_dec_ref(v_a_3653_);
lean_dec_ref(v_suggestions_3649_);
return v_res_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(lean_object* v_t_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
lean_object* v___x_3662_; 
v___x_3662_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3658_, v___y_3660_);
return v___x_3662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___boxed(lean_object* v_t_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
lean_object* v_res_3667_; 
v_res_3667_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(v_t_3663_, v___y_3664_, v___y_3665_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
return v_res_3667_;
}
}
static lean_object* _init_l_Lean_MessageData_hint___closed__3(void){
_start:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3672_ = ((lean_object*)(l_Lean_MessageData_hint___closed__2));
v___x_3673_ = l_Lean_stringToMessageData(v___x_3672_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint(lean_object* v_hint_3674_, lean_object* v_suggestions_3675_, lean_object* v_ref_x3f_3676_, lean_object* v_codeActionPrefix_x3f_3677_, uint8_t v_forceList_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_){
_start:
{
lean_object* v___y_3683_; 
if (lean_obj_tag(v_ref_x3f_3676_) == 0)
{
lean_object* v_ref_3698_; 
v_ref_3698_ = lean_ctor_get(v_a_3679_, 4);
lean_inc(v_ref_3698_);
v___y_3683_ = v_ref_3698_;
goto v___jp_3682_;
}
else
{
lean_object* v_val_3699_; 
v_val_3699_ = lean_ctor_get(v_ref_x3f_3676_, 0);
lean_inc(v_val_3699_);
lean_dec_ref_known(v_ref_x3f_3676_, 1);
v___y_3683_ = v_val_3699_;
goto v___jp_3682_;
}
v___jp_3682_:
{
lean_object* v___x_3684_; 
v___x_3684_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3675_, v___y_3683_, v_codeActionPrefix_x3f_3677_, v_forceList_3678_, v_a_3679_, v_a_3680_);
if (lean_obj_tag(v___x_3684_) == 0)
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3697_; 
v_a_3685_ = lean_ctor_get(v___x_3684_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3684_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3687_ = v___x_3684_;
v_isShared_3688_ = v_isSharedCheck_3697_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3684_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3697_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3695_; 
v___x_3689_ = ((lean_object*)(l_Lean_MessageData_hint___closed__1));
v___x_3690_ = lean_obj_once(&l_Lean_MessageData_hint___closed__3, &l_Lean_MessageData_hint___closed__3_once, _init_l_Lean_MessageData_hint___closed__3);
v___x_3691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3690_);
lean_ctor_set(v___x_3691_, 1, v_hint_3674_);
v___x_3692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3691_);
lean_ctor_set(v___x_3692_, 1, v_a_3685_);
v___x_3693_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3689_);
lean_ctor_set(v___x_3693_, 1, v___x_3692_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set(v___x_3687_, 0, v___x_3693_);
v___x_3695_ = v___x_3687_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3693_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
else
{
lean_dec_ref(v_hint_3674_);
return v___x_3684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint___boxed(lean_object* v_hint_3700_, lean_object* v_suggestions_3701_, lean_object* v_ref_x3f_3702_, lean_object* v_codeActionPrefix_x3f_3703_, lean_object* v_forceList_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_){
_start:
{
uint8_t v_forceList_boxed_3708_; lean_object* v_res_3709_; 
v_forceList_boxed_3708_ = lean_unbox(v_forceList_3704_);
v_res_3709_ = l_Lean_MessageData_hint(v_hint_3700_, v_suggestions_3701_, v_ref_x3f_3702_, v_codeActionPrefix_x3f_3703_, v_forceList_boxed_3708_, v_a_3705_, v_a_3706_);
lean_dec(v_a_3706_);
lean_dec_ref(v_a_3705_);
lean_dec_ref(v_suggestions_3701_);
return v_res_3709_;
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
l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed__const__1 = _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed__const__1();
lean_mark_persistent(l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed__const__1);
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
