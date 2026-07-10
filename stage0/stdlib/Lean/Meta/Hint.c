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
uint8_t lean_bool_not(uint8_t);
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
lean_object* v___x_1127_; lean_object* v___x_1128_; uint32_t v___x_1129_; uint8_t v___x_1130_; uint8_t v___x_1131_; 
v___x_1127_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1;
v___x_1128_ = lean_array_get_borrowed(v___x_1127_, v_edited_1100_, v_snd_1105_);
v___x_1129_ = lean_unbox_uint32(v___x_1128_);
v___x_1130_ = lean_uint32_dec_eq(v___x_1129_, v_a_1102_);
v___x_1131_ = lean_bool_not(v___x_1130_);
v___y_1110_ = v___x_1131_;
goto v___jp_1109_;
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
lean_object* v___x_1166_; lean_object* v___x_1167_; uint32_t v___x_1168_; uint8_t v___x_1169_; uint8_t v___x_1170_; 
v___x_1166_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg___boxed__const__1;
v___x_1167_ = lean_array_get_borrowed(v___x_1166_, v_original_1139_, v_snd_1144_);
v___x_1168_ = lean_unbox_uint32(v___x_1167_);
v___x_1169_ = lean_uint32_dec_eq(v___x_1168_, v_a_1141_);
v___x_1170_ = lean_bool_not(v___x_1169_);
v___y_1149_ = v___x_1170_;
goto v___jp_1148_;
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
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; uint8_t v___x_1404_; 
v___x_1400_ = lean_unsigned_to_nat(0u);
v___x_1401_ = lean_string_utf8_byte_size(v_oldWs_1398_);
lean_inc_ref(v_oldWs_1398_);
v___x_1402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1402_, 0, v_oldWs_1398_);
lean_ctor_set(v___x_1402_, 1, v___x_1400_);
lean_ctor_set(v___x_1402_, 2, v___x_1401_);
v___x_1403_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_1402_);
lean_dec_ref_known(v___x_1402_, 3);
v___x_1404_ = lean_bool_not(v___x_1403_);
if (v___x_1404_ == 0)
{
uint8_t v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
lean_dec_ref(v_oldWs_1398_);
v___x_1405_ = 2;
v___x_1406_ = lean_box(v___x_1405_);
v___x_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1406_);
lean_ctor_set(v___x_1407_, 1, v_newWs_1399_);
v___x_1408_ = lean_unsigned_to_nat(1u);
v___x_1409_ = lean_mk_empty_array_with_capacity(v___x_1408_);
v___x_1410_ = lean_array_push(v___x_1409_, v___x_1407_);
return v___x_1410_;
}
else
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1411_ = lean_string_data(v_oldWs_1398_);
v___x_1412_ = lean_array_mk(v___x_1411_);
v___x_1413_ = lean_string_data(v_newWs_1399_);
v___x_1414_ = lean_array_mk(v___x_1413_);
v___x_1415_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_1412_, v___x_1414_);
v___x_1416_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_1415_);
lean_dec_ref(v___x_1415_);
return v___x_1416_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(lean_object* v_s_1417_, lean_object* v_inst_1418_, lean_object* v_R_1419_, lean_object* v_a_1420_, uint8_t v_b_1421_, lean_object* v_c_1422_){
_start:
{
uint8_t v___x_1423_; 
v___x_1423_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1417_, v_a_1420_, v_b_1421_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___boxed(lean_object* v_s_1424_, lean_object* v_inst_1425_, lean_object* v_R_1426_, lean_object* v_a_1427_, lean_object* v_b_1428_, lean_object* v_c_1429_){
_start:
{
uint8_t v_b_boxed_1430_; uint8_t v_res_1431_; lean_object* v_r_1432_; 
v_b_boxed_1430_ = lean_unbox(v_b_1428_);
v_res_1431_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(v_s_1424_, v_inst_1425_, v_R_1426_, v_a_1427_, v_b_boxed_1430_, v_c_1429_);
lean_dec_ref(v_s_1424_);
v_r_1432_ = lean_box(v_res_1431_);
return v_r_1432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(lean_object* v_original_1433_, lean_object* v___x_1434_, uint32_t v_a_1435_, lean_object* v_inst_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v_original_1433_, v___x_1434_, v_a_1435_, v_a_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___boxed(lean_object* v_original_1439_, lean_object* v___x_1440_, lean_object* v_a_1441_, lean_object* v_inst_1442_, lean_object* v_a_1443_){
_start:
{
uint32_t v_a_boxed_1444_; lean_object* v_res_1445_; 
v_a_boxed_1444_ = lean_unbox_uint32(v_a_1441_);
lean_dec(v_a_1441_);
v_res_1445_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(v_original_1439_, v___x_1440_, v_a_boxed_1444_, v_inst_1442_, v_a_1443_);
lean_dec(v___x_1440_);
lean_dec_ref(v_original_1439_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(lean_object* v_edited_1446_, lean_object* v___x_1447_, uint32_t v_a_1448_, lean_object* v_inst_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___redArg(v_edited_1446_, v___x_1447_, v_a_1448_, v_a_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___boxed(lean_object* v_edited_1452_, lean_object* v___x_1453_, lean_object* v_a_1454_, lean_object* v_inst_1455_, lean_object* v_a_1456_){
_start:
{
uint32_t v_a_boxed_1457_; lean_object* v_res_1458_; 
v_a_boxed_1457_ = lean_unbox_uint32(v_a_1454_);
lean_dec(v_a_1454_);
v_res_1458_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v_edited_1452_, v___x_1453_, v_a_boxed_1457_, v_inst_1455_, v_a_1456_);
lean_dec(v___x_1453_);
lean_dec_ref(v_edited_1452_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(lean_object* v___x_1459_, lean_object* v_original_1460_, lean_object* v_inst_1461_, lean_object* v_a_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_1459_, v_original_1460_, v_a_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___boxed(lean_object* v___x_1464_, lean_object* v_original_1465_, lean_object* v_inst_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(v___x_1464_, v_original_1465_, v_inst_1466_, v_a_1467_);
lean_dec_ref(v_original_1465_);
lean_dec(v___x_1464_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(lean_object* v___x_1469_, lean_object* v_edited_1470_, lean_object* v_inst_1471_, lean_object* v_a_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1469_, v_edited_1470_, v_a_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___boxed(lean_object* v___x_1474_, lean_object* v_edited_1475_, lean_object* v_inst_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(v___x_1474_, v_edited_1475_, v_inst_1476_, v_a_1477_);
lean_dec_ref(v_edited_1475_);
lean_dec(v___x_1474_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5(lean_object* v_as_1479_, lean_object* v_as_x27_1480_, lean_object* v_b_1481_, lean_object* v_a_1482_){
_start:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___redArg(v_as_x27_1480_, v_b_1481_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5___boxed(lean_object* v_as_1484_, lean_object* v_as_x27_1485_, lean_object* v_b_1486_, lean_object* v_a_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__5(v_as_1484_, v_as_x27_1485_, v_b_1486_, v_a_1487_);
lean_dec(v_as_x27_1485_);
lean_dec(v_as_1484_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8(lean_object* v_lsize_1489_, lean_object* v_rsize_1490_, lean_object* v_histogram_1491_, lean_object* v_index_1492_, uint32_t v_val_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___redArg(v_histogram_1491_, v_index_1492_, v_val_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8___boxed(lean_object* v_lsize_1495_, lean_object* v_rsize_1496_, lean_object* v_histogram_1497_, lean_object* v_index_1498_, lean_object* v_val_1499_){
_start:
{
uint32_t v_val_boxed_1500_; lean_object* v_res_1501_; 
v_val_boxed_1500_ = lean_unbox_uint32(v_val_1499_);
lean_dec(v_val_1499_);
v_res_1501_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8(v_lsize_1495_, v_rsize_1496_, v_histogram_1497_, v_index_1498_, v_val_boxed_1500_);
lean_dec(v_rsize_1496_);
lean_dec(v_lsize_1495_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9(lean_object* v_upperBound_1502_, lean_object* v___x_1503_, lean_object* v_fst_1504_, lean_object* v___x_1505_, lean_object* v_inst_1506_, lean_object* v_R_1507_, lean_object* v_a_1508_, lean_object* v_b_1509_, lean_object* v_c_1510_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___redArg(v_upperBound_1502_, v___x_1503_, v_fst_1504_, v___x_1505_, v_a_1508_, v_b_1509_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9___boxed(lean_object* v_upperBound_1512_, lean_object* v___x_1513_, lean_object* v_fst_1514_, lean_object* v___x_1515_, lean_object* v_inst_1516_, lean_object* v_R_1517_, lean_object* v_a_1518_, lean_object* v_b_1519_, lean_object* v_c_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__9(v_upperBound_1512_, v___x_1513_, v_fst_1514_, v___x_1515_, v_inst_1516_, v_R_1517_, v_a_1518_, v_b_1519_, v_c_1520_);
lean_dec(v___x_1515_);
lean_dec_ref(v_fst_1514_);
lean_dec(v___x_1513_);
lean_dec(v_upperBound_1512_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10(lean_object* v_lsize_1522_, lean_object* v_rsize_1523_, lean_object* v_histogram_1524_, lean_object* v_index_1525_, uint32_t v_val_1526_){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___redArg(v_histogram_1524_, v_index_1525_, v_val_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10___boxed(lean_object* v_lsize_1528_, lean_object* v_rsize_1529_, lean_object* v_histogram_1530_, lean_object* v_index_1531_, lean_object* v_val_1532_){
_start:
{
uint32_t v_val_boxed_1533_; lean_object* v_res_1534_; 
v_val_boxed_1533_ = lean_unbox_uint32(v_val_1532_);
lean_dec(v_val_1532_);
v_res_1534_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__10(v_lsize_1528_, v_rsize_1529_, v_histogram_1530_, v_index_1531_, v_val_boxed_1533_);
lean_dec(v_rsize_1529_);
lean_dec(v_lsize_1528_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11(lean_object* v_upperBound_1535_, lean_object* v_fst_1536_, lean_object* v___x_1537_, lean_object* v_fst_1538_, lean_object* v_inst_1539_, lean_object* v_R_1540_, lean_object* v_a_1541_, lean_object* v_b_1542_, lean_object* v_c_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___redArg(v_upperBound_1535_, v_fst_1536_, v___x_1537_, v_fst_1538_, v_a_1541_, v_b_1542_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11___boxed(lean_object* v_upperBound_1545_, lean_object* v_fst_1546_, lean_object* v___x_1547_, lean_object* v_fst_1548_, lean_object* v_inst_1549_, lean_object* v_R_1550_, lean_object* v_a_1551_, lean_object* v_b_1552_, lean_object* v_c_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__11(v_upperBound_1545_, v_fst_1546_, v___x_1547_, v_fst_1548_, v_inst_1549_, v_R_1550_, v_a_1551_, v_b_1552_, v_c_1553_);
lean_dec_ref(v_fst_1548_);
lean_dec(v___x_1547_);
lean_dec_ref(v_fst_1546_);
lean_dec(v_upperBound_1545_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11(lean_object* v_00_u03b2_1555_, lean_object* v_m_1556_, uint32_t v_a_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___redArg(v_m_1556_, v_a_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11___boxed(lean_object* v_00_u03b2_1559_, lean_object* v_m_1560_, lean_object* v_a_1561_){
_start:
{
uint32_t v_a_boxed_1562_; lean_object* v_res_1563_; 
v_a_boxed_1562_ = lean_unbox_uint32(v_a_1561_);
lean_dec(v_a_1561_);
v_res_1563_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11(v_00_u03b2_1559_, v_m_1560_, v_a_boxed_1562_);
lean_dec_ref(v_m_1560_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12(lean_object* v_00_u03b2_1564_, lean_object* v_m_1565_, uint32_t v_a_1566_, lean_object* v_b_1567_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___redArg(v_m_1565_, v_a_1566_, v_b_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12___boxed(lean_object* v_00_u03b2_1569_, lean_object* v_m_1570_, lean_object* v_a_1571_, lean_object* v_b_1572_){
_start:
{
uint32_t v_a_boxed_1573_; lean_object* v_res_1574_; 
v_a_boxed_1573_ = lean_unbox_uint32(v_a_1571_);
lean_dec(v_a_1571_);
v_res_1574_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12(v_00_u03b2_1569_, v_m_1570_, v_a_boxed_1573_, v_b_1572_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14(lean_object* v_inst_1575_, lean_object* v_R_1576_, lean_object* v_a_1577_, lean_object* v_b_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__4_spec__6_spec__14___redArg(v_a_1577_, v_b_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20(lean_object* v_00_u03b2_1580_, uint32_t v_a_1581_, lean_object* v_x_1582_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___redArg(v_a_1581_, v_x_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20___boxed(lean_object* v_00_u03b2_1584_, lean_object* v_a_1585_, lean_object* v_x_1586_){
_start:
{
uint32_t v_a_boxed_1587_; lean_object* v_res_1588_; 
v_a_boxed_1587_ = lean_unbox_uint32(v_a_1585_);
lean_dec(v_a_1585_);
v_res_1588_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__11_spec__20(v_00_u03b2_1584_, v_a_boxed_1587_, v_x_1586_);
lean_dec(v_x_1586_);
return v_res_1588_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22(lean_object* v_00_u03b2_1589_, uint32_t v_a_1590_, lean_object* v_x_1591_){
_start:
{
uint8_t v___x_1592_; 
v___x_1592_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___redArg(v_a_1590_, v_x_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22___boxed(lean_object* v_00_u03b2_1593_, lean_object* v_a_1594_, lean_object* v_x_1595_){
_start:
{
uint32_t v_a_boxed_1596_; uint8_t v_res_1597_; lean_object* v_r_1598_; 
v_a_boxed_1596_ = lean_unbox_uint32(v_a_1594_);
lean_dec(v_a_1594_);
v_res_1597_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__22(v_00_u03b2_1593_, v_a_boxed_1596_, v_x_1595_);
lean_dec(v_x_1595_);
v_r_1598_ = lean_box(v_res_1597_);
return v_r_1598_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23(lean_object* v_00_u03b2_1599_, lean_object* v_data_1600_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23___redArg(v_data_1600_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24(lean_object* v_00_u03b2_1602_, uint32_t v_a_1603_, lean_object* v_b_1604_, lean_object* v_x_1605_){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___redArg(v_a_1603_, v_b_1604_, v_x_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24___boxed(lean_object* v_00_u03b2_1607_, lean_object* v_a_1608_, lean_object* v_b_1609_, lean_object* v_x_1610_){
_start:
{
uint32_t v_a_boxed_1611_; lean_object* v_res_1612_; 
v_a_boxed_1611_ = lean_unbox_uint32(v_a_1608_);
lean_dec(v_a_1608_);
v_res_1612_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__24(v_00_u03b2_1607_, v_a_boxed_1611_, v_b_1609_, v_x_1610_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28(lean_object* v_00_u03b2_1613_, lean_object* v_i_1614_, lean_object* v_source_1615_, lean_object* v_target_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28___redArg(v_i_1614_, v_source_1615_, v_target_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_1618_, lean_object* v_x_1619_, lean_object* v_x_1620_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_spec__8_spec__12_spec__23_spec__28_spec__29___redArg(v_x_1619_, v_x_1620_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(lean_object* v_s_1622_, lean_object* v_stopPos_1623_, lean_object* v_i_1624_){
_start:
{
uint8_t v___y_1629_; uint8_t v___x_1630_; 
v___x_1630_ = lean_nat_dec_lt(v_i_1624_, v_stopPos_1623_);
if (v___x_1630_ == 0)
{
return v_i_1624_;
}
else
{
uint32_t v___x_1631_; uint8_t v___y_1633_; uint32_t v___x_1638_; uint8_t v___x_1639_; 
v___x_1631_ = lean_string_utf8_get(v_s_1622_, v_i_1624_);
v___x_1638_ = 32;
v___x_1639_ = lean_uint32_dec_eq(v___x_1631_, v___x_1638_);
if (v___x_1639_ == 0)
{
uint32_t v___x_1640_; uint8_t v___x_1641_; 
v___x_1640_ = 9;
v___x_1641_ = lean_uint32_dec_eq(v___x_1631_, v___x_1640_);
v___y_1633_ = v___x_1641_;
goto v___jp_1632_;
}
else
{
v___y_1633_ = v___x_1639_;
goto v___jp_1632_;
}
v___jp_1632_:
{
if (v___y_1633_ == 0)
{
uint32_t v___x_1634_; uint8_t v___x_1635_; 
v___x_1634_ = 13;
v___x_1635_ = lean_uint32_dec_eq(v___x_1631_, v___x_1634_);
if (v___x_1635_ == 0)
{
uint32_t v___x_1636_; uint8_t v___x_1637_; 
v___x_1636_ = 10;
v___x_1637_ = lean_uint32_dec_eq(v___x_1631_, v___x_1636_);
v___y_1629_ = v___x_1637_;
goto v___jp_1628_;
}
else
{
v___y_1629_ = v___x_1635_;
goto v___jp_1628_;
}
}
else
{
goto v___jp_1625_;
}
}
}
v___jp_1625_:
{
lean_object* v___x_1626_; 
v___x_1626_ = lean_string_utf8_next(v_s_1622_, v_i_1624_);
lean_dec(v_i_1624_);
v_i_1624_ = v___x_1626_;
goto _start;
}
v___jp_1628_:
{
if (v___y_1629_ == 0)
{
return v_i_1624_;
}
else
{
goto v___jp_1625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0___boxed(lean_object* v_s_1642_, lean_object* v_stopPos_1643_, lean_object* v_i_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1642_, v_stopPos_1643_, v_i_1644_);
lean_dec(v_stopPos_1643_);
lean_dec_ref(v_s_1642_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(lean_object* v_s_1646_, lean_object* v_b_1647_, lean_object* v_i_1648_, lean_object* v_r_1649_, lean_object* v_ws_1650_){
_start:
{
uint8_t v___y_1660_; uint8_t v___x_1663_; 
v___x_1663_ = lean_string_utf8_at_end(v_s_1646_, v_i_1648_);
if (v___x_1663_ == 0)
{
uint32_t v___x_1664_; uint8_t v___y_1666_; uint32_t v___x_1671_; uint8_t v___x_1672_; 
v___x_1664_ = lean_string_utf8_get(v_s_1646_, v_i_1648_);
v___x_1671_ = 32;
v___x_1672_ = lean_uint32_dec_eq(v___x_1664_, v___x_1671_);
if (v___x_1672_ == 0)
{
uint32_t v___x_1673_; uint8_t v___x_1674_; 
v___x_1673_ = 9;
v___x_1674_ = lean_uint32_dec_eq(v___x_1664_, v___x_1673_);
v___y_1666_ = v___x_1674_;
goto v___jp_1665_;
}
else
{
v___y_1666_ = v___x_1672_;
goto v___jp_1665_;
}
v___jp_1665_:
{
if (v___y_1666_ == 0)
{
uint32_t v___x_1667_; uint8_t v___x_1668_; 
v___x_1667_ = 13;
v___x_1668_ = lean_uint32_dec_eq(v___x_1664_, v___x_1667_);
if (v___x_1668_ == 0)
{
uint32_t v___x_1669_; uint8_t v___x_1670_; 
v___x_1669_ = 10;
v___x_1670_ = lean_uint32_dec_eq(v___x_1664_, v___x_1669_);
v___y_1660_ = v___x_1670_;
goto v___jp_1659_;
}
else
{
v___y_1660_ = v___x_1668_;
goto v___jp_1659_;
}
}
else
{
goto v___jp_1651_;
}
}
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1675_ = lean_string_utf8_extract(v_s_1646_, v_b_1647_, v_i_1648_);
lean_dec(v_i_1648_);
lean_dec(v_b_1647_);
v___x_1676_ = lean_array_push(v_r_1649_, v___x_1675_);
v___x_1677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
lean_ctor_set(v___x_1677_, 1, v_ws_1650_);
return v___x_1677_;
}
v___jp_1651_:
{
lean_object* v___x_1652_; lean_object* v_e_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1652_ = lean_string_utf8_byte_size(v_s_1646_);
lean_inc(v_i_1648_);
v_e_1653_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1646_, v___x_1652_, v_i_1648_);
v___x_1654_ = lean_string_utf8_extract(v_s_1646_, v_b_1647_, v_i_1648_);
lean_dec(v_b_1647_);
v___x_1655_ = lean_array_push(v_r_1649_, v___x_1654_);
v___x_1656_ = lean_string_utf8_extract(v_s_1646_, v_i_1648_, v_e_1653_);
lean_dec(v_i_1648_);
v___x_1657_ = lean_array_push(v_ws_1650_, v___x_1656_);
lean_inc(v_e_1653_);
v_b_1647_ = v_e_1653_;
v_i_1648_ = v_e_1653_;
v_r_1649_ = v___x_1655_;
v_ws_1650_ = v___x_1657_;
goto _start;
}
v___jp_1659_:
{
if (v___y_1660_ == 0)
{
lean_object* v___x_1661_; 
v___x_1661_ = lean_string_utf8_next(v_s_1646_, v_i_1648_);
lean_dec(v_i_1648_);
v_i_1648_ = v___x_1661_;
goto _start;
}
else
{
goto v___jp_1651_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux___boxed(lean_object* v_s_1678_, lean_object* v_b_1679_, lean_object* v_i_1680_, lean_object* v_r_1681_, lean_object* v_ws_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1678_, v_b_1679_, v_i_1680_, v_r_1681_, v_ws_1682_);
lean_dec_ref(v_s_1678_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(lean_object* v_s_1686_){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = lean_unsigned_to_nat(0u);
v___x_1688_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_1689_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1686_, v___x_1687_, v___x_1687_, v___x_1688_, v___x_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___boxed(lean_object* v_s_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_1690_);
lean_dec_ref(v_s_1690_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(size_t v_sz_1692_, size_t v_i_1693_, lean_object* v_bs_1694_){
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
lean_object* v_v_1696_; lean_object* v_fst_1697_; lean_object* v_snd_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1732_; 
v_v_1696_ = lean_array_uget(v_bs_1694_, v_i_1693_);
v_fst_1697_ = lean_ctor_get(v_v_1696_, 0);
v_snd_1698_ = lean_ctor_get(v_v_1696_, 1);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_v_1696_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1700_ = v_v_1696_;
v_isShared_1701_ = v_isSharedCheck_1732_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_snd_1698_);
lean_inc(v_fst_1697_);
lean_dec(v_v_1696_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1732_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; lean_object* v_bs_x27_1703_; lean_object* v___y_1705_; lean_object* v___x_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1702_ = lean_unsigned_to_nat(0u);
v_bs_x27_1703_ = lean_array_uset(v_bs_1694_, v_i_1693_, v___x_1702_);
v___x_1710_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_1711_ = lean_array_get_size(v_snd_1698_);
v___x_1712_ = lean_nat_dec_lt(v___x_1702_, v___x_1711_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1714_; 
lean_dec(v_snd_1698_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 1, v___x_1710_);
v___x_1714_ = v___x_1700_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_fst_1697_);
lean_ctor_set(v_reuseFailAlloc_1715_, 1, v___x_1710_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
v___y_1705_ = v___x_1714_;
goto v___jp_1704_;
}
}
else
{
uint8_t v___x_1716_; 
v___x_1716_ = lean_nat_dec_le(v___x_1711_, v___x_1711_);
if (v___x_1716_ == 0)
{
if (v___x_1712_ == 0)
{
lean_object* v___x_1718_; 
lean_dec(v_snd_1698_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 1, v___x_1710_);
v___x_1718_ = v___x_1700_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_fst_1697_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v___x_1710_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
v___y_1705_ = v___x_1718_;
goto v___jp_1704_;
}
}
else
{
size_t v___x_1720_; size_t v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1720_ = ((size_t)0ULL);
v___x_1721_ = lean_usize_of_nat(v___x_1711_);
v___x_1722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_1698_, v___x_1720_, v___x_1721_, v___x_1710_);
lean_dec(v_snd_1698_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 1, v___x_1722_);
v___x_1724_ = v___x_1700_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_fst_1697_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
v___y_1705_ = v___x_1724_;
goto v___jp_1704_;
}
}
}
else
{
size_t v___x_1726_; size_t v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1730_; 
v___x_1726_ = ((size_t)0ULL);
v___x_1727_ = lean_usize_of_nat(v___x_1711_);
v___x_1728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_1698_, v___x_1726_, v___x_1727_, v___x_1710_);
lean_dec(v_snd_1698_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 1, v___x_1728_);
v___x_1730_ = v___x_1700_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_fst_1697_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v___x_1728_);
v___x_1730_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
v___y_1705_ = v___x_1730_;
goto v___jp_1704_;
}
}
}
v___jp_1704_:
{
size_t v___x_1706_; size_t v___x_1707_; lean_object* v___x_1708_; 
v___x_1706_ = ((size_t)1ULL);
v___x_1707_ = lean_usize_add(v_i_1693_, v___x_1706_);
v___x_1708_ = lean_array_uset(v_bs_x27_1703_, v_i_1693_, v___y_1705_);
v_i_1693_ = v___x_1707_;
v_bs_1694_ = v___x_1708_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0___boxed(lean_object* v_sz_1733_, lean_object* v_i_1734_, lean_object* v_bs_1735_){
_start:
{
size_t v_sz_boxed_1736_; size_t v_i_boxed_1737_; lean_object* v_res_1738_; 
v_sz_boxed_1736_ = lean_unbox_usize(v_sz_1733_);
lean_dec(v_sz_1733_);
v_i_boxed_1737_ = lean_unbox_usize(v_i_1734_);
lean_dec(v_i_1734_);
v_res_1738_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_boxed_1736_, v_i_boxed_1737_, v_bs_1735_);
return v_res_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(size_t v_sz_1739_, size_t v_i_1740_, lean_object* v_bs_1741_){
_start:
{
uint8_t v___x_1742_; 
v___x_1742_ = lean_usize_dec_lt(v_i_1740_, v_sz_1739_);
if (v___x_1742_ == 0)
{
return v_bs_1741_;
}
else
{
lean_object* v_v_1743_; lean_object* v___x_1744_; lean_object* v_bs_x27_1745_; uint8_t v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; size_t v___x_1749_; size_t v___x_1750_; lean_object* v___x_1751_; 
v_v_1743_ = lean_array_uget(v_bs_1741_, v_i_1740_);
v___x_1744_ = lean_unsigned_to_nat(0u);
v_bs_x27_1745_ = lean_array_uset(v_bs_1741_, v_i_1740_, v___x_1744_);
v___x_1746_ = 0;
v___x_1747_ = lean_box(v___x_1746_);
v___x_1748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
lean_ctor_set(v___x_1748_, 1, v_v_1743_);
v___x_1749_ = ((size_t)1ULL);
v___x_1750_ = lean_usize_add(v_i_1740_, v___x_1749_);
v___x_1751_ = lean_array_uset(v_bs_x27_1745_, v_i_1740_, v___x_1748_);
v_i_1740_ = v___x_1750_;
v_bs_1741_ = v___x_1751_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8___boxed(lean_object* v_sz_1753_, lean_object* v_i_1754_, lean_object* v_bs_1755_){
_start:
{
size_t v_sz_boxed_1756_; size_t v_i_boxed_1757_; lean_object* v_res_1758_; 
v_sz_boxed_1756_ = lean_unbox_usize(v_sz_1753_);
lean_dec(v_sz_1753_);
v_i_boxed_1757_ = lean_unbox_usize(v_i_1754_);
lean_dec(v_i_1754_);
v_res_1758_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_boxed_1756_, v_i_boxed_1757_, v_bs_1755_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(lean_object* v___x_1759_, lean_object* v_original_1760_, lean_object* v_a_1761_){
_start:
{
lean_object* v_fst_1762_; lean_object* v_snd_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1782_; 
v_fst_1762_ = lean_ctor_get(v_a_1761_, 0);
v_snd_1763_ = lean_ctor_get(v_a_1761_, 1);
v_isSharedCheck_1782_ = !lean_is_exclusive(v_a_1761_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1765_ = v_a_1761_;
v_isShared_1766_ = v_isSharedCheck_1782_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_snd_1763_);
lean_inc(v_fst_1762_);
lean_dec(v_a_1761_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1782_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
uint8_t v___x_1767_; 
v___x_1767_ = lean_nat_dec_lt(v_snd_1763_, v___x_1759_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1769_; 
if (v_isShared_1766_ == 0)
{
v___x_1769_ = v___x_1765_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_fst_1762_);
lean_ctor_set(v_reuseFailAlloc_1770_, 1, v_snd_1763_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
else
{
uint8_t v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1775_; 
v___x_1771_ = 1;
v___x_1772_ = lean_array_fget_borrowed(v_original_1760_, v_snd_1763_);
v___x_1773_ = lean_box(v___x_1771_);
lean_inc(v___x_1772_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 1, v___x_1772_);
lean_ctor_set(v___x_1765_, 0, v___x_1773_);
v___x_1775_ = v___x_1765_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v___x_1773_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v___x_1772_);
v___x_1775_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1776_ = lean_array_push(v_fst_1762_, v___x_1775_);
v___x_1777_ = lean_unsigned_to_nat(1u);
v___x_1778_ = lean_nat_add(v_snd_1763_, v___x_1777_);
lean_dec(v_snd_1763_);
v___x_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1779_, 0, v___x_1776_);
lean_ctor_set(v___x_1779_, 1, v___x_1778_);
v_a_1761_ = v___x_1779_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg___boxed(lean_object* v___x_1783_, lean_object* v_original_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_1783_, v_original_1784_, v_a_1785_);
lean_dec_ref(v_original_1784_);
lean_dec(v___x_1783_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(lean_object* v___x_1787_, lean_object* v_edited_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v_fst_1790_; lean_object* v_snd_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1810_; 
v_fst_1790_ = lean_ctor_get(v_a_1789_, 0);
v_snd_1791_ = lean_ctor_get(v_a_1789_, 1);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_a_1789_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1793_ = v_a_1789_;
v_isShared_1794_ = v_isSharedCheck_1810_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_snd_1791_);
lean_inc(v_fst_1790_);
lean_dec(v_a_1789_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1810_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
uint8_t v___x_1795_; 
v___x_1795_ = lean_nat_dec_lt(v_snd_1791_, v___x_1787_);
if (v___x_1795_ == 0)
{
lean_object* v___x_1797_; 
if (v_isShared_1794_ == 0)
{
v___x_1797_ = v___x_1793_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_fst_1790_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_snd_1791_);
v___x_1797_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
return v___x_1797_;
}
}
else
{
uint8_t v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1803_; 
v___x_1799_ = 0;
v___x_1800_ = lean_array_fget_borrowed(v_edited_1788_, v_snd_1791_);
v___x_1801_ = lean_box(v___x_1799_);
lean_inc(v___x_1800_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 1, v___x_1800_);
lean_ctor_set(v___x_1793_, 0, v___x_1801_);
v___x_1803_ = v___x_1793_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1801_);
lean_ctor_set(v_reuseFailAlloc_1809_, 1, v___x_1800_);
v___x_1803_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1804_ = lean_array_push(v_fst_1790_, v___x_1803_);
v___x_1805_ = lean_unsigned_to_nat(1u);
v___x_1806_ = lean_nat_add(v_snd_1791_, v___x_1805_);
lean_dec(v_snd_1791_);
v___x_1807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1804_);
lean_ctor_set(v___x_1807_, 1, v___x_1806_);
v_a_1789_ = v___x_1807_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg___boxed(lean_object* v___x_1811_, lean_object* v_edited_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_1811_, v_edited_1812_, v_a_1813_);
lean_dec_ref(v_edited_1812_);
lean_dec(v___x_1811_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(lean_object* v_original_1815_, lean_object* v___x_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v_fst_1819_; lean_object* v_snd_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1845_; 
v_fst_1819_ = lean_ctor_get(v_a_1818_, 0);
v_snd_1820_ = lean_ctor_get(v_a_1818_, 1);
v_isSharedCheck_1845_ = !lean_is_exclusive(v_a_1818_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1822_ = v_a_1818_;
v_isShared_1823_ = v_isSharedCheck_1845_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_snd_1820_);
lean_inc(v_fst_1819_);
lean_dec(v_a_1818_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1845_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; uint8_t v___y_1826_; uint8_t v___x_1841_; 
v___x_1824_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_1841_ = lean_nat_dec_lt(v_snd_1820_, v___x_1816_);
if (v___x_1841_ == 0)
{
v___y_1826_ = v___x_1841_;
goto v___jp_1825_;
}
else
{
lean_object* v___x_1842_; uint8_t v___x_1843_; uint8_t v___x_1844_; 
v___x_1842_ = lean_array_get_borrowed(v___x_1824_, v_original_1815_, v_snd_1820_);
v___x_1843_ = lean_string_dec_eq(v___x_1842_, v_a_1817_);
v___x_1844_ = lean_bool_not(v___x_1843_);
v___y_1826_ = v___x_1844_;
goto v___jp_1825_;
}
v___jp_1825_:
{
if (v___y_1826_ == 0)
{
lean_object* v___x_1828_; 
if (v_isShared_1823_ == 0)
{
v___x_1828_ = v___x_1822_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_fst_1819_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_snd_1820_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
else
{
uint8_t v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1834_; 
v___x_1830_ = 1;
v___x_1831_ = lean_array_get_borrowed(v___x_1824_, v_original_1815_, v_snd_1820_);
v___x_1832_ = lean_box(v___x_1830_);
lean_inc(v___x_1831_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 1, v___x_1831_);
lean_ctor_set(v___x_1822_, 0, v___x_1832_);
v___x_1834_ = v___x_1822_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1832_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v___x_1831_);
v___x_1834_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1835_ = lean_array_push(v_fst_1819_, v___x_1834_);
v___x_1836_ = lean_unsigned_to_nat(1u);
v___x_1837_ = lean_nat_add(v_snd_1820_, v___x_1836_);
lean_dec(v_snd_1820_);
v___x_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1835_);
lean_ctor_set(v___x_1838_, 1, v___x_1837_);
v_a_1818_ = v___x_1838_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg___boxed(lean_object* v_original_1846_, lean_object* v___x_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v_original_1846_, v___x_1847_, v_a_1848_, v_a_1849_);
lean_dec_ref(v_a_1848_);
lean_dec(v___x_1847_);
lean_dec_ref(v_original_1846_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(lean_object* v_edited_1851_, lean_object* v___x_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_){
_start:
{
lean_object* v_fst_1855_; lean_object* v_snd_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1881_; 
v_fst_1855_ = lean_ctor_get(v_a_1854_, 0);
v_snd_1856_ = lean_ctor_get(v_a_1854_, 1);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_a_1854_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1858_ = v_a_1854_;
v_isShared_1859_ = v_isSharedCheck_1881_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_snd_1856_);
lean_inc(v_fst_1855_);
lean_dec(v_a_1854_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1881_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; uint8_t v___y_1862_; uint8_t v___x_1877_; 
v___x_1860_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_1877_ = lean_nat_dec_lt(v_snd_1856_, v___x_1852_);
if (v___x_1877_ == 0)
{
v___y_1862_ = v___x_1877_;
goto v___jp_1861_;
}
else
{
lean_object* v___x_1878_; uint8_t v___x_1879_; uint8_t v___x_1880_; 
v___x_1878_ = lean_array_get_borrowed(v___x_1860_, v_edited_1851_, v_snd_1856_);
v___x_1879_ = lean_string_dec_eq(v___x_1878_, v_a_1853_);
v___x_1880_ = lean_bool_not(v___x_1879_);
v___y_1862_ = v___x_1880_;
goto v___jp_1861_;
}
v___jp_1861_:
{
if (v___y_1862_ == 0)
{
lean_object* v___x_1864_; 
if (v_isShared_1859_ == 0)
{
v___x_1864_ = v___x_1858_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_fst_1855_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v_snd_1856_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
else
{
uint8_t v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1870_; 
v___x_1866_ = 0;
v___x_1867_ = lean_array_get_borrowed(v___x_1860_, v_edited_1851_, v_snd_1856_);
v___x_1868_ = lean_box(v___x_1866_);
lean_inc(v___x_1867_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 1, v___x_1867_);
lean_ctor_set(v___x_1858_, 0, v___x_1868_);
v___x_1870_ = v___x_1858_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v___x_1868_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v___x_1867_);
v___x_1870_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1871_ = lean_array_push(v_fst_1855_, v___x_1870_);
v___x_1872_ = lean_unsigned_to_nat(1u);
v___x_1873_ = lean_nat_add(v_snd_1856_, v___x_1872_);
lean_dec(v_snd_1856_);
v___x_1874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1871_);
lean_ctor_set(v___x_1874_, 1, v___x_1873_);
v_a_1854_ = v___x_1874_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg___boxed(lean_object* v_edited_1882_, lean_object* v___x_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(v_edited_1882_, v___x_1883_, v_a_1884_, v_a_1885_);
lean_dec_ref(v_a_1884_);
lean_dec(v___x_1883_);
lean_dec_ref(v_edited_1882_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(lean_object* v_original_1887_, lean_object* v___x_1888_, lean_object* v_edited_1889_, lean_object* v___x_1890_, lean_object* v_as_1891_, size_t v_sz_1892_, size_t v_i_1893_, lean_object* v_b_1894_){
_start:
{
uint8_t v___x_1895_; 
v___x_1895_ = lean_usize_dec_lt(v_i_1893_, v_sz_1892_);
if (v___x_1895_ == 0)
{
return v_b_1894_;
}
else
{
lean_object* v_snd_1896_; lean_object* v_fst_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1944_; 
v_snd_1896_ = lean_ctor_get(v_b_1894_, 1);
v_fst_1897_ = lean_ctor_get(v_b_1894_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v_b_1894_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1899_ = v_b_1894_;
v_isShared_1900_ = v_isSharedCheck_1944_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_snd_1896_);
lean_inc(v_fst_1897_);
lean_dec(v_b_1894_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1944_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v_fst_1901_; lean_object* v_snd_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1943_; 
v_fst_1901_ = lean_ctor_get(v_snd_1896_, 0);
v_snd_1902_ = lean_ctor_get(v_snd_1896_, 1);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_snd_1896_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1904_ = v_snd_1896_;
v_isShared_1905_ = v_isSharedCheck_1943_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_snd_1902_);
lean_inc(v_fst_1901_);
lean_dec(v_snd_1896_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1943_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v_a_1906_; lean_object* v___x_1908_; 
v_a_1906_ = lean_array_uget_borrowed(v_as_1891_, v_i_1893_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 1, v_fst_1901_);
lean_ctor_set(v___x_1904_, 0, v_fst_1897_);
v___x_1908_ = v___x_1904_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_fst_1897_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v_fst_1901_);
v___x_1908_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
lean_object* v___x_1909_; lean_object* v_fst_1910_; lean_object* v_snd_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1941_; 
v___x_1909_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v_original_1887_, v___x_1888_, v_a_1906_, v___x_1908_);
v_fst_1910_ = lean_ctor_get(v___x_1909_, 0);
v_snd_1911_ = lean_ctor_get(v___x_1909_, 1);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1913_ = v___x_1909_;
v_isShared_1914_ = v_isSharedCheck_1941_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_snd_1911_);
lean_inc(v_fst_1910_);
lean_dec(v___x_1909_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1941_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 1, v_snd_1902_);
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_fst_1910_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_snd_1902_);
v___x_1916_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1917_; lean_object* v_fst_1918_; lean_object* v_snd_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1939_; 
v___x_1917_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(v_edited_1889_, v___x_1890_, v_a_1906_, v___x_1916_);
v_fst_1918_ = lean_ctor_get(v___x_1917_, 0);
v_snd_1919_ = lean_ctor_get(v___x_1917_, 1);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1921_ = v___x_1917_;
v_isShared_1922_ = v_isSharedCheck_1939_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_snd_1919_);
lean_inc(v_fst_1918_);
lean_dec(v___x_1917_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1939_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
uint8_t v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1926_; 
v___x_1923_ = 2;
v___x_1924_ = lean_box(v___x_1923_);
lean_inc(v_a_1906_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 1, v_a_1906_);
lean_ctor_set(v___x_1921_, 0, v___x_1924_);
v___x_1926_ = v___x_1921_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v___x_1924_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_a_1906_);
v___x_1926_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1932_; 
v___x_1927_ = lean_array_push(v_fst_1918_, v___x_1926_);
v___x_1928_ = lean_unsigned_to_nat(1u);
v___x_1929_ = lean_nat_add(v_snd_1911_, v___x_1928_);
lean_dec(v_snd_1911_);
v___x_1930_ = lean_nat_add(v_snd_1919_, v___x_1928_);
lean_dec(v_snd_1919_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 1, v___x_1930_);
lean_ctor_set(v___x_1899_, 0, v___x_1929_);
v___x_1932_ = v___x_1899_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1929_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v___x_1930_);
v___x_1932_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1933_; size_t v___x_1934_; size_t v___x_1935_; 
v___x_1933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1927_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = ((size_t)1ULL);
v___x_1935_ = lean_usize_add(v_i_1893_, v___x_1934_);
v_i_1893_ = v___x_1935_;
v_b_1894_ = v___x_1933_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14___boxed(lean_object* v_original_1945_, lean_object* v___x_1946_, lean_object* v_edited_1947_, lean_object* v___x_1948_, lean_object* v_as_1949_, lean_object* v_sz_1950_, lean_object* v_i_1951_, lean_object* v_b_1952_){
_start:
{
size_t v_sz_boxed_1953_; size_t v_i_boxed_1954_; lean_object* v_res_1955_; 
v_sz_boxed_1953_ = lean_unbox_usize(v_sz_1950_);
lean_dec(v_sz_1950_);
v_i_boxed_1954_ = lean_unbox_usize(v_i_1951_);
lean_dec(v_i_1951_);
v_res_1955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v_original_1945_, v___x_1946_, v_edited_1947_, v___x_1948_, v_as_1949_, v_sz_boxed_1953_, v_i_boxed_1954_, v_b_1952_);
lean_dec_ref(v_as_1949_);
lean_dec(v___x_1948_);
lean_dec_ref(v_edited_1947_);
lean_dec(v___x_1946_);
lean_dec_ref(v_original_1945_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(lean_object* v_edited_1956_, lean_object* v___x_1957_, lean_object* v_original_1958_, lean_object* v___x_1959_, lean_object* v_as_1960_, size_t v_sz_1961_, size_t v_i_1962_, lean_object* v_b_1963_){
_start:
{
uint8_t v___x_1964_; 
v___x_1964_ = lean_usize_dec_lt(v_i_1962_, v_sz_1961_);
if (v___x_1964_ == 0)
{
return v_b_1963_;
}
else
{
lean_object* v_snd_1965_; lean_object* v_fst_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_2013_; 
v_snd_1965_ = lean_ctor_get(v_b_1963_, 1);
v_fst_1966_ = lean_ctor_get(v_b_1963_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v_b_1963_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_1968_ = v_b_1963_;
v_isShared_1969_ = v_isSharedCheck_2013_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_snd_1965_);
lean_inc(v_fst_1966_);
lean_dec(v_b_1963_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_2013_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v_fst_1970_; lean_object* v_snd_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_2012_; 
v_fst_1970_ = lean_ctor_get(v_snd_1965_, 0);
v_snd_1971_ = lean_ctor_get(v_snd_1965_, 1);
v_isSharedCheck_2012_ = !lean_is_exclusive(v_snd_1965_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_1973_ = v_snd_1965_;
v_isShared_1974_ = v_isSharedCheck_2012_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_snd_1971_);
lean_inc(v_fst_1970_);
lean_dec(v_snd_1965_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_2012_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v_a_1975_; lean_object* v___x_1977_; 
v_a_1975_ = lean_array_uget_borrowed(v_as_1960_, v_i_1962_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 1, v_fst_1970_);
lean_ctor_set(v___x_1973_, 0, v_fst_1966_);
v___x_1977_ = v___x_1973_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_fst_1966_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v_fst_1970_);
v___x_1977_ = v_reuseFailAlloc_2011_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
lean_object* v___x_1978_; lean_object* v_fst_1979_; lean_object* v_snd_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_2010_; 
v___x_1978_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v_original_1958_, v___x_1959_, v_a_1975_, v___x_1977_);
v_fst_1979_ = lean_ctor_get(v___x_1978_, 0);
v_snd_1980_ = lean_ctor_get(v___x_1978_, 1);
v_isSharedCheck_2010_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1982_ = v___x_1978_;
v_isShared_1983_ = v_isSharedCheck_2010_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_snd_1980_);
lean_inc(v_fst_1979_);
lean_dec(v___x_1978_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_2010_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 1, v_snd_1971_);
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_fst_1979_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_snd_1971_);
v___x_1985_ = v_reuseFailAlloc_2009_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
lean_object* v___x_1986_; lean_object* v_fst_1987_; lean_object* v_snd_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_2008_; 
v___x_1986_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(v_edited_1956_, v___x_1957_, v_a_1975_, v___x_1985_);
v_fst_1987_ = lean_ctor_get(v___x_1986_, 0);
v_snd_1988_ = lean_ctor_get(v___x_1986_, 1);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_1990_ = v___x_1986_;
v_isShared_1991_ = v_isSharedCheck_2008_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_snd_1988_);
lean_inc(v_fst_1987_);
lean_dec(v___x_1986_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_2008_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
uint8_t v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1992_ = 2;
v___x_1993_ = lean_box(v___x_1992_);
lean_inc(v_a_1975_);
if (v_isShared_1991_ == 0)
{
lean_ctor_set(v___x_1990_, 1, v_a_1975_);
lean_ctor_set(v___x_1990_, 0, v___x_1993_);
v___x_1995_ = v___x_1990_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_1993_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v_a_1975_);
v___x_1995_ = v_reuseFailAlloc_2007_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2001_; 
v___x_1996_ = lean_array_push(v_fst_1987_, v___x_1995_);
v___x_1997_ = lean_unsigned_to_nat(1u);
v___x_1998_ = lean_nat_add(v_snd_1980_, v___x_1997_);
lean_dec(v_snd_1980_);
v___x_1999_ = lean_nat_add(v_snd_1988_, v___x_1997_);
lean_dec(v_snd_1988_);
if (v_isShared_1969_ == 0)
{
lean_ctor_set(v___x_1968_, 1, v___x_1999_);
lean_ctor_set(v___x_1968_, 0, v___x_1998_);
v___x_2001_ = v___x_1968_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_1998_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2002_; size_t v___x_2003_; size_t v___x_2004_; lean_object* v___x_2005_; 
v___x_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_1996_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
v___x_2003_ = ((size_t)1ULL);
v___x_2004_ = lean_usize_add(v_i_1962_, v___x_2003_);
v___x_2005_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v_original_1958_, v___x_1959_, v_edited_1956_, v___x_1957_, v_as_1960_, v_sz_1961_, v___x_2004_, v___x_2002_);
return v___x_2005_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4___boxed(lean_object* v_edited_2014_, lean_object* v___x_2015_, lean_object* v_original_2016_, lean_object* v___x_2017_, lean_object* v_as_2018_, lean_object* v_sz_2019_, lean_object* v_i_2020_, lean_object* v_b_2021_){
_start:
{
size_t v_sz_boxed_2022_; size_t v_i_boxed_2023_; lean_object* v_res_2024_; 
v_sz_boxed_2022_ = lean_unbox_usize(v_sz_2019_);
lean_dec(v_sz_2019_);
v_i_boxed_2023_ = lean_unbox_usize(v_i_2020_);
lean_dec(v_i_2020_);
v_res_2024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v_edited_2014_, v___x_2015_, v_original_2016_, v___x_2017_, v_as_2018_, v_sz_boxed_2022_, v_i_boxed_2023_, v_b_2021_);
lean_dec_ref(v_as_2018_);
lean_dec(v___x_2017_);
lean_dec_ref(v_original_2016_);
lean_dec(v___x_2015_);
lean_dec_ref(v_edited_2014_);
return v_res_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(lean_object* v_a_2025_, lean_object* v_b_2026_){
_start:
{
lean_object* v_array_2027_; lean_object* v_start_2028_; lean_object* v_stop_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2042_; 
v_array_2027_ = lean_ctor_get(v_a_2025_, 0);
v_start_2028_ = lean_ctor_get(v_a_2025_, 1);
v_stop_2029_ = lean_ctor_get(v_a_2025_, 2);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_a_2025_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2031_ = v_a_2025_;
v_isShared_2032_ = v_isSharedCheck_2042_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_stop_2029_);
lean_inc(v_start_2028_);
lean_inc(v_array_2027_);
lean_dec(v_a_2025_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2042_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
uint8_t v___x_2033_; 
v___x_2033_ = lean_nat_dec_lt(v_start_2028_, v_stop_2029_);
if (v___x_2033_ == 0)
{
lean_del_object(v___x_2031_);
lean_dec(v_stop_2029_);
lean_dec(v_start_2028_);
lean_dec_ref(v_array_2027_);
return v_b_2026_;
}
else
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
v___x_2034_ = lean_unsigned_to_nat(1u);
v___x_2035_ = lean_nat_add(v_start_2028_, v___x_2034_);
lean_inc_ref(v_array_2027_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 1, v___x_2035_);
v___x_2037_ = v___x_2031_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_array_2027_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2041_, 2, v_stop_2029_);
v___x_2037_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = lean_array_fget(v_array_2027_, v_start_2028_);
lean_dec(v_start_2028_);
lean_dec_ref(v_array_2027_);
v___x_2039_ = lean_array_push(v_b_2026_, v___x_2038_);
v_a_2025_ = v___x_2037_;
v_b_2026_ = v___x_2039_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6(lean_object* v_left_2043_, lean_object* v_right_2044_, lean_object* v_i_2045_){
_start:
{
lean_object* v_start_2046_; lean_object* v_stop_2047_; lean_object* v___x_2048_; uint8_t v___x_2062_; 
v_start_2046_ = lean_ctor_get(v_left_2043_, 1);
v_stop_2047_ = lean_ctor_get(v_left_2043_, 2);
v___x_2048_ = lean_nat_sub(v_stop_2047_, v_start_2046_);
v___x_2062_ = lean_nat_dec_lt(v_i_2045_, v___x_2048_);
if (v___x_2062_ == 0)
{
goto v___jp_2049_;
}
else
{
lean_object* v_start_2063_; lean_object* v_stop_2064_; lean_object* v___x_2065_; uint8_t v___x_2066_; 
v_start_2063_ = lean_ctor_get(v_right_2044_, 1);
v_stop_2064_ = lean_ctor_get(v_right_2044_, 2);
v___x_2065_ = lean_nat_sub(v_stop_2064_, v_start_2063_);
v___x_2066_ = lean_nat_dec_lt(v_i_2045_, v___x_2065_);
if (v___x_2066_ == 0)
{
lean_dec(v___x_2065_);
goto v___jp_2049_;
}
else
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; 
v___x_2067_ = lean_nat_sub(v___x_2048_, v_i_2045_);
lean_dec(v___x_2048_);
v___x_2068_ = lean_unsigned_to_nat(1u);
v___x_2069_ = lean_nat_sub(v___x_2067_, v___x_2068_);
v___x_2070_ = l_Subarray_get___redArg(v_left_2043_, v___x_2069_);
lean_dec(v___x_2069_);
v___x_2071_ = lean_nat_sub(v___x_2065_, v_i_2045_);
lean_dec(v___x_2065_);
v___x_2072_ = lean_nat_sub(v___x_2071_, v___x_2068_);
v___x_2073_ = l_Subarray_get___redArg(v_right_2044_, v___x_2072_);
lean_dec(v___x_2072_);
v___x_2074_ = lean_string_dec_eq(v___x_2070_, v___x_2073_);
lean_dec(v___x_2073_);
lean_dec(v___x_2070_);
if (v___x_2074_ == 0)
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
lean_dec(v_i_2045_);
lean_inc_ref(v_left_2043_);
v___x_2075_ = l_Subarray_take___redArg(v_left_2043_, v___x_2067_);
v___x_2076_ = l_Subarray_take___redArg(v_right_2044_, v___x_2071_);
lean_dec(v___x_2071_);
v___x_2077_ = l_Subarray_drop___redArg(v_left_2043_, v___x_2067_);
lean_dec(v___x_2067_);
v___x_2078_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2079_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v___x_2077_, v___x_2078_);
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2076_);
lean_ctor_set(v___x_2080_, 1, v___x_2079_);
v___x_2081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2081_, 0, v___x_2075_);
lean_ctor_set(v___x_2081_, 1, v___x_2080_);
return v___x_2081_;
}
else
{
lean_object* v___x_2082_; 
lean_dec(v___x_2071_);
lean_dec(v___x_2067_);
v___x_2082_ = lean_nat_add(v_i_2045_, v___x_2068_);
lean_dec(v_i_2045_);
v_i_2045_ = v___x_2082_;
goto _start;
}
}
}
v___jp_2049_:
{
lean_object* v_start_2050_; lean_object* v_stop_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v_start_2050_ = lean_ctor_get(v_right_2044_, 1);
v_stop_2051_ = lean_ctor_get(v_right_2044_, 2);
v___x_2052_ = lean_nat_sub(v___x_2048_, v_i_2045_);
lean_dec(v___x_2048_);
lean_inc_ref(v_left_2043_);
v___x_2053_ = l_Subarray_take___redArg(v_left_2043_, v___x_2052_);
v___x_2054_ = lean_nat_sub(v_stop_2051_, v_start_2050_);
v___x_2055_ = lean_nat_sub(v___x_2054_, v_i_2045_);
lean_dec(v_i_2045_);
lean_dec(v___x_2054_);
v___x_2056_ = l_Subarray_take___redArg(v_right_2044_, v___x_2055_);
lean_dec(v___x_2055_);
v___x_2057_ = l_Subarray_drop___redArg(v_left_2043_, v___x_2052_);
lean_dec(v___x_2052_);
v___x_2058_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2059_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v___x_2057_, v___x_2058_);
v___x_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2056_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
v___x_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2053_);
lean_ctor_set(v___x_2061_, 1, v___x_2060_);
return v___x_2061_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3(lean_object* v_left_2084_, lean_object* v_right_2085_){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2086_ = lean_unsigned_to_nat(0u);
v___x_2087_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6(v_left_2084_, v_right_2085_, v___x_2086_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2_spec__4(lean_object* v_left_2088_, lean_object* v_right_2089_, lean_object* v_pref_2090_){
_start:
{
lean_object* v_start_2091_; lean_object* v_stop_2092_; lean_object* v_i_2093_; lean_object* v___x_2099_; uint8_t v___x_2100_; 
v_start_2091_ = lean_ctor_get(v_left_2088_, 1);
v_stop_2092_ = lean_ctor_get(v_left_2088_, 2);
v_i_2093_ = lean_array_get_size(v_pref_2090_);
v___x_2099_ = lean_nat_sub(v_stop_2092_, v_start_2091_);
v___x_2100_ = lean_nat_dec_lt(v_i_2093_, v___x_2099_);
lean_dec(v___x_2099_);
if (v___x_2100_ == 0)
{
goto v___jp_2094_;
}
else
{
lean_object* v_start_2101_; lean_object* v_stop_2102_; lean_object* v___x_2103_; uint8_t v___x_2104_; 
v_start_2101_ = lean_ctor_get(v_right_2089_, 1);
v_stop_2102_ = lean_ctor_get(v_right_2089_, 2);
v___x_2103_ = lean_nat_sub(v_stop_2102_, v_start_2101_);
v___x_2104_ = lean_nat_dec_lt(v_i_2093_, v___x_2103_);
lean_dec(v___x_2103_);
if (v___x_2104_ == 0)
{
goto v___jp_2094_;
}
else
{
lean_object* v___x_2105_; lean_object* v___x_2106_; uint8_t v___x_2107_; 
v___x_2105_ = l_Subarray_get___redArg(v_left_2088_, v_i_2093_);
v___x_2106_ = l_Subarray_get___redArg(v_right_2089_, v_i_2093_);
v___x_2107_ = lean_string_dec_eq(v___x_2105_, v___x_2106_);
lean_dec(v___x_2106_);
if (v___x_2107_ == 0)
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
lean_dec(v___x_2105_);
v___x_2108_ = l_Subarray_drop___redArg(v_left_2088_, v_i_2093_);
v___x_2109_ = l_Subarray_drop___redArg(v_right_2089_, v_i_2093_);
v___x_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2108_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
v___x_2111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2111_, 0, v_pref_2090_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
return v___x_2111_;
}
else
{
lean_object* v___x_2112_; 
v___x_2112_ = lean_array_push(v_pref_2090_, v___x_2105_);
v_pref_2090_ = v___x_2112_;
goto _start;
}
}
}
v___jp_2094_:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2095_ = l_Subarray_drop___redArg(v_left_2088_, v_i_2093_);
v___x_2096_ = l_Subarray_drop___redArg(v_right_2089_, v_i_2093_);
v___x_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2095_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
v___x_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2098_, 0, v_pref_2090_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
return v___x_2098_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2(lean_object* v_left_2114_, lean_object* v_right_2115_){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2117_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2_spec__4(v_left_2114_, v_right_2115_, v___x_2116_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(lean_object* v_as_x27_2118_, lean_object* v_b_2119_){
_start:
{
if (lean_obj_tag(v_as_x27_2118_) == 0)
{
return v_b_2119_;
}
else
{
lean_object* v_head_2120_; lean_object* v_snd_2121_; lean_object* v_leftIndex_2122_; 
v_head_2120_ = lean_ctor_get(v_as_x27_2118_, 0);
v_snd_2121_ = lean_ctor_get(v_head_2120_, 1);
v_leftIndex_2122_ = lean_ctor_get(v_snd_2121_, 1);
if (lean_obj_tag(v_leftIndex_2122_) == 1)
{
lean_object* v_rightIndex_2123_; 
v_rightIndex_2123_ = lean_ctor_get(v_snd_2121_, 3);
if (lean_obj_tag(v_rightIndex_2123_) == 1)
{
if (lean_obj_tag(v_b_2119_) == 0)
{
lean_object* v_tail_2124_; lean_object* v_fst_2125_; lean_object* v_leftCount_2126_; lean_object* v_rightCount_2127_; lean_object* v_val_2128_; lean_object* v_val_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v_tail_2124_ = lean_ctor_get(v_as_x27_2118_, 1);
v_fst_2125_ = lean_ctor_get(v_head_2120_, 0);
v_leftCount_2126_ = lean_ctor_get(v_snd_2121_, 0);
v_rightCount_2127_ = lean_ctor_get(v_snd_2121_, 2);
v_val_2128_ = lean_ctor_get(v_leftIndex_2122_, 0);
v_val_2129_ = lean_ctor_get(v_rightIndex_2123_, 0);
v___x_2130_ = lean_nat_add(v_leftCount_2126_, v_rightCount_2127_);
lean_inc(v_val_2129_);
lean_inc(v_val_2128_);
v___x_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2131_, 0, v_val_2128_);
lean_ctor_set(v___x_2131_, 1, v_val_2129_);
lean_inc(v_fst_2125_);
v___x_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2132_, 0, v_fst_2125_);
lean_ctor_set(v___x_2132_, 1, v___x_2131_);
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2130_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
v_as_x27_2118_ = v_tail_2124_;
v_b_2119_ = v___x_2134_;
goto _start;
}
else
{
lean_object* v_val_2136_; lean_object* v_tail_2137_; lean_object* v_fst_2138_; lean_object* v_leftCount_2139_; lean_object* v_rightCount_2140_; lean_object* v_val_2141_; lean_object* v_val_2142_; lean_object* v_fst_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2164_; 
v_val_2136_ = lean_ctor_get(v_b_2119_, 0);
lean_inc(v_val_2136_);
v_tail_2137_ = lean_ctor_get(v_as_x27_2118_, 1);
v_fst_2138_ = lean_ctor_get(v_head_2120_, 0);
v_leftCount_2139_ = lean_ctor_get(v_snd_2121_, 0);
v_rightCount_2140_ = lean_ctor_get(v_snd_2121_, 2);
v_val_2141_ = lean_ctor_get(v_leftIndex_2122_, 0);
v_val_2142_ = lean_ctor_get(v_rightIndex_2123_, 0);
v_fst_2143_ = lean_ctor_get(v_val_2136_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_val_2136_);
if (v_isSharedCheck_2164_ == 0)
{
lean_object* v_unused_2165_; 
v_unused_2165_ = lean_ctor_get(v_val_2136_, 1);
lean_dec(v_unused_2165_);
v___x_2145_ = v_val_2136_;
v_isShared_2146_ = v_isSharedCheck_2164_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_fst_2143_);
lean_dec(v_val_2136_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2164_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2147_; uint8_t v___x_2148_; 
v___x_2147_ = lean_nat_add(v_leftCount_2139_, v_rightCount_2140_);
v___x_2148_ = lean_nat_dec_lt(v___x_2147_, v_fst_2143_);
lean_dec(v_fst_2143_);
if (v___x_2148_ == 0)
{
lean_dec(v___x_2147_);
lean_del_object(v___x_2145_);
v_as_x27_2118_ = v_tail_2137_;
goto _start;
}
else
{
lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2162_; 
v_isSharedCheck_2162_ = !lean_is_exclusive(v_b_2119_);
if (v_isSharedCheck_2162_ == 0)
{
lean_object* v_unused_2163_; 
v_unused_2163_ = lean_ctor_get(v_b_2119_, 0);
lean_dec(v_unused_2163_);
v___x_2151_ = v_b_2119_;
v_isShared_2152_ = v_isSharedCheck_2162_;
goto v_resetjp_2150_;
}
else
{
lean_dec(v_b_2119_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2162_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
lean_inc(v_val_2142_);
lean_inc(v_val_2141_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 1, v_val_2142_);
lean_ctor_set(v___x_2145_, 0, v_val_2141_);
v___x_2154_ = v___x_2145_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_val_2141_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_val_2142_);
v___x_2154_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2158_; 
lean_inc(v_fst_2138_);
v___x_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2155_, 0, v_fst_2138_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
v___x_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2147_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 0, v___x_2156_);
v___x_2158_ = v___x_2151_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
v_as_x27_2118_ = v_tail_2137_;
v_b_2119_ = v___x_2158_;
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
lean_object* v_tail_2166_; 
v_tail_2166_ = lean_ctor_get(v_as_x27_2118_, 1);
v_as_x27_2118_ = v_tail_2166_;
goto _start;
}
}
else
{
lean_object* v_tail_2168_; 
v_tail_2168_ = lean_ctor_get(v_as_x27_2118_, 1);
v_as_x27_2118_ = v_tail_2168_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg___boxed(lean_object* v_as_x27_2170_, lean_object* v_b_2171_){
_start:
{
lean_object* v_res_2172_; 
v_res_2172_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(v_as_x27_2170_, v_b_2171_);
lean_dec(v_as_x27_2170_);
return v_res_2172_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(lean_object* v_a_2173_, lean_object* v_b_2174_, lean_object* v_x_2175_){
_start:
{
if (lean_obj_tag(v_x_2175_) == 0)
{
lean_dec(v_b_2174_);
lean_dec_ref(v_a_2173_);
return v_x_2175_;
}
else
{
lean_object* v_key_2176_; lean_object* v_value_2177_; lean_object* v_tail_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2190_; 
v_key_2176_ = lean_ctor_get(v_x_2175_, 0);
v_value_2177_ = lean_ctor_get(v_x_2175_, 1);
v_tail_2178_ = lean_ctor_get(v_x_2175_, 2);
v_isSharedCheck_2190_ = !lean_is_exclusive(v_x_2175_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2180_ = v_x_2175_;
v_isShared_2181_ = v_isSharedCheck_2190_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_tail_2178_);
lean_inc(v_value_2177_);
lean_inc(v_key_2176_);
lean_dec(v_x_2175_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2190_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
uint8_t v___x_2182_; 
v___x_2182_ = lean_string_dec_eq(v_key_2176_, v_a_2173_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; lean_object* v___x_2185_; 
v___x_2183_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(v_a_2173_, v_b_2174_, v_tail_2178_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 2, v___x_2183_);
v___x_2185_ = v___x_2180_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_key_2176_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_value_2177_);
lean_ctor_set(v_reuseFailAlloc_2186_, 2, v___x_2183_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
else
{
lean_object* v___x_2188_; 
lean_dec(v_value_2177_);
lean_dec(v_key_2176_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 1, v_b_2174_);
lean_ctor_set(v___x_2180_, 0, v_a_2173_);
v___x_2188_ = v___x_2180_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2173_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_b_2174_);
lean_ctor_set(v_reuseFailAlloc_2189_, 2, v_tail_2178_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(lean_object* v_a_2191_, lean_object* v_x_2192_){
_start:
{
if (lean_obj_tag(v_x_2192_) == 0)
{
uint8_t v___x_2193_; 
v___x_2193_ = 0;
return v___x_2193_;
}
else
{
lean_object* v_key_2194_; lean_object* v_tail_2195_; uint8_t v___x_2196_; 
v_key_2194_ = lean_ctor_get(v_x_2192_, 0);
v_tail_2195_ = lean_ctor_get(v_x_2192_, 2);
v___x_2196_ = lean_string_dec_eq(v_key_2194_, v_a_2191_);
if (v___x_2196_ == 0)
{
v_x_2192_ = v_tail_2195_;
goto _start;
}
else
{
return v___x_2196_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg___boxed(lean_object* v_a_2198_, lean_object* v_x_2199_){
_start:
{
uint8_t v_res_2200_; lean_object* v_r_2201_; 
v_res_2200_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(v_a_2198_, v_x_2199_);
lean_dec(v_x_2199_);
lean_dec_ref(v_a_2198_);
v_r_2201_ = lean_box(v_res_2200_);
return v_r_2201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29___redArg(lean_object* v_x_2202_, lean_object* v_x_2203_){
_start:
{
if (lean_obj_tag(v_x_2203_) == 0)
{
return v_x_2202_;
}
else
{
lean_object* v_key_2204_; lean_object* v_value_2205_; lean_object* v_tail_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2229_; 
v_key_2204_ = lean_ctor_get(v_x_2203_, 0);
v_value_2205_ = lean_ctor_get(v_x_2203_, 1);
v_tail_2206_ = lean_ctor_get(v_x_2203_, 2);
v_isSharedCheck_2229_ = !lean_is_exclusive(v_x_2203_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2208_ = v_x_2203_;
v_isShared_2209_ = v_isSharedCheck_2229_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_tail_2206_);
lean_inc(v_value_2205_);
lean_inc(v_key_2204_);
lean_dec(v_x_2203_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2229_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; uint64_t v___x_2211_; uint64_t v___x_2212_; uint64_t v___x_2213_; uint64_t v_fold_2214_; uint64_t v___x_2215_; uint64_t v___x_2216_; uint64_t v___x_2217_; size_t v___x_2218_; size_t v___x_2219_; size_t v___x_2220_; size_t v___x_2221_; size_t v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2225_; 
v___x_2210_ = lean_array_get_size(v_x_2202_);
v___x_2211_ = lean_string_hash(v_key_2204_);
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
v___x_2223_ = lean_array_uget_borrowed(v_x_2202_, v___x_2222_);
lean_inc(v___x_2223_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 2, v___x_2223_);
v___x_2225_ = v___x_2208_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_key_2204_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_value_2205_);
lean_ctor_set(v_reuseFailAlloc_2228_, 2, v___x_2223_);
v___x_2225_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_array_uset(v_x_2202_, v___x_2222_, v___x_2225_);
v_x_2202_ = v___x_2226_;
v_x_2203_ = v_tail_2206_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28___redArg(lean_object* v_i_2230_, lean_object* v_source_2231_, lean_object* v_target_2232_){
_start:
{
lean_object* v___x_2233_; uint8_t v___x_2234_; 
v___x_2233_ = lean_array_get_size(v_source_2231_);
v___x_2234_ = lean_nat_dec_lt(v_i_2230_, v___x_2233_);
if (v___x_2234_ == 0)
{
lean_dec_ref(v_source_2231_);
lean_dec(v_i_2230_);
return v_target_2232_;
}
else
{
lean_object* v_es_2235_; lean_object* v___x_2236_; lean_object* v_source_2237_; lean_object* v_target_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v_es_2235_ = lean_array_fget(v_source_2231_, v_i_2230_);
v___x_2236_ = lean_box(0);
v_source_2237_ = lean_array_fset(v_source_2231_, v_i_2230_, v___x_2236_);
v_target_2238_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29___redArg(v_target_2232_, v_es_2235_);
v___x_2239_ = lean_unsigned_to_nat(1u);
v___x_2240_ = lean_nat_add(v_i_2230_, v___x_2239_);
lean_dec(v_i_2230_);
v_i_2230_ = v___x_2240_;
v_source_2231_ = v_source_2237_;
v_target_2232_ = v_target_2238_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23___redArg(lean_object* v_data_2242_){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v_nbuckets_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2243_ = lean_array_get_size(v_data_2242_);
v___x_2244_ = lean_unsigned_to_nat(2u);
v_nbuckets_2245_ = lean_nat_mul(v___x_2243_, v___x_2244_);
v___x_2246_ = lean_unsigned_to_nat(0u);
v___x_2247_ = lean_box(0);
v___x_2248_ = lean_mk_array(v_nbuckets_2245_, v___x_2247_);
v___x_2249_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28___redArg(v___x_2246_, v_data_2242_, v___x_2248_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(lean_object* v_m_2250_, lean_object* v_a_2251_, lean_object* v_b_2252_){
_start:
{
lean_object* v_size_2253_; lean_object* v_buckets_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2297_; 
v_size_2253_ = lean_ctor_get(v_m_2250_, 0);
v_buckets_2254_ = lean_ctor_get(v_m_2250_, 1);
v_isSharedCheck_2297_ = !lean_is_exclusive(v_m_2250_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2256_ = v_m_2250_;
v_isShared_2257_ = v_isSharedCheck_2297_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_buckets_2254_);
lean_inc(v_size_2253_);
lean_dec(v_m_2250_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2297_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2258_; uint64_t v___x_2259_; uint64_t v___x_2260_; uint64_t v___x_2261_; uint64_t v_fold_2262_; uint64_t v___x_2263_; uint64_t v___x_2264_; uint64_t v___x_2265_; size_t v___x_2266_; size_t v___x_2267_; size_t v___x_2268_; size_t v___x_2269_; size_t v___x_2270_; lean_object* v_bkt_2271_; uint8_t v___x_2272_; 
v___x_2258_ = lean_array_get_size(v_buckets_2254_);
v___x_2259_ = lean_string_hash(v_a_2251_);
v___x_2260_ = 32ULL;
v___x_2261_ = lean_uint64_shift_right(v___x_2259_, v___x_2260_);
v_fold_2262_ = lean_uint64_xor(v___x_2259_, v___x_2261_);
v___x_2263_ = 16ULL;
v___x_2264_ = lean_uint64_shift_right(v_fold_2262_, v___x_2263_);
v___x_2265_ = lean_uint64_xor(v_fold_2262_, v___x_2264_);
v___x_2266_ = lean_uint64_to_usize(v___x_2265_);
v___x_2267_ = lean_usize_of_nat(v___x_2258_);
v___x_2268_ = ((size_t)1ULL);
v___x_2269_ = lean_usize_sub(v___x_2267_, v___x_2268_);
v___x_2270_ = lean_usize_land(v___x_2266_, v___x_2269_);
v_bkt_2271_ = lean_array_uget_borrowed(v_buckets_2254_, v___x_2270_);
v___x_2272_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(v_a_2251_, v_bkt_2271_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2273_; lean_object* v_size_x27_2274_; lean_object* v___x_2275_; lean_object* v_buckets_x27_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; uint8_t v___x_2282_; 
v___x_2273_ = lean_unsigned_to_nat(1u);
v_size_x27_2274_ = lean_nat_add(v_size_2253_, v___x_2273_);
lean_dec(v_size_2253_);
lean_inc(v_bkt_2271_);
v___x_2275_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2275_, 0, v_a_2251_);
lean_ctor_set(v___x_2275_, 1, v_b_2252_);
lean_ctor_set(v___x_2275_, 2, v_bkt_2271_);
v_buckets_x27_2276_ = lean_array_uset(v_buckets_2254_, v___x_2270_, v___x_2275_);
v___x_2277_ = lean_unsigned_to_nat(4u);
v___x_2278_ = lean_nat_mul(v_size_x27_2274_, v___x_2277_);
v___x_2279_ = lean_unsigned_to_nat(3u);
v___x_2280_ = lean_nat_div(v___x_2278_, v___x_2279_);
lean_dec(v___x_2278_);
v___x_2281_ = lean_array_get_size(v_buckets_x27_2276_);
v___x_2282_ = lean_nat_dec_le(v___x_2280_, v___x_2281_);
lean_dec(v___x_2280_);
if (v___x_2282_ == 0)
{
lean_object* v_val_2283_; lean_object* v___x_2285_; 
v_val_2283_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23___redArg(v_buckets_x27_2276_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 1, v_val_2283_);
lean_ctor_set(v___x_2256_, 0, v_size_x27_2274_);
v___x_2285_ = v___x_2256_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_size_x27_2274_);
lean_ctor_set(v_reuseFailAlloc_2286_, 1, v_val_2283_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
else
{
lean_object* v___x_2288_; 
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 1, v_buckets_x27_2276_);
lean_ctor_set(v___x_2256_, 0, v_size_x27_2274_);
v___x_2288_ = v___x_2256_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_size_x27_2274_);
lean_ctor_set(v_reuseFailAlloc_2289_, 1, v_buckets_x27_2276_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
else
{
lean_object* v___x_2290_; lean_object* v_buckets_x27_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2295_; 
lean_inc(v_bkt_2271_);
v___x_2290_ = lean_box(0);
v_buckets_x27_2291_ = lean_array_uset(v_buckets_2254_, v___x_2270_, v___x_2290_);
v___x_2292_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(v_a_2251_, v_b_2252_, v_bkt_2271_);
v___x_2293_ = lean_array_uset(v_buckets_x27_2291_, v___x_2270_, v___x_2292_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 1, v___x_2293_);
v___x_2295_ = v___x_2256_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_size_2253_);
lean_ctor_set(v_reuseFailAlloc_2296_, 1, v___x_2293_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(lean_object* v_a_2298_, lean_object* v_x_2299_){
_start:
{
if (lean_obj_tag(v_x_2299_) == 0)
{
lean_object* v___x_2300_; 
v___x_2300_ = lean_box(0);
return v___x_2300_;
}
else
{
lean_object* v_key_2301_; lean_object* v_value_2302_; lean_object* v_tail_2303_; uint8_t v___x_2304_; 
v_key_2301_ = lean_ctor_get(v_x_2299_, 0);
v_value_2302_ = lean_ctor_get(v_x_2299_, 1);
v_tail_2303_ = lean_ctor_get(v_x_2299_, 2);
v___x_2304_ = lean_string_dec_eq(v_key_2301_, v_a_2298_);
if (v___x_2304_ == 0)
{
v_x_2299_ = v_tail_2303_;
goto _start;
}
else
{
lean_object* v___x_2306_; 
lean_inc(v_value_2302_);
v___x_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2306_, 0, v_value_2302_);
return v___x_2306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg___boxed(lean_object* v_a_2307_, lean_object* v_x_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(v_a_2307_, v_x_2308_);
lean_dec(v_x_2308_);
lean_dec_ref(v_a_2307_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(lean_object* v_m_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v_buckets_2312_; lean_object* v___x_2313_; uint64_t v___x_2314_; uint64_t v___x_2315_; uint64_t v___x_2316_; uint64_t v_fold_2317_; uint64_t v___x_2318_; uint64_t v___x_2319_; uint64_t v___x_2320_; size_t v___x_2321_; size_t v___x_2322_; size_t v___x_2323_; size_t v___x_2324_; size_t v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v_buckets_2312_ = lean_ctor_get(v_m_2310_, 1);
v___x_2313_ = lean_array_get_size(v_buckets_2312_);
v___x_2314_ = lean_string_hash(v_a_2311_);
v___x_2315_ = 32ULL;
v___x_2316_ = lean_uint64_shift_right(v___x_2314_, v___x_2315_);
v_fold_2317_ = lean_uint64_xor(v___x_2314_, v___x_2316_);
v___x_2318_ = 16ULL;
v___x_2319_ = lean_uint64_shift_right(v_fold_2317_, v___x_2318_);
v___x_2320_ = lean_uint64_xor(v_fold_2317_, v___x_2319_);
v___x_2321_ = lean_uint64_to_usize(v___x_2320_);
v___x_2322_ = lean_usize_of_nat(v___x_2313_);
v___x_2323_ = ((size_t)1ULL);
v___x_2324_ = lean_usize_sub(v___x_2322_, v___x_2323_);
v___x_2325_ = lean_usize_land(v___x_2321_, v___x_2324_);
v___x_2326_ = lean_array_uget_borrowed(v_buckets_2312_, v___x_2325_);
v___x_2327_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(v_a_2311_, v___x_2326_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg___boxed(lean_object* v_m_2328_, lean_object* v_a_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_m_2328_, v_a_2329_);
lean_dec_ref(v_a_2329_);
lean_dec_ref(v_m_2328_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(lean_object* v_histogram_2331_, lean_object* v_index_2332_, lean_object* v_val_2333_){
_start:
{
lean_object* v___x_2334_; 
v___x_2334_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_histogram_2331_, v_val_2333_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2335_ = lean_unsigned_to_nat(1u);
v___x_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2336_, 0, v_index_2332_);
v___x_2337_ = lean_unsigned_to_nat(0u);
v___x_2338_ = lean_box(0);
v___x_2339_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2335_);
lean_ctor_set(v___x_2339_, 1, v___x_2336_);
lean_ctor_set(v___x_2339_, 2, v___x_2337_);
lean_ctor_set(v___x_2339_, 3, v___x_2338_);
v___x_2340_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2331_, v_val_2333_, v___x_2339_);
return v___x_2340_;
}
else
{
lean_object* v_val_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2362_; 
v_val_2341_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2343_ = v___x_2334_;
v_isShared_2344_ = v_isSharedCheck_2362_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_val_2341_);
lean_dec(v___x_2334_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2362_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v_leftCount_2345_; lean_object* v_rightCount_2346_; lean_object* v_rightIndex_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2360_; 
v_leftCount_2345_ = lean_ctor_get(v_val_2341_, 0);
v_rightCount_2346_ = lean_ctor_get(v_val_2341_, 2);
v_rightIndex_2347_ = lean_ctor_get(v_val_2341_, 3);
v_isSharedCheck_2360_ = !lean_is_exclusive(v_val_2341_);
if (v_isSharedCheck_2360_ == 0)
{
lean_object* v_unused_2361_; 
v_unused_2361_ = lean_ctor_get(v_val_2341_, 1);
lean_dec(v_unused_2361_);
v___x_2349_ = v_val_2341_;
v_isShared_2350_ = v_isSharedCheck_2360_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_rightIndex_2347_);
lean_inc(v_rightCount_2346_);
lean_inc(v_leftCount_2345_);
lean_dec(v_val_2341_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2360_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2354_; 
v___x_2351_ = lean_unsigned_to_nat(1u);
v___x_2352_ = lean_nat_add(v_leftCount_2345_, v___x_2351_);
lean_dec(v_leftCount_2345_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v_index_2332_);
v___x_2354_ = v___x_2343_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_index_2332_);
v___x_2354_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
lean_object* v___x_2356_; 
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 1, v___x_2354_);
lean_ctor_set(v___x_2349_, 0, v___x_2352_);
v___x_2356_ = v___x_2349_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2352_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2358_, 2, v_rightCount_2346_);
lean_ctor_set(v_reuseFailAlloc_2358_, 3, v_rightIndex_2347_);
v___x_2356_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2357_; 
v___x_2357_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2331_, v_val_2333_, v___x_2356_);
return v___x_2357_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(lean_object* v_upperBound_2363_, lean_object* v_fst_2364_, lean_object* v___x_2365_, lean_object* v_fst_2366_, lean_object* v_a_2367_, lean_object* v_b_2368_){
_start:
{
uint8_t v___x_2369_; 
v___x_2369_ = lean_nat_dec_lt(v_a_2367_, v_upperBound_2363_);
if (v___x_2369_ == 0)
{
lean_dec(v_a_2367_);
return v_b_2368_;
}
else
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2370_ = l_Subarray_get___redArg(v_fst_2366_, v_a_2367_);
lean_inc(v_a_2367_);
v___x_2371_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(v_b_2368_, v_a_2367_, v___x_2370_);
v___x_2372_ = lean_unsigned_to_nat(1u);
v___x_2373_ = lean_nat_add(v_a_2367_, v___x_2372_);
lean_dec(v_a_2367_);
v_a_2367_ = v___x_2373_;
v_b_2368_ = v___x_2371_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg___boxed(lean_object* v_upperBound_2375_, lean_object* v_fst_2376_, lean_object* v___x_2377_, lean_object* v_fst_2378_, lean_object* v_a_2379_, lean_object* v_b_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(v_upperBound_2375_, v_fst_2376_, v___x_2377_, v_fst_2378_, v_a_2379_, v_b_2380_);
lean_dec_ref(v_fst_2378_);
lean_dec(v___x_2377_);
lean_dec_ref(v_fst_2376_);
lean_dec(v_upperBound_2375_);
return v_res_2381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(lean_object* v_x_2382_, lean_object* v_x_2383_){
_start:
{
if (lean_obj_tag(v_x_2383_) == 0)
{
lean_inc(v_x_2382_);
return v_x_2382_;
}
else
{
lean_object* v_key_2384_; lean_object* v_value_2385_; lean_object* v_tail_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v_key_2384_ = lean_ctor_get(v_x_2383_, 0);
v_value_2385_ = lean_ctor_get(v_x_2383_, 1);
v_tail_2386_ = lean_ctor_get(v_x_2383_, 2);
v___x_2387_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(v_x_2382_, v_tail_2386_);
lean_inc(v_value_2385_);
lean_inc(v_key_2384_);
v___x_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2388_, 0, v_key_2384_);
lean_ctor_set(v___x_2388_, 1, v_value_2385_);
v___x_2389_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2388_);
lean_ctor_set(v___x_2389_, 1, v___x_2387_);
return v___x_2389_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5___boxed(lean_object* v_x_2390_, lean_object* v_x_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(v_x_2390_, v_x_2391_);
lean_dec(v_x_2391_);
lean_dec(v_x_2390_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(lean_object* v_as_2393_, size_t v_i_2394_, size_t v_stop_2395_, lean_object* v_b_2396_){
_start:
{
uint8_t v___x_2397_; 
v___x_2397_ = lean_usize_dec_eq(v_i_2394_, v_stop_2395_);
if (v___x_2397_ == 0)
{
size_t v___x_2398_; size_t v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2398_ = ((size_t)1ULL);
v___x_2399_ = lean_usize_sub(v_i_2394_, v___x_2398_);
v___x_2400_ = lean_array_uget_borrowed(v_as_2393_, v___x_2399_);
v___x_2401_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__5(v_b_2396_, v___x_2400_);
lean_dec(v_b_2396_);
v_i_2394_ = v___x_2399_;
v_b_2396_ = v___x_2401_;
goto _start;
}
else
{
return v_b_2396_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6___boxed(lean_object* v_as_2403_, lean_object* v_i_2404_, lean_object* v_stop_2405_, lean_object* v_b_2406_){
_start:
{
size_t v_i_boxed_2407_; size_t v_stop_boxed_2408_; lean_object* v_res_2409_; 
v_i_boxed_2407_ = lean_unbox_usize(v_i_2404_);
lean_dec(v_i_2404_);
v_stop_boxed_2408_ = lean_unbox_usize(v_stop_2405_);
lean_dec(v_stop_2405_);
v_res_2409_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(v_as_2403_, v_i_boxed_2407_, v_stop_boxed_2408_, v_b_2406_);
lean_dec_ref(v_as_2403_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(lean_object* v_histogram_2410_, lean_object* v_index_2411_, lean_object* v_val_2412_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_histogram_2410_, v_val_2412_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2414_ = lean_unsigned_to_nat(0u);
v___x_2415_ = lean_box(0);
v___x_2416_ = lean_unsigned_to_nat(1u);
v___x_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2417_, 0, v_index_2411_);
v___x_2418_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2414_);
lean_ctor_set(v___x_2418_, 1, v___x_2415_);
lean_ctor_set(v___x_2418_, 2, v___x_2416_);
lean_ctor_set(v___x_2418_, 3, v___x_2417_);
v___x_2419_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2410_, v_val_2412_, v___x_2418_);
return v___x_2419_;
}
else
{
lean_object* v_val_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2441_; 
v_val_2420_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2422_ = v___x_2413_;
v_isShared_2423_ = v_isSharedCheck_2441_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_val_2420_);
lean_dec(v___x_2413_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2441_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v_leftCount_2424_; lean_object* v_leftIndex_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2438_; 
v_leftCount_2424_ = lean_ctor_get(v_val_2420_, 0);
v_leftIndex_2425_ = lean_ctor_get(v_val_2420_, 1);
v_isSharedCheck_2438_ = !lean_is_exclusive(v_val_2420_);
if (v_isSharedCheck_2438_ == 0)
{
lean_object* v_unused_2439_; lean_object* v_unused_2440_; 
v_unused_2439_ = lean_ctor_get(v_val_2420_, 3);
lean_dec(v_unused_2439_);
v_unused_2440_ = lean_ctor_get(v_val_2420_, 2);
lean_dec(v_unused_2440_);
v___x_2427_ = v_val_2420_;
v_isShared_2428_ = v_isSharedCheck_2438_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_leftIndex_2425_);
lean_inc(v_leftCount_2424_);
lean_dec(v_val_2420_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2438_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2432_; 
v___x_2429_ = lean_unsigned_to_nat(1u);
v___x_2430_ = lean_nat_add(v_leftCount_2424_, v___x_2429_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v_index_2411_);
v___x_2432_ = v___x_2422_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_index_2411_);
v___x_2432_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
lean_object* v___x_2434_; 
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 3, v___x_2432_);
lean_ctor_set(v___x_2427_, 2, v___x_2430_);
v___x_2434_ = v___x_2427_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_leftCount_2424_);
lean_ctor_set(v_reuseFailAlloc_2436_, 1, v_leftIndex_2425_);
lean_ctor_set(v_reuseFailAlloc_2436_, 2, v___x_2430_);
lean_ctor_set(v_reuseFailAlloc_2436_, 3, v___x_2432_);
v___x_2434_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
lean_object* v___x_2435_; 
v___x_2435_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_histogram_2410_, v_val_2412_, v___x_2434_);
return v___x_2435_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(lean_object* v_upperBound_2442_, lean_object* v___x_2443_, lean_object* v_fst_2444_, lean_object* v___x_2445_, lean_object* v_a_2446_, lean_object* v_b_2447_){
_start:
{
uint8_t v___x_2448_; 
v___x_2448_ = lean_nat_dec_lt(v_a_2446_, v_upperBound_2442_);
if (v___x_2448_ == 0)
{
lean_dec(v_a_2446_);
return v_b_2447_;
}
else
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2449_ = l_Subarray_get___redArg(v_fst_2444_, v_a_2446_);
lean_inc(v_a_2446_);
v___x_2450_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(v_b_2447_, v_a_2446_, v___x_2449_);
v___x_2451_ = lean_unsigned_to_nat(1u);
v___x_2452_ = lean_nat_add(v_a_2446_, v___x_2451_);
lean_dec(v_a_2446_);
v_a_2446_ = v___x_2452_;
v_b_2447_ = v___x_2450_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg___boxed(lean_object* v_upperBound_2454_, lean_object* v___x_2455_, lean_object* v_fst_2456_, lean_object* v___x_2457_, lean_object* v_a_2458_, lean_object* v_b_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(v_upperBound_2454_, v___x_2455_, v_fst_2456_, v___x_2457_, v_a_2458_, v_b_2459_);
lean_dec(v___x_2457_);
lean_dec_ref(v_fst_2456_);
lean_dec(v___x_2455_);
lean_dec(v_upperBound_2454_);
return v_res_2460_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v___x_2461_ = lean_box(0);
v___x_2462_ = lean_unsigned_to_nat(16u);
v___x_2463_ = lean_mk_array(v___x_2462_, v___x_2461_);
return v___x_2463_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1(void){
_start:
{
lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v_hist_2466_; 
v___x_2464_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__0);
v___x_2465_ = lean_unsigned_to_nat(0u);
v_hist_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_2466_, 0, v___x_2465_);
lean_ctor_set(v_hist_2466_, 1, v___x_2464_);
return v_hist_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(lean_object* v_left_2467_, lean_object* v_right_2468_){
_start:
{
lean_object* v___x_2469_; lean_object* v_snd_2470_; lean_object* v_fst_2471_; lean_object* v_fst_2472_; lean_object* v_snd_2473_; lean_object* v___x_2474_; lean_object* v_snd_2475_; lean_object* v_fst_2476_; lean_object* v_fst_2477_; lean_object* v_snd_2478_; lean_object* v_start_2479_; lean_object* v_stop_2480_; lean_object* v___x_2481_; lean_object* v_hist_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v_start_2485_; lean_object* v_stop_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v_buckets_2489_; lean_object* v___x_2490_; lean_object* v___y_2492_; lean_object* v___x_2518_; lean_object* v___x_2519_; uint8_t v___x_2520_; 
v___x_2469_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__2(v_left_2467_, v_right_2468_);
v_snd_2470_ = lean_ctor_get(v___x_2469_, 1);
lean_inc(v_snd_2470_);
v_fst_2471_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_fst_2471_);
lean_dec_ref(v___x_2469_);
v_fst_2472_ = lean_ctor_get(v_snd_2470_, 0);
lean_inc(v_fst_2472_);
v_snd_2473_ = lean_ctor_get(v_snd_2470_, 1);
lean_inc(v_snd_2473_);
lean_dec(v_snd_2470_);
v___x_2474_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3(v_fst_2472_, v_snd_2473_);
v_snd_2475_ = lean_ctor_get(v___x_2474_, 1);
lean_inc(v_snd_2475_);
v_fst_2476_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_fst_2476_);
lean_dec_ref(v___x_2474_);
v_fst_2477_ = lean_ctor_get(v_snd_2475_, 0);
lean_inc(v_fst_2477_);
v_snd_2478_ = lean_ctor_get(v_snd_2475_, 1);
lean_inc(v_snd_2478_);
lean_dec(v_snd_2475_);
v_start_2479_ = lean_ctor_get(v_fst_2476_, 1);
v_stop_2480_ = lean_ctor_get(v_fst_2476_, 2);
v___x_2481_ = lean_unsigned_to_nat(0u);
v_hist_2482_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___closed__1);
v___x_2483_ = lean_nat_sub(v_stop_2480_, v_start_2479_);
v___x_2484_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(v___x_2483_, v_fst_2477_, v___x_2483_, v_fst_2476_, v___x_2481_, v_hist_2482_);
v_start_2485_ = lean_ctor_get(v_fst_2477_, 1);
v_stop_2486_ = lean_ctor_get(v_fst_2477_, 2);
v___x_2487_ = lean_nat_sub(v_stop_2486_, v_start_2485_);
v___x_2488_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(v___x_2487_, v___x_2487_, v_fst_2477_, v___x_2483_, v___x_2481_, v___x_2484_);
lean_dec(v___x_2483_);
lean_dec(v___x_2487_);
v_buckets_2489_ = lean_ctor_get(v___x_2488_, 1);
lean_inc_ref(v_buckets_2489_);
lean_dec_ref(v___x_2488_);
v___x_2490_ = lean_box(0);
v___x_2518_ = lean_box(0);
v___x_2519_ = lean_array_get_size(v_buckets_2489_);
v___x_2520_ = lean_nat_dec_lt(v___x_2481_, v___x_2519_);
if (v___x_2520_ == 0)
{
lean_dec_ref(v_buckets_2489_);
v___y_2492_ = v___x_2518_;
goto v___jp_2491_;
}
else
{
size_t v___x_2521_; size_t v___x_2522_; lean_object* v___x_2523_; 
v___x_2521_ = lean_usize_of_nat(v___x_2519_);
v___x_2522_ = ((size_t)0ULL);
v___x_2523_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__6(v_buckets_2489_, v___x_2521_, v___x_2522_, v___x_2518_);
lean_dec_ref(v_buckets_2489_);
v___y_2492_ = v___x_2523_;
goto v___jp_2491_;
}
v___jp_2491_:
{
lean_object* v___x_2493_; 
v___x_2493_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(v___y_2492_, v___x_2490_);
lean_dec(v___y_2492_);
if (lean_obj_tag(v___x_2493_) == 1)
{
lean_object* v_val_2494_; lean_object* v_snd_2495_; lean_object* v_snd_2496_; lean_object* v_fst_2497_; lean_object* v_fst_2498_; lean_object* v_snd_2499_; lean_object* v___x_2500_; lean_object* v_fst_2501_; lean_object* v_snd_2502_; lean_object* v___x_2503_; lean_object* v_fst_2504_; lean_object* v_snd_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v_val_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_val_2494_);
lean_dec_ref_known(v___x_2493_, 1);
v_snd_2495_ = lean_ctor_get(v_val_2494_, 1);
lean_inc(v_snd_2495_);
lean_dec(v_val_2494_);
v_snd_2496_ = lean_ctor_get(v_snd_2495_, 1);
lean_inc(v_snd_2496_);
v_fst_2497_ = lean_ctor_get(v_snd_2495_, 0);
lean_inc(v_fst_2497_);
lean_dec(v_snd_2495_);
v_fst_2498_ = lean_ctor_get(v_snd_2496_, 0);
lean_inc(v_fst_2498_);
v_snd_2499_ = lean_ctor_get(v_snd_2496_, 1);
lean_inc(v_snd_2499_);
lean_dec(v_snd_2496_);
v___x_2500_ = l_Subarray_split___redArg(v_fst_2476_, v_fst_2498_);
lean_dec(v_fst_2498_);
v_fst_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_fst_2501_);
v_snd_2502_ = lean_ctor_get(v___x_2500_, 1);
lean_inc(v_snd_2502_);
lean_dec_ref(v___x_2500_);
v___x_2503_ = l_Subarray_split___redArg(v_fst_2477_, v_snd_2499_);
lean_dec(v_snd_2499_);
v_fst_2504_ = lean_ctor_get(v___x_2503_, 0);
lean_inc(v_fst_2504_);
v_snd_2505_ = lean_ctor_get(v___x_2503_, 1);
lean_inc(v_snd_2505_);
lean_dec_ref(v___x_2503_);
v___x_2506_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v_fst_2501_, v_fst_2504_);
v___x_2507_ = l_Array_append___redArg(v_fst_2471_, v___x_2506_);
lean_dec_ref(v___x_2506_);
v___x_2508_ = lean_unsigned_to_nat(1u);
v___x_2509_ = lean_mk_empty_array_with_capacity(v___x_2508_);
v___x_2510_ = lean_array_push(v___x_2509_, v_fst_2497_);
v___x_2511_ = l_Array_append___redArg(v___x_2507_, v___x_2510_);
lean_dec_ref(v___x_2510_);
v___x_2512_ = l_Subarray_drop___redArg(v_snd_2502_, v___x_2508_);
v___x_2513_ = l_Subarray_drop___redArg(v_snd_2505_, v___x_2508_);
v___x_2514_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v___x_2512_, v___x_2513_);
v___x_2515_ = l_Array_append___redArg(v___x_2511_, v___x_2514_);
lean_dec_ref(v___x_2514_);
v___x_2516_ = l_Array_append___redArg(v___x_2515_, v_snd_2478_);
lean_dec(v_snd_2478_);
return v___x_2516_;
}
else
{
lean_object* v___x_2517_; 
lean_dec(v___x_2493_);
lean_dec(v_fst_2477_);
lean_dec(v_fst_2476_);
v___x_2517_ = l_Array_append___redArg(v_fst_2471_, v_snd_2478_);
lean_dec(v_snd_2478_);
return v___x_2517_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(size_t v_sz_2524_, size_t v_i_2525_, lean_object* v_bs_2526_){
_start:
{
uint8_t v___x_2527_; 
v___x_2527_ = lean_usize_dec_lt(v_i_2525_, v_sz_2524_);
if (v___x_2527_ == 0)
{
return v_bs_2526_;
}
else
{
lean_object* v_v_2528_; lean_object* v___x_2529_; lean_object* v_bs_x27_2530_; uint8_t v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; size_t v___x_2534_; size_t v___x_2535_; lean_object* v___x_2536_; 
v_v_2528_ = lean_array_uget(v_bs_2526_, v_i_2525_);
v___x_2529_ = lean_unsigned_to_nat(0u);
v_bs_x27_2530_ = lean_array_uset(v_bs_2526_, v_i_2525_, v___x_2529_);
v___x_2531_ = 1;
v___x_2532_ = lean_box(v___x_2531_);
v___x_2533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2532_);
lean_ctor_set(v___x_2533_, 1, v_v_2528_);
v___x_2534_ = ((size_t)1ULL);
v___x_2535_ = lean_usize_add(v_i_2525_, v___x_2534_);
v___x_2536_ = lean_array_uset(v_bs_x27_2530_, v_i_2525_, v___x_2533_);
v_i_2525_ = v___x_2535_;
v_bs_2526_ = v___x_2536_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7___boxed(lean_object* v_sz_2538_, lean_object* v_i_2539_, lean_object* v_bs_2540_){
_start:
{
size_t v_sz_boxed_2541_; size_t v_i_boxed_2542_; lean_object* v_res_2543_; 
v_sz_boxed_2541_ = lean_unbox_usize(v_sz_2538_);
lean_dec(v_sz_2538_);
v_i_boxed_2542_ = lean_unbox_usize(v_i_2539_);
lean_dec(v_i_2539_);
v_res_2543_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_boxed_2541_, v_i_boxed_2542_, v_bs_2540_);
return v_res_2543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(lean_object* v_original_2549_, lean_object* v_edited_2550_){
_start:
{
lean_object* v_i_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; 
v_i_2551_ = lean_unsigned_to_nat(0u);
v___x_2552_ = lean_array_get_size(v_original_2549_);
v___x_2553_ = lean_nat_dec_lt(v_i_2551_, v___x_2552_);
if (v___x_2553_ == 0)
{
size_t v_sz_2554_; size_t v___x_2555_; lean_object* v___x_2556_; 
lean_dec_ref(v_original_2549_);
v_sz_2554_ = lean_array_size(v_edited_2550_);
v___x_2555_ = ((size_t)0ULL);
v___x_2556_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_2554_, v___x_2555_, v_edited_2550_);
return v___x_2556_;
}
else
{
lean_object* v___x_2557_; uint8_t v___x_2558_; 
v___x_2557_ = lean_array_get_size(v_edited_2550_);
v___x_2558_ = lean_nat_dec_lt(v_i_2551_, v___x_2557_);
if (v___x_2558_ == 0)
{
size_t v_sz_2559_; size_t v___x_2560_; lean_object* v___x_2561_; 
lean_dec_ref(v_edited_2550_);
v_sz_2559_ = lean_array_size(v_original_2549_);
v___x_2560_ = ((size_t)0ULL);
v___x_2561_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_2559_, v___x_2560_, v_original_2549_);
return v___x_2561_;
}
else
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v_ds_2564_; lean_object* v___x_2565_; size_t v_sz_2566_; size_t v___x_2567_; lean_object* v___x_2568_; lean_object* v_snd_2569_; lean_object* v_fst_2570_; lean_object* v_fst_2571_; lean_object* v_snd_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2591_; 
lean_inc_ref(v_original_2549_);
v___x_2562_ = l_Array_toSubarray___redArg(v_original_2549_, v_i_2551_, v___x_2552_);
lean_inc_ref(v_edited_2550_);
v___x_2563_ = l_Array_toSubarray___redArg(v_edited_2550_, v_i_2551_, v___x_2557_);
v_ds_2564_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v___x_2562_, v___x_2563_);
v___x_2565_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__1));
v_sz_2566_ = lean_array_size(v_ds_2564_);
v___x_2567_ = ((size_t)0ULL);
v___x_2568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v_edited_2550_, v___x_2557_, v_original_2549_, v___x_2552_, v_ds_2564_, v_sz_2566_, v___x_2567_, v___x_2565_);
lean_dec_ref(v_ds_2564_);
v_snd_2569_ = lean_ctor_get(v___x_2568_, 1);
lean_inc(v_snd_2569_);
v_fst_2570_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_fst_2570_);
lean_dec_ref(v___x_2568_);
v_fst_2571_ = lean_ctor_get(v_snd_2569_, 0);
v_snd_2572_ = lean_ctor_get(v_snd_2569_, 1);
v_isSharedCheck_2591_ = !lean_is_exclusive(v_snd_2569_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2574_ = v_snd_2569_;
v_isShared_2575_ = v_isSharedCheck_2591_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_snd_2572_);
lean_inc(v_fst_2571_);
lean_dec(v_snd_2569_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2591_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 1, v_fst_2571_);
lean_ctor_set(v___x_2574_, 0, v_fst_2570_);
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_fst_2570_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v_fst_2571_);
v___x_2577_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2578_; lean_object* v_fst_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2588_; 
v___x_2578_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2552_, v_original_2549_, v___x_2577_);
lean_dec_ref(v_original_2549_);
v_fst_2579_ = lean_ctor_get(v___x_2578_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2578_);
if (v_isSharedCheck_2588_ == 0)
{
lean_object* v_unused_2589_; 
v_unused_2589_ = lean_ctor_get(v___x_2578_, 1);
lean_dec(v_unused_2589_);
v___x_2581_ = v___x_2578_;
v_isShared_2582_ = v_isSharedCheck_2588_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_fst_2579_);
lean_dec(v___x_2578_);
v___x_2581_ = lean_box(0);
v_isShared_2582_ = v_isSharedCheck_2588_;
goto v_resetjp_2580_;
}
v_resetjp_2580_:
{
lean_object* v___x_2584_; 
if (v_isShared_2582_ == 0)
{
lean_ctor_set(v___x_2581_, 1, v_snd_2572_);
v___x_2584_ = v___x_2581_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_fst_2579_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v_snd_2572_);
v___x_2584_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
lean_object* v___x_2585_; lean_object* v_fst_2586_; 
v___x_2585_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2557_, v_edited_2550_, v___x_2584_);
lean_dec_ref(v_edited_2550_);
v_fst_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_fst_2586_);
lean_dec_ref(v___x_2585_);
return v_fst_2586_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(lean_object* v___x_2592_, uint8_t v_inSubst_2593_, lean_object* v___x_2594_, lean_object* v_____r_2595_, lean_object* v_wssIdx_2596_){
_start:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2597_ = lean_box(v_inSubst_2593_);
v___x_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2592_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
v___x_2599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2599_, 0, v_wssIdx_2596_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
v___x_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2594_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
v___x_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1___boxed(lean_object* v___x_2602_, lean_object* v_inSubst_2603_, lean_object* v___x_2604_, lean_object* v_____r_2605_, lean_object* v_wssIdx_2606_){
_start:
{
uint8_t v_inSubst_boxed_2607_; lean_object* v_res_2608_; 
v_inSubst_boxed_2607_ = lean_unbox(v_inSubst_2603_);
v_res_2608_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2602_, v_inSubst_boxed_2607_, v___x_2604_, v_____r_2605_, v_wssIdx_2606_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(lean_object* v_fst_2609_, uint8_t v___x_2610_, lean_object* v_fst_2611_, lean_object* v___x_2612_, lean_object* v_00___2613_){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2614_ = lean_box(v___x_2610_);
v___x_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2615_, 0, v_fst_2609_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v___x_2616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2616_, 0, v_fst_2611_);
lean_ctor_set(v___x_2616_, 1, v___x_2615_);
v___x_2617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2612_);
lean_ctor_set(v___x_2617_, 1, v___x_2616_);
v___x_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2617_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0___boxed(lean_object* v_fst_2619_, lean_object* v___x_2620_, lean_object* v_fst_2621_, lean_object* v___x_2622_, lean_object* v_00___2623_){
_start:
{
uint8_t v___x_9176__boxed_2624_; lean_object* v_res_2625_; 
v___x_9176__boxed_2624_ = lean_unbox(v___x_2620_);
v_res_2625_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2619_, v___x_9176__boxed_2624_, v_fst_2621_, v___x_2622_, v_00___2623_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(uint8_t v_inSubst_2626_, lean_object* v_snd_2627_, lean_object* v_fst_2628_, lean_object* v_____r_2629_, lean_object* v_withWs_2630_, lean_object* v_wssIdx_2631_){
_start:
{
lean_object* v_wss_x27Idx_2633_; uint8_t v___x_2639_; 
v___x_2639_ = lean_unbox(v_snd_2627_);
if (v___x_2639_ == 0)
{
v_wss_x27Idx_2633_ = v_fst_2628_;
goto v___jp_2632_;
}
else
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = lean_unsigned_to_nat(1u);
v___x_2641_ = lean_nat_add(v_fst_2628_, v___x_2640_);
lean_dec(v_fst_2628_);
v_wss_x27Idx_2633_ = v___x_2641_;
goto v___jp_2632_;
}
v___jp_2632_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2634_ = lean_box(v_inSubst_2626_);
v___x_2635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2635_, 0, v_wss_x27Idx_2633_);
lean_ctor_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2636_, 0, v_wssIdx_2631_);
lean_ctor_set(v___x_2636_, 1, v___x_2635_);
v___x_2637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2637_, 0, v_withWs_2630_);
lean_ctor_set(v___x_2637_, 1, v___x_2636_);
v___x_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2637_);
return v___x_2638_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2___boxed(lean_object* v_inSubst_2642_, lean_object* v_snd_2643_, lean_object* v_fst_2644_, lean_object* v_____r_2645_, lean_object* v_withWs_2646_, lean_object* v_wssIdx_2647_){
_start:
{
uint8_t v_inSubst_boxed_2648_; lean_object* v_res_2649_; 
v_inSubst_boxed_2648_ = lean_unbox(v_inSubst_2642_);
v_res_2649_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_boxed_2648_, v_snd_2643_, v_fst_2644_, v_____r_2645_, v_withWs_2646_, v_wssIdx_2647_);
lean_dec(v_snd_2643_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(lean_object* v_upperBound_2650_, lean_object* v_diff_2651_, lean_object* v_snd_2652_, lean_object* v_snd_2653_, lean_object* v_a_2654_, lean_object* v_b_2655_){
_start:
{
lean_object* v_a_2657_; lean_object* v___y_2662_; uint8_t v___x_2665_; 
v___x_2665_ = lean_nat_dec_lt(v_a_2654_, v_upperBound_2650_);
if (v___x_2665_ == 0)
{
lean_dec(v_a_2654_);
return v_b_2655_;
}
else
{
lean_object* v___x_2666_; lean_object* v_snd_2667_; lean_object* v_snd_2668_; lean_object* v_fst_2669_; lean_object* v_fst_2670_; lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2810_; 
v___x_2666_ = lean_array_fget_borrowed(v_diff_2651_, v_a_2654_);
v_snd_2667_ = lean_ctor_get(v_b_2655_, 1);
lean_inc(v_snd_2667_);
v_snd_2668_ = lean_ctor_get(v_snd_2667_, 1);
lean_inc(v_snd_2668_);
v_fst_2669_ = lean_ctor_get(v___x_2666_, 0);
v_fst_2670_ = lean_ctor_get(v_b_2655_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v_b_2655_);
if (v_isSharedCheck_2810_ == 0)
{
lean_object* v_unused_2811_; 
v_unused_2811_ = lean_ctor_get(v_b_2655_, 1);
lean_dec(v_unused_2811_);
v___x_2672_ = v_b_2655_;
v_isShared_2673_ = v_isSharedCheck_2810_;
goto v_resetjp_2671_;
}
else
{
lean_inc(v_fst_2670_);
lean_dec(v_b_2655_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2810_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v_fst_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2808_; 
v_fst_2674_ = lean_ctor_get(v_snd_2667_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v_snd_2667_);
if (v_isSharedCheck_2808_ == 0)
{
lean_object* v_unused_2809_; 
v_unused_2809_ = lean_ctor_get(v_snd_2667_, 1);
lean_dec(v_unused_2809_);
v___x_2676_ = v_snd_2667_;
v_isShared_2677_ = v_isSharedCheck_2808_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_fst_2674_);
lean_dec(v_snd_2667_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2808_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v_fst_2678_; lean_object* v_snd_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2807_; 
v_fst_2678_ = lean_ctor_get(v_snd_2668_, 0);
v_snd_2679_ = lean_ctor_get(v_snd_2668_, 1);
v_isSharedCheck_2807_ = !lean_is_exclusive(v_snd_2668_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2681_ = v_snd_2668_;
v_isShared_2682_ = v_isSharedCheck_2807_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_snd_2679_);
lean_inc(v_fst_2678_);
lean_dec(v_snd_2668_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2807_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2683_; lean_object* v___y_2685_; lean_object* v___y_2700_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; uint8_t v___x_2711_; 
lean_inc(v___x_2666_);
v___x_2683_ = lean_array_push(v_fst_2670_, v___x_2666_);
v___x_2708_ = lean_unsigned_to_nat(1u);
v___x_2709_ = lean_nat_add(v_a_2654_, v___x_2708_);
v___x_2710_ = lean_array_get_size(v_diff_2651_);
v___x_2711_ = lean_nat_dec_lt(v___x_2709_, v___x_2710_);
if (v___x_2711_ == 0)
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
lean_dec(v___x_2709_);
lean_del_object(v___x_2681_);
lean_del_object(v___x_2676_);
lean_del_object(v___x_2672_);
v___x_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2712_, 0, v_fst_2678_);
lean_ctor_set(v___x_2712_, 1, v_snd_2679_);
v___x_2713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2713_, 0, v_fst_2674_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v___x_2714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2683_);
lean_ctor_set(v___x_2714_, 1, v___x_2713_);
v_a_2657_ = v___x_2714_;
goto v___jp_2656_;
}
else
{
lean_object* v___x_2715_; lean_object* v_fst_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2805_; 
v___x_2715_ = lean_array_fget(v_diff_2651_, v___x_2709_);
lean_dec(v___x_2709_);
v_fst_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2805_ == 0)
{
lean_object* v_unused_2806_; 
v_unused_2806_ = lean_ctor_get(v___x_2715_, 1);
lean_dec(v_unused_2806_);
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2805_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_fst_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2805_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
uint8_t v_inSubst_2720_; lean_object* v___y_2722_; lean_object* v___x_2731_; uint8_t v___x_2732_; 
v_inSubst_2720_ = 0;
v___x_2731_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2732_ = lean_unbox(v_fst_2669_);
switch(v___x_2732_)
{
case 0:
{
uint8_t v___x_2733_; 
lean_del_object(v___x_2681_);
lean_del_object(v___x_2676_);
lean_del_object(v___x_2672_);
v___x_2733_ = lean_unbox(v_fst_2716_);
switch(v___x_2733_)
{
case 0:
{
lean_object* v___x_2734_; lean_object* v___x_2736_; 
v___x_2734_ = lean_array_get_borrowed(v___x_2731_, v_snd_2652_, v_fst_2678_);
lean_inc(v___x_2734_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 1, v___x_2734_);
v___x_2736_ = v___x_2718_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_fst_2716_);
lean_ctor_set(v_reuseFailAlloc_2742_, 1, v___x_2734_);
v___x_2736_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2737_ = lean_array_push(v___x_2683_, v___x_2736_);
v___x_2738_ = lean_nat_add(v_fst_2678_, v___x_2708_);
lean_dec(v_fst_2678_);
v___x_2739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2738_);
lean_ctor_set(v___x_2739_, 1, v_snd_2679_);
v___x_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2740_, 0, v_fst_2674_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2737_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v_a_2657_ = v___x_2741_;
goto v___jp_2656_;
}
}
case 1:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
lean_del_object(v___x_2718_);
lean_dec(v_fst_2716_);
lean_dec(v_snd_2679_);
v___x_2743_ = lean_box(0);
v___x_2744_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2678_, v___x_2665_, v_fst_2674_, v___x_2683_, v___x_2743_);
v___y_2662_ = v___x_2744_;
goto v___jp_2661_;
}
default: 
{
lean_object* v___x_2745_; uint8_t v___x_2746_; 
lean_dec(v_fst_2716_);
v___x_2745_ = lean_array_get_borrowed(v___x_2731_, v_snd_2652_, v_fst_2678_);
v___x_2746_ = lean_unbox(v_snd_2679_);
if (v___x_2746_ == 0)
{
lean_object* v___x_2748_; 
lean_inc(v___x_2745_);
lean_inc(v_fst_2669_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 1, v___x_2745_);
lean_ctor_set(v___x_2718_, 0, v_fst_2669_);
v___x_2748_ = v___x_2718_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_fst_2669_);
lean_ctor_set(v_reuseFailAlloc_2751_, 1, v___x_2745_);
v___x_2748_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = lean_mk_empty_array_with_capacity(v___x_2708_);
v___x_2750_ = lean_array_push(v___x_2749_, v___x_2748_);
v___y_2722_ = v___x_2750_;
goto v___jp_2721_;
}
}
else
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
lean_del_object(v___x_2718_);
v___x_2752_ = lean_array_get_borrowed(v___x_2731_, v_snd_2653_, v_fst_2674_);
lean_inc(v___x_2745_);
lean_inc(v___x_2752_);
v___x_2753_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2752_, v___x_2745_);
v___y_2722_ = v___x_2753_;
goto v___jp_2721_;
}
}
}
}
case 1:
{
uint8_t v___x_2754_; 
lean_del_object(v___x_2681_);
lean_del_object(v___x_2676_);
lean_del_object(v___x_2672_);
v___x_2754_ = lean_unbox(v_fst_2716_);
switch(v___x_2754_)
{
case 0:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
lean_del_object(v___x_2718_);
lean_dec(v_fst_2716_);
lean_dec(v_snd_2679_);
v___x_2755_ = lean_box(0);
v___x_2756_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2678_, v___x_2665_, v_fst_2674_, v___x_2683_, v___x_2755_);
v___y_2662_ = v___x_2756_;
goto v___jp_2661_;
}
case 1:
{
lean_object* v___x_2757_; lean_object* v___x_2759_; 
v___x_2757_ = lean_array_get_borrowed(v___x_2731_, v_snd_2653_, v_fst_2674_);
lean_inc(v___x_2757_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 1, v___x_2757_);
v___x_2759_ = v___x_2718_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_fst_2716_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v___x_2757_);
v___x_2759_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2760_ = lean_array_push(v___x_2683_, v___x_2759_);
v___x_2761_ = lean_nat_add(v_fst_2674_, v___x_2708_);
lean_dec(v_fst_2674_);
v___x_2762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2762_, 0, v_fst_2678_);
lean_ctor_set(v___x_2762_, 1, v_snd_2679_);
v___x_2763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2761_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2760_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
v_a_2657_ = v___x_2764_;
goto v___jp_2656_;
}
}
default: 
{
uint8_t v___x_2769_; 
lean_dec(v_fst_2716_);
v___x_2769_ = lean_unbox(v_snd_2679_);
if (v___x_2769_ == 0)
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; uint8_t v___x_2774_; 
v___x_2770_ = lean_array_get_borrowed(v___x_2731_, v_snd_2653_, v_fst_2674_);
v___x_2771_ = lean_unsigned_to_nat(0u);
v___x_2772_ = lean_string_utf8_byte_size(v___x_2770_);
lean_inc(v___x_2770_);
v___x_2773_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2773_, 0, v___x_2770_);
lean_ctor_set(v___x_2773_, 1, v___x_2771_);
lean_ctor_set(v___x_2773_, 2, v___x_2772_);
v___x_2774_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_2773_);
lean_dec_ref_known(v___x_2773_, 3);
if (v___x_2774_ == 0)
{
lean_object* v___x_2776_; 
lean_inc(v___x_2770_);
lean_inc(v_fst_2669_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 1, v___x_2770_);
lean_ctor_set(v___x_2718_, 0, v_fst_2669_);
v___x_2776_ = v___x_2718_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_fst_2669_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v___x_2770_);
v___x_2776_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2777_ = lean_array_push(v___x_2683_, v___x_2776_);
v___x_2778_ = lean_nat_add(v_fst_2674_, v___x_2708_);
lean_dec(v_fst_2674_);
v___x_2779_ = lean_box(0);
v___x_2780_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2720_, v_snd_2679_, v_fst_2678_, v___x_2779_, v___x_2777_, v___x_2778_);
lean_dec(v_snd_2679_);
v___y_2662_ = v___x_2780_;
goto v___jp_2661_;
}
}
else
{
lean_del_object(v___x_2718_);
goto v___jp_2766_;
}
}
else
{
lean_del_object(v___x_2718_);
goto v___jp_2766_;
}
v___jp_2766_:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = lean_box(0);
v___x_2768_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2720_, v_snd_2679_, v_fst_2678_, v___x_2767_, v___x_2683_, v_fst_2674_);
lean_dec(v_snd_2679_);
v___y_2662_ = v___x_2768_;
goto v___jp_2661_;
}
}
}
}
default: 
{
uint8_t v___x_2782_; 
v___x_2782_ = lean_unbox(v_fst_2716_);
if (v___x_2782_ == 1)
{
lean_object* v___x_2783_; lean_object* v___x_2784_; uint8_t v___x_2785_; 
v___x_2783_ = lean_array_get_borrowed(v___x_2731_, v_snd_2653_, v_fst_2674_);
v___x_2784_ = lean_array_get_size(v_snd_2652_);
v___x_2785_ = lean_nat_dec_lt(v_fst_2678_, v___x_2784_);
if (v___x_2785_ == 0)
{
lean_object* v___x_2787_; 
lean_inc(v___x_2783_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 1, v___x_2783_);
v___x_2787_ = v___x_2718_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_fst_2716_);
lean_ctor_set(v_reuseFailAlloc_2790_, 1, v___x_2783_);
v___x_2787_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = lean_mk_empty_array_with_capacity(v___x_2708_);
v___x_2789_ = lean_array_push(v___x_2788_, v___x_2787_);
v___y_2685_ = v___x_2789_;
goto v___jp_2684_;
}
}
else
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
lean_del_object(v___x_2718_);
lean_dec(v_fst_2716_);
v___x_2791_ = lean_array_fget_borrowed(v_snd_2652_, v_fst_2678_);
lean_inc(v___x_2791_);
lean_inc(v___x_2783_);
v___x_2792_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2783_, v___x_2791_);
v___y_2685_ = v___x_2792_;
goto v___jp_2684_;
}
}
else
{
lean_object* v___x_2793_; lean_object* v___x_2794_; uint8_t v___x_2795_; 
lean_dec(v_fst_2716_);
lean_del_object(v___x_2681_);
lean_del_object(v___x_2676_);
lean_del_object(v___x_2672_);
v___x_2793_ = lean_array_get_borrowed(v___x_2731_, v_snd_2652_, v_fst_2678_);
v___x_2794_ = lean_array_get_size(v_snd_2653_);
v___x_2795_ = lean_nat_dec_lt(v_fst_2674_, v___x_2794_);
if (v___x_2795_ == 0)
{
uint8_t v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2799_; 
v___x_2796_ = 0;
v___x_2797_ = lean_box(v___x_2796_);
lean_inc(v___x_2793_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 1, v___x_2793_);
lean_ctor_set(v___x_2718_, 0, v___x_2797_);
v___x_2799_ = v___x_2718_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v___x_2797_);
lean_ctor_set(v_reuseFailAlloc_2802_, 1, v___x_2793_);
v___x_2799_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = lean_mk_empty_array_with_capacity(v___x_2708_);
v___x_2801_ = lean_array_push(v___x_2800_, v___x_2799_);
v___y_2700_ = v___x_2801_;
goto v___jp_2699_;
}
}
else
{
lean_object* v___x_2803_; lean_object* v___x_2804_; 
lean_del_object(v___x_2718_);
v___x_2803_ = lean_array_fget_borrowed(v_snd_2653_, v_fst_2674_);
lean_inc(v___x_2793_);
lean_inc(v___x_2803_);
v___x_2804_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2803_, v___x_2793_);
v___y_2700_ = v___x_2804_;
goto v___jp_2699_;
}
}
}
}
v___jp_2721_:
{
lean_object* v___x_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; 
v___x_2723_ = l_Array_append___redArg(v___x_2683_, v___y_2722_);
lean_dec_ref(v___y_2722_);
v___x_2724_ = lean_nat_add(v_fst_2678_, v___x_2708_);
lean_dec(v_fst_2678_);
v___x_2725_ = lean_unbox(v_snd_2679_);
lean_dec(v_snd_2679_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2726_ = lean_box(0);
v___x_2727_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2724_, v_inSubst_2720_, v___x_2723_, v___x_2726_, v_fst_2674_);
v___y_2662_ = v___x_2727_;
goto v___jp_2661_;
}
else
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
v___x_2728_ = lean_nat_add(v_fst_2674_, v___x_2708_);
lean_dec(v_fst_2674_);
v___x_2729_ = lean_box(0);
v___x_2730_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2724_, v_inSubst_2720_, v___x_2723_, v___x_2729_, v___x_2728_);
v___y_2662_ = v___x_2730_;
goto v___jp_2661_;
}
}
}
}
v___jp_2684_:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2691_; 
v___x_2686_ = l_Array_append___redArg(v___x_2683_, v___y_2685_);
lean_dec_ref(v___y_2685_);
v___x_2687_ = lean_unsigned_to_nat(1u);
v___x_2688_ = lean_nat_add(v_fst_2674_, v___x_2687_);
lean_dec(v_fst_2674_);
v___x_2689_ = lean_nat_add(v_fst_2678_, v___x_2687_);
lean_dec(v_fst_2678_);
if (v_isShared_2682_ == 0)
{
lean_ctor_set(v___x_2681_, 0, v___x_2689_);
v___x_2691_ = v___x_2681_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v___x_2689_);
lean_ctor_set(v_reuseFailAlloc_2698_, 1, v_snd_2679_);
v___x_2691_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
lean_object* v___x_2693_; 
if (v_isShared_2677_ == 0)
{
lean_ctor_set(v___x_2676_, 1, v___x_2691_);
lean_ctor_set(v___x_2676_, 0, v___x_2688_);
v___x_2693_ = v___x_2676_;
goto v_reusejp_2692_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v___x_2688_);
lean_ctor_set(v_reuseFailAlloc_2697_, 1, v___x_2691_);
v___x_2693_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2692_;
}
v_reusejp_2692_:
{
lean_object* v___x_2695_; 
if (v_isShared_2673_ == 0)
{
lean_ctor_set(v___x_2672_, 1, v___x_2693_);
lean_ctor_set(v___x_2672_, 0, v___x_2686_);
v___x_2695_ = v___x_2672_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v___x_2686_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v___x_2693_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
v_a_2657_ = v___x_2695_;
goto v___jp_2656_;
}
}
}
}
v___jp_2699_:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2701_ = l_Array_append___redArg(v___x_2683_, v___y_2700_);
lean_dec_ref(v___y_2700_);
v___x_2702_ = lean_unsigned_to_nat(1u);
v___x_2703_ = lean_nat_add(v_fst_2674_, v___x_2702_);
lean_dec(v_fst_2674_);
v___x_2704_ = lean_nat_add(v_fst_2678_, v___x_2702_);
lean_dec(v_fst_2678_);
v___x_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
lean_ctor_set(v___x_2705_, 1, v_snd_2679_);
v___x_2706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2703_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
v___x_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2701_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
v_a_2657_ = v___x_2707_;
goto v___jp_2656_;
}
}
}
}
}
v___jp_2656_:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2658_ = lean_unsigned_to_nat(1u);
v___x_2659_ = lean_nat_add(v_a_2654_, v___x_2658_);
lean_dec(v_a_2654_);
v_a_2654_ = v___x_2659_;
v_b_2655_ = v_a_2657_;
goto _start;
}
v___jp_2661_:
{
if (lean_obj_tag(v___y_2662_) == 0)
{
lean_object* v_a_2663_; 
lean_dec(v_a_2654_);
v_a_2663_ = lean_ctor_get(v___y_2662_, 0);
lean_inc(v_a_2663_);
lean_dec_ref_known(v___y_2662_, 1);
return v_a_2663_;
}
else
{
lean_object* v_a_2664_; 
v_a_2664_ = lean_ctor_get(v___y_2662_, 0);
lean_inc(v_a_2664_);
lean_dec_ref_known(v___y_2662_, 1);
v_a_2657_ = v_a_2664_;
goto v___jp_2656_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___boxed(lean_object* v_upperBound_2812_, lean_object* v_diff_2813_, lean_object* v_snd_2814_, lean_object* v_snd_2815_, lean_object* v_a_2816_, lean_object* v_b_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2812_, v_diff_2813_, v_snd_2814_, v_snd_2815_, v_a_2816_, v_b_2817_);
lean_dec_ref(v_snd_2815_);
lean_dec_ref(v_snd_2814_);
lean_dec_ref(v_diff_2813_);
lean_dec(v_upperBound_2812_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(lean_object* v_s_2829_, lean_object* v_s_x27_2830_){
_start:
{
lean_object* v___x_2831_; lean_object* v_fst_2832_; lean_object* v_snd_2833_; lean_object* v___x_2834_; lean_object* v_fst_2835_; lean_object* v_snd_2836_; lean_object* v_diff_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v_fst_2842_; lean_object* v___x_2843_; size_t v_sz_2844_; size_t v___x_2845_; lean_object* v___x_2846_; 
v___x_2831_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_2829_);
v_fst_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc(v_fst_2832_);
v_snd_2833_ = lean_ctor_get(v___x_2831_, 1);
lean_inc(v_snd_2833_);
lean_dec_ref(v___x_2831_);
v___x_2834_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_x27_2830_);
v_fst_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_fst_2835_);
v_snd_2836_ = lean_ctor_get(v___x_2834_, 1);
lean_inc(v_snd_2836_);
lean_dec_ref(v___x_2834_);
v_diff_2837_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(v_fst_2832_, v_fst_2835_);
v___x_2838_ = lean_unsigned_to_nat(0u);
v___x_2839_ = lean_array_get_size(v_diff_2837_);
v___x_2840_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__2));
v___x_2841_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v___x_2839_, v_diff_2837_, v_snd_2836_, v_snd_2833_, v___x_2838_, v___x_2840_);
lean_dec(v_snd_2833_);
lean_dec(v_snd_2836_);
lean_dec_ref(v_diff_2837_);
v_fst_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_fst_2842_);
lean_dec_ref(v___x_2841_);
v___x_2843_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_fst_2842_);
lean_dec(v_fst_2842_);
v_sz_2844_ = lean_array_size(v___x_2843_);
v___x_2845_ = ((size_t)0ULL);
v___x_2846_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_2844_, v___x_2845_, v___x_2843_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___boxed(lean_object* v_s_2847_, lean_object* v_s_x27_2848_){
_start:
{
lean_object* v_res_2849_; 
v_res_2849_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_2847_, v_s_x27_2848_);
lean_dec_ref(v_s_x27_2848_);
lean_dec_ref(v_s_2847_);
return v_res_2849_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(lean_object* v_upperBound_2850_, lean_object* v_diff_2851_, lean_object* v_snd_2852_, lean_object* v_snd_2853_, lean_object* v_inst_2854_, lean_object* v_R_2855_, lean_object* v_a_2856_, lean_object* v_b_2857_, lean_object* v_c_2858_){
_start:
{
lean_object* v___x_2859_; 
v___x_2859_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2850_, v_diff_2851_, v_snd_2852_, v_snd_2853_, v_a_2856_, v_b_2857_);
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___boxed(lean_object* v_upperBound_2860_, lean_object* v_diff_2861_, lean_object* v_snd_2862_, lean_object* v_snd_2863_, lean_object* v_inst_2864_, lean_object* v_R_2865_, lean_object* v_a_2866_, lean_object* v_b_2867_, lean_object* v_c_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(v_upperBound_2860_, v_diff_2861_, v_snd_2862_, v_snd_2863_, v_inst_2864_, v_R_2865_, v_a_2866_, v_b_2867_, v_c_2868_);
lean_dec_ref(v_snd_2863_);
lean_dec_ref(v_snd_2862_);
lean_dec_ref(v_diff_2861_);
lean_dec(v_upperBound_2860_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(lean_object* v_original_2870_, lean_object* v___x_2871_, lean_object* v_a_2872_, lean_object* v_inst_2873_, lean_object* v_a_2874_){
_start:
{
lean_object* v___x_2875_; 
v___x_2875_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v_original_2870_, v___x_2871_, v_a_2872_, v_a_2874_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___boxed(lean_object* v_original_2876_, lean_object* v___x_2877_, lean_object* v_a_2878_, lean_object* v_inst_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v_res_2881_; 
v_res_2881_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(v_original_2876_, v___x_2877_, v_a_2878_, v_inst_2879_, v_a_2880_);
lean_dec_ref(v_a_2878_);
lean_dec(v___x_2877_);
lean_dec_ref(v_original_2876_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(lean_object* v_edited_2882_, lean_object* v___x_2883_, lean_object* v_a_2884_, lean_object* v_inst_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___redArg(v_edited_2882_, v___x_2883_, v_a_2884_, v_a_2886_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___boxed(lean_object* v_edited_2888_, lean_object* v___x_2889_, lean_object* v_a_2890_, lean_object* v_inst_2891_, lean_object* v_a_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v_edited_2888_, v___x_2889_, v_a_2890_, v_inst_2891_, v_a_2892_);
lean_dec_ref(v_a_2890_);
lean_dec(v___x_2889_);
lean_dec_ref(v_edited_2888_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(lean_object* v___x_2894_, lean_object* v_original_2895_, lean_object* v_inst_2896_, lean_object* v_a_2897_){
_start:
{
lean_object* v___x_2898_; 
v___x_2898_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2894_, v_original_2895_, v_a_2897_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___boxed(lean_object* v___x_2899_, lean_object* v_original_2900_, lean_object* v_inst_2901_, lean_object* v_a_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(v___x_2899_, v_original_2900_, v_inst_2901_, v_a_2902_);
lean_dec_ref(v_original_2900_);
lean_dec(v___x_2899_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(lean_object* v___x_2904_, lean_object* v_edited_2905_, lean_object* v_inst_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2904_, v_edited_2905_, v_a_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___boxed(lean_object* v___x_2909_, lean_object* v_edited_2910_, lean_object* v_inst_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(v___x_2909_, v_edited_2910_, v_inst_2911_, v_a_2912_);
lean_dec_ref(v_edited_2910_);
lean_dec(v___x_2909_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4(lean_object* v_as_2914_, lean_object* v_as_x27_2915_, lean_object* v_b_2916_, lean_object* v_a_2917_){
_start:
{
lean_object* v___x_2918_; 
v___x_2918_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___redArg(v_as_x27_2915_, v_b_2916_);
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4___boxed(lean_object* v_as_2919_, lean_object* v_as_x27_2920_, lean_object* v_b_2921_, lean_object* v_a_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__4(v_as_2919_, v_as_x27_2920_, v_b_2921_, v_a_2922_);
lean_dec(v_as_x27_2920_);
lean_dec(v_as_2919_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7(lean_object* v_lsize_2924_, lean_object* v_rsize_2925_, lean_object* v_histogram_2926_, lean_object* v_index_2927_, lean_object* v_val_2928_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___redArg(v_histogram_2926_, v_index_2927_, v_val_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7___boxed(lean_object* v_lsize_2930_, lean_object* v_rsize_2931_, lean_object* v_histogram_2932_, lean_object* v_index_2933_, lean_object* v_val_2934_){
_start:
{
lean_object* v_res_2935_; 
v_res_2935_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7(v_lsize_2930_, v_rsize_2931_, v_histogram_2932_, v_index_2933_, v_val_2934_);
lean_dec(v_rsize_2931_);
lean_dec(v_lsize_2930_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8(lean_object* v_upperBound_2936_, lean_object* v___x_2937_, lean_object* v_fst_2938_, lean_object* v___x_2939_, lean_object* v_inst_2940_, lean_object* v_R_2941_, lean_object* v_a_2942_, lean_object* v_b_2943_, lean_object* v_c_2944_){
_start:
{
lean_object* v___x_2945_; 
v___x_2945_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___redArg(v_upperBound_2936_, v___x_2937_, v_fst_2938_, v___x_2939_, v_a_2942_, v_b_2943_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8___boxed(lean_object* v_upperBound_2946_, lean_object* v___x_2947_, lean_object* v_fst_2948_, lean_object* v___x_2949_, lean_object* v_inst_2950_, lean_object* v_R_2951_, lean_object* v_a_2952_, lean_object* v_b_2953_, lean_object* v_c_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__8(v_upperBound_2946_, v___x_2947_, v_fst_2948_, v___x_2949_, v_inst_2950_, v_R_2951_, v_a_2952_, v_b_2953_, v_c_2954_);
lean_dec(v___x_2949_);
lean_dec_ref(v_fst_2948_);
lean_dec(v___x_2947_);
lean_dec(v_upperBound_2946_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9(lean_object* v_lsize_2956_, lean_object* v_rsize_2957_, lean_object* v_histogram_2958_, lean_object* v_index_2959_, lean_object* v_val_2960_){
_start:
{
lean_object* v___x_2961_; 
v___x_2961_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___redArg(v_histogram_2958_, v_index_2959_, v_val_2960_);
return v___x_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9___boxed(lean_object* v_lsize_2962_, lean_object* v_rsize_2963_, lean_object* v_histogram_2964_, lean_object* v_index_2965_, lean_object* v_val_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__9(v_lsize_2962_, v_rsize_2963_, v_histogram_2964_, v_index_2965_, v_val_2966_);
lean_dec(v_rsize_2963_);
lean_dec(v_lsize_2962_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10(lean_object* v_upperBound_2968_, lean_object* v_fst_2969_, lean_object* v___x_2970_, lean_object* v_fst_2971_, lean_object* v_inst_2972_, lean_object* v_R_2973_, lean_object* v_a_2974_, lean_object* v_b_2975_, lean_object* v_c_2976_){
_start:
{
lean_object* v___x_2977_; 
v___x_2977_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___redArg(v_upperBound_2968_, v_fst_2969_, v___x_2970_, v_fst_2971_, v_a_2974_, v_b_2975_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10___boxed(lean_object* v_upperBound_2978_, lean_object* v_fst_2979_, lean_object* v___x_2980_, lean_object* v_fst_2981_, lean_object* v_inst_2982_, lean_object* v_R_2983_, lean_object* v_a_2984_, lean_object* v_b_2985_, lean_object* v_c_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__10(v_upperBound_2978_, v_fst_2979_, v___x_2980_, v_fst_2981_, v_inst_2982_, v_R_2983_, v_a_2984_, v_b_2985_, v_c_2986_);
lean_dec_ref(v_fst_2981_);
lean_dec(v___x_2980_);
lean_dec_ref(v_fst_2979_);
lean_dec(v_upperBound_2978_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11(lean_object* v_00_u03b2_2988_, lean_object* v_m_2989_, lean_object* v_a_2990_){
_start:
{
lean_object* v___x_2991_; 
v___x_2991_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___redArg(v_m_2989_, v_a_2990_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11___boxed(lean_object* v_00_u03b2_2992_, lean_object* v_m_2993_, lean_object* v_a_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11(v_00_u03b2_2992_, v_m_2993_, v_a_2994_);
lean_dec_ref(v_a_2994_);
lean_dec_ref(v_m_2993_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12(lean_object* v_00_u03b2_2996_, lean_object* v_m_2997_, lean_object* v_a_2998_, lean_object* v_b_2999_){
_start:
{
lean_object* v___x_3000_; 
v___x_3000_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12___redArg(v_m_2997_, v_a_2998_, v_b_2999_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14(lean_object* v_inst_3001_, lean_object* v_R_3002_, lean_object* v_a_3003_, lean_object* v_b_3004_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__3_spec__6_spec__14___redArg(v_a_3003_, v_b_3004_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20(lean_object* v_00_u03b2_3006_, lean_object* v_a_3007_, lean_object* v_x_3008_){
_start:
{
lean_object* v___x_3009_; 
v___x_3009_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___redArg(v_a_3007_, v_x_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20___boxed(lean_object* v_00_u03b2_3010_, lean_object* v_a_3011_, lean_object* v_x_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__11_spec__20(v_00_u03b2_3010_, v_a_3011_, v_x_3012_);
lean_dec(v_x_3012_);
lean_dec_ref(v_a_3011_);
return v_res_3013_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22(lean_object* v_00_u03b2_3014_, lean_object* v_a_3015_, lean_object* v_x_3016_){
_start:
{
uint8_t v___x_3017_; 
v___x_3017_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___redArg(v_a_3015_, v_x_3016_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22___boxed(lean_object* v_00_u03b2_3018_, lean_object* v_a_3019_, lean_object* v_x_3020_){
_start:
{
uint8_t v_res_3021_; lean_object* v_r_3022_; 
v_res_3021_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__22(v_00_u03b2_3018_, v_a_3019_, v_x_3020_);
lean_dec(v_x_3020_);
lean_dec_ref(v_a_3019_);
v_r_3022_ = lean_box(v_res_3021_);
return v_r_3022_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23(lean_object* v_00_u03b2_3023_, lean_object* v_data_3024_){
_start:
{
lean_object* v___x_3025_; 
v___x_3025_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23___redArg(v_data_3024_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24(lean_object* v_00_u03b2_3026_, lean_object* v_a_3027_, lean_object* v_b_3028_, lean_object* v_x_3029_){
_start:
{
lean_object* v___x_3030_; 
v___x_3030_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__24___redArg(v_a_3027_, v_b_3028_, v_x_3029_);
return v___x_3030_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28(lean_object* v_00_u03b2_3031_, lean_object* v_i_3032_, lean_object* v_source_3033_, lean_object* v_target_3034_){
_start:
{
lean_object* v___x_3035_; 
v___x_3035_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28___redArg(v_i_3032_, v_source_3033_, v_target_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_3036_, lean_object* v_x_3037_, lean_object* v_x_3038_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1_spec__7_spec__12_spec__23_spec__28_spec__29___redArg(v_x_3037_, v_x_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(lean_object* v_s_3040_){
_start:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3041_ = lean_string_data(v_s_3040_);
v___x_3042_ = lean_array_mk(v___x_3041_);
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(lean_object* v_s_3043_, lean_object* v_s_x27_3044_){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3045_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3043_);
v___x_3046_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3044_);
v___x_3047_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3045_, v___x_3046_);
v___x_3048_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_3047_);
lean_dec_ref(v___x_3047_);
return v___x_3048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(lean_object* v_s_3049_, lean_object* v_s_x27_3050_){
_start:
{
uint8_t v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; uint8_t v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3051_ = 1;
v___x_3052_ = lean_box(v___x_3051_);
v___x_3053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
lean_ctor_set(v___x_3053_, 1, v_s_3049_);
v___x_3054_ = 0;
v___x_3055_ = lean_box(v___x_3054_);
v___x_3056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
lean_ctor_set(v___x_3056_, 1, v_s_x27_3050_);
v___x_3057_ = lean_unsigned_to_nat(2u);
v___x_3058_ = lean_mk_empty_array_with_capacity(v___x_3057_);
v___x_3059_ = lean_array_push(v___x_3058_, v___x_3053_);
v___x_3060_ = lean_array_push(v___x_3059_, v___x_3056_);
return v___x_3060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(lean_object* v_as_3061_, size_t v_i_3062_, size_t v_stop_3063_, lean_object* v_b_3064_){
_start:
{
lean_object* v___y_3066_; uint8_t v___x_3070_; 
v___x_3070_ = lean_usize_dec_eq(v_i_3062_, v_stop_3063_);
if (v___x_3070_ == 0)
{
lean_object* v___x_3071_; lean_object* v_fst_3072_; uint8_t v___x_3073_; uint8_t v___x_3074_; uint8_t v___x_3075_; uint8_t v___x_3076_; 
v___x_3071_ = lean_array_uget_borrowed(v_as_3061_, v_i_3062_);
v_fst_3072_ = lean_ctor_get(v___x_3071_, 0);
v___x_3073_ = 2;
v___x_3074_ = lean_unbox(v_fst_3072_);
v___x_3075_ = l_Lean_Diff_instBEqAction_beq(v___x_3074_, v___x_3073_);
v___x_3076_ = lean_bool_not(v___x_3075_);
if (v___x_3076_ == 0)
{
v___y_3066_ = v_b_3064_;
goto v___jp_3065_;
}
else
{
lean_object* v___x_3077_; 
lean_inc(v___x_3071_);
v___x_3077_ = lean_array_push(v_b_3064_, v___x_3071_);
v___y_3066_ = v___x_3077_;
goto v___jp_3065_;
}
}
else
{
return v_b_3064_;
}
v___jp_3065_:
{
size_t v___x_3067_; size_t v___x_3068_; 
v___x_3067_ = ((size_t)1ULL);
v___x_3068_ = lean_usize_add(v_i_3062_, v___x_3067_);
v_i_3062_ = v___x_3068_;
v_b_3064_ = v___y_3066_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0___boxed(lean_object* v_as_3078_, lean_object* v_i_3079_, lean_object* v_stop_3080_, lean_object* v_b_3081_){
_start:
{
size_t v_i_boxed_3082_; size_t v_stop_boxed_3083_; lean_object* v_res_3084_; 
v_i_boxed_3082_ = lean_unbox_usize(v_i_3079_);
lean_dec(v_i_3079_);
v_stop_boxed_3083_ = lean_unbox_usize(v_stop_3080_);
lean_dec(v_stop_3080_);
v_res_3084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_as_3078_, v_i_boxed_3082_, v_stop_boxed_3083_, v_b_3081_);
lean_dec_ref(v_as_3078_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff(lean_object* v_s_3085_, lean_object* v_s_x27_3086_, uint8_t v_granularity_3087_){
_start:
{
lean_object* v___y_3089_; lean_object* v___y_3090_; lean_object* v___y_3091_; uint8_t v___y_3092_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; 
switch(v_granularity_3087_)
{
case 0:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___y_3134_; uint8_t v___x_3140_; 
v___x_3131_ = lean_string_length(v_s_3085_);
v___x_3132_ = lean_string_length(v_s_x27_3086_);
v___x_3140_ = lean_nat_dec_le(v___x_3131_, v___x_3132_);
if (v___x_3140_ == 0)
{
v___y_3134_ = v___x_3132_;
goto v___jp_3133_;
}
else
{
v___y_3134_ = v___x_3131_;
goto v___jp_3133_;
}
v___jp_3133_:
{
lean_object* v___x_3135_; lean_object* v_maxCharDiffDistance_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; uint8_t v___x_3139_; 
v___x_3135_ = lean_unsigned_to_nat(5u);
v_maxCharDiffDistance_3136_ = lean_nat_div(v___y_3134_, v___x_3135_);
v___x_3137_ = lean_unsigned_to_nat(1u);
v___x_3138_ = lean_nat_shiftr(v___y_3134_, v___x_3137_);
lean_dec(v___y_3134_);
v___x_3139_ = lean_nat_dec_le(v___x_3131_, v___x_3132_);
if (v___x_3139_ == 0)
{
v___y_3111_ = v___x_3138_;
v___y_3112_ = v_maxCharDiffDistance_3136_;
v___y_3113_ = v___x_3137_;
v___y_3114_ = v___x_3131_;
goto v___jp_3110_;
}
else
{
v___y_3111_ = v___x_3138_;
v___y_3112_ = v_maxCharDiffDistance_3136_;
v___y_3113_ = v___x_3137_;
v___y_3114_ = v___x_3132_;
goto v___jp_3110_;
}
}
}
case 1:
{
lean_object* v___x_3141_; 
v___x_3141_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(v_s_3085_, v_s_x27_3086_);
return v___x_3141_;
}
case 2:
{
lean_object* v___x_3142_; 
v___x_3142_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3085_, v_s_x27_3086_);
lean_dec_ref(v_s_x27_3086_);
lean_dec_ref(v_s_3085_);
return v___x_3142_;
}
case 3:
{
lean_object* v___x_3143_; 
v___x_3143_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3085_, v_s_x27_3086_);
return v___x_3143_;
}
default: 
{
uint8_t v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; 
lean_dec_ref(v_s_3085_);
v___x_3144_ = 0;
v___x_3145_ = lean_box(v___x_3144_);
v___x_3146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3145_);
lean_ctor_set(v___x_3146_, 1, v_s_x27_3086_);
v___x_3147_ = lean_unsigned_to_nat(1u);
v___x_3148_ = lean_mk_empty_array_with_capacity(v___x_3147_);
v___x_3149_ = lean_array_push(v___x_3148_, v___x_3146_);
return v___x_3149_;
}
}
v___jp_3088_:
{
if (v___y_3092_ == 0)
{
uint8_t v___x_3093_; 
lean_dec_ref(v___y_3089_);
v___x_3093_ = lean_nat_dec_le(v___y_3091_, v___y_3090_);
lean_dec(v___y_3090_);
lean_dec(v___y_3091_);
if (v___x_3093_ == 0)
{
lean_object* v___x_3094_; 
v___x_3094_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3085_, v_s_x27_3086_);
return v___x_3094_;
}
else
{
lean_object* v___x_3095_; 
v___x_3095_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3085_, v_s_x27_3086_);
lean_dec_ref(v_s_x27_3086_);
lean_dec_ref(v_s_3085_);
return v___x_3095_;
}
}
else
{
size_t v_sz_3096_; size_t v___x_3097_; lean_object* v___x_3098_; 
lean_dec(v___y_3091_);
lean_dec(v___y_3090_);
lean_dec_ref(v_s_x27_3086_);
lean_dec_ref(v_s_3085_);
v_sz_3096_ = lean_array_size(v___y_3089_);
v___x_3097_ = ((size_t)0ULL);
v___x_3098_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_3096_, v___x_3097_, v___y_3089_);
return v___x_3098_;
}
}
v___jp_3099_:
{
lean_object* v_approxEditDistance_3104_; lean_object* v_charArrDiff_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; uint8_t v___x_3108_; 
v_approxEditDistance_3104_ = lean_array_get_size(v___y_3103_);
lean_dec_ref(v___y_3103_);
v_charArrDiff_3105_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v___y_3102_);
lean_dec_ref(v___y_3102_);
v___x_3106_ = lean_array_get_size(v_charArrDiff_3105_);
v___x_3107_ = lean_unsigned_to_nat(3u);
v___x_3108_ = lean_nat_dec_le(v___x_3106_, v___x_3107_);
if (v___x_3108_ == 0)
{
uint8_t v___x_3109_; 
v___x_3109_ = lean_nat_dec_le(v_approxEditDistance_3104_, v___y_3101_);
lean_dec(v___y_3101_);
v___y_3089_ = v_charArrDiff_3105_;
v___y_3090_ = v___y_3100_;
v___y_3091_ = v_approxEditDistance_3104_;
v___y_3092_ = v___x_3109_;
goto v___jp_3088_;
}
else
{
lean_dec(v___y_3101_);
v___y_3089_ = v_charArrDiff_3105_;
v___y_3090_ = v___y_3100_;
v___y_3091_ = v_approxEditDistance_3104_;
v___y_3092_ = v___x_3108_;
goto v___jp_3088_;
}
}
v___jp_3110_:
{
lean_object* v___x_3115_; lean_object* v_maxWordDiffDistance_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v_charDiffRaw_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; uint8_t v___x_3123_; 
v___x_3115_ = lean_nat_shiftr(v___y_3114_, v___y_3113_);
lean_dec(v___y_3114_);
v_maxWordDiffDistance_3116_ = lean_nat_add(v___y_3111_, v___x_3115_);
lean_dec(v___x_3115_);
lean_dec(v___y_3111_);
lean_inc_ref(v_s_3085_);
v___x_3117_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3085_);
lean_inc_ref(v_s_x27_3086_);
v___x_3118_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3086_);
v_charDiffRaw_3119_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3117_, v___x_3118_);
v___x_3120_ = lean_unsigned_to_nat(0u);
v___x_3121_ = lean_array_get_size(v_charDiffRaw_3119_);
v___x_3122_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0));
v___x_3123_ = lean_nat_dec_lt(v___x_3120_, v___x_3121_);
if (v___x_3123_ == 0)
{
v___y_3100_ = v_maxWordDiffDistance_3116_;
v___y_3101_ = v___y_3112_;
v___y_3102_ = v_charDiffRaw_3119_;
v___y_3103_ = v___x_3122_;
goto v___jp_3099_;
}
else
{
uint8_t v___x_3124_; 
v___x_3124_ = lean_nat_dec_le(v___x_3121_, v___x_3121_);
if (v___x_3124_ == 0)
{
if (v___x_3123_ == 0)
{
v___y_3100_ = v_maxWordDiffDistance_3116_;
v___y_3101_ = v___y_3112_;
v___y_3102_ = v_charDiffRaw_3119_;
v___y_3103_ = v___x_3122_;
goto v___jp_3099_;
}
else
{
size_t v___x_3125_; size_t v___x_3126_; lean_object* v___x_3127_; 
v___x_3125_ = ((size_t)0ULL);
v___x_3126_ = lean_usize_of_nat(v___x_3121_);
v___x_3127_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3119_, v___x_3125_, v___x_3126_, v___x_3122_);
v___y_3100_ = v_maxWordDiffDistance_3116_;
v___y_3101_ = v___y_3112_;
v___y_3102_ = v_charDiffRaw_3119_;
v___y_3103_ = v___x_3127_;
goto v___jp_3099_;
}
}
else
{
size_t v___x_3128_; size_t v___x_3129_; lean_object* v___x_3130_; 
v___x_3128_ = ((size_t)0ULL);
v___x_3129_ = lean_usize_of_nat(v___x_3121_);
v___x_3130_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3119_, v___x_3128_, v___x_3129_, v___x_3122_);
v___y_3100_ = v_maxWordDiffDistance_3116_;
v___y_3101_ = v___y_3112_;
v___y_3102_ = v_charDiffRaw_3119_;
v___y_3103_ = v___x_3130_;
goto v___jp_3099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff___boxed(lean_object* v_s_3150_, lean_object* v_s_x27_3151_, lean_object* v_granularity_3152_){
_start:
{
uint8_t v_granularity_boxed_3153_; lean_object* v_res_3154_; 
v_granularity_boxed_3153_ = lean_unbox(v_granularity_3152_);
v_res_3154_ = l_Lean_Meta_Hint_readableDiff(v_s_3150_, v_s_x27_3151_, v_granularity_boxed_3153_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(lean_object* v_as_3155_, size_t v_i_3156_, size_t v_stop_3157_, lean_object* v_b_3158_){
_start:
{
uint8_t v___x_3159_; 
v___x_3159_ = lean_usize_dec_eq(v_i_3156_, v_stop_3157_);
if (v___x_3159_ == 0)
{
lean_object* v___x_3160_; lean_object* v_snd_3161_; lean_object* v___x_3162_; size_t v___x_3163_; size_t v___x_3164_; 
v___x_3160_ = lean_array_uget_borrowed(v_as_3155_, v_i_3156_);
v_snd_3161_ = lean_ctor_get(v___x_3160_, 1);
v___x_3162_ = lean_string_append(v_b_3158_, v_snd_3161_);
v___x_3163_ = ((size_t)1ULL);
v___x_3164_ = lean_usize_add(v_i_3156_, v___x_3163_);
v_i_3156_ = v___x_3164_;
v_b_3158_ = v___x_3162_;
goto _start;
}
else
{
return v_b_3158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0___boxed(lean_object* v_as_3166_, lean_object* v_i_3167_, lean_object* v_stop_3168_, lean_object* v_b_3169_){
_start:
{
size_t v_i_boxed_3170_; size_t v_stop_boxed_3171_; lean_object* v_res_3172_; 
v_i_boxed_3170_ = lean_unbox_usize(v_i_3167_);
lean_dec(v_i_3167_);
v_stop_boxed_3171_ = lean_unbox_usize(v_stop_3168_);
lean_dec(v_stop_3168_);
v_res_3172_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v_as_3166_, v_i_boxed_3170_, v_stop_boxed_3171_, v_b_3169_);
lean_dec_ref(v_as_3166_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(lean_object* v_t_3173_, lean_object* v___y_3174_){
_start:
{
lean_object* v___x_3176_; lean_object* v_infoState_3177_; uint8_t v_enabled_3178_; 
v___x_3176_ = lean_st_ref_get(v___y_3174_);
v_infoState_3177_ = lean_ctor_get(v___x_3176_, 7);
lean_inc_ref(v_infoState_3177_);
lean_dec(v___x_3176_);
v_enabled_3178_ = lean_ctor_get_uint8(v_infoState_3177_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3177_);
if (v_enabled_3178_ == 0)
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
lean_dec_ref(v_t_3173_);
v___x_3179_ = lean_box(0);
v___x_3180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3179_);
return v___x_3180_;
}
else
{
lean_object* v___x_3181_; lean_object* v_infoState_3182_; lean_object* v_env_3183_; lean_object* v_nextMacroScope_3184_; lean_object* v_ngen_3185_; lean_object* v_auxDeclNGen_3186_; lean_object* v_traceState_3187_; lean_object* v_cache_3188_; lean_object* v_messages_3189_; lean_object* v_snapshotTasks_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3212_; 
v___x_3181_ = lean_st_ref_take(v___y_3174_);
v_infoState_3182_ = lean_ctor_get(v___x_3181_, 7);
v_env_3183_ = lean_ctor_get(v___x_3181_, 0);
v_nextMacroScope_3184_ = lean_ctor_get(v___x_3181_, 1);
v_ngen_3185_ = lean_ctor_get(v___x_3181_, 2);
v_auxDeclNGen_3186_ = lean_ctor_get(v___x_3181_, 3);
v_traceState_3187_ = lean_ctor_get(v___x_3181_, 4);
v_cache_3188_ = lean_ctor_get(v___x_3181_, 5);
v_messages_3189_ = lean_ctor_get(v___x_3181_, 6);
v_snapshotTasks_3190_ = lean_ctor_get(v___x_3181_, 8);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3192_ = v___x_3181_;
v_isShared_3193_ = v_isSharedCheck_3212_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_snapshotTasks_3190_);
lean_inc(v_infoState_3182_);
lean_inc(v_messages_3189_);
lean_inc(v_cache_3188_);
lean_inc(v_traceState_3187_);
lean_inc(v_auxDeclNGen_3186_);
lean_inc(v_ngen_3185_);
lean_inc(v_nextMacroScope_3184_);
lean_inc(v_env_3183_);
lean_dec(v___x_3181_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3212_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
uint8_t v_enabled_3194_; lean_object* v_assignment_3195_; lean_object* v_lazyAssignment_3196_; lean_object* v_trees_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3211_; 
v_enabled_3194_ = lean_ctor_get_uint8(v_infoState_3182_, sizeof(void*)*3);
v_assignment_3195_ = lean_ctor_get(v_infoState_3182_, 0);
v_lazyAssignment_3196_ = lean_ctor_get(v_infoState_3182_, 1);
v_trees_3197_ = lean_ctor_get(v_infoState_3182_, 2);
v_isSharedCheck_3211_ = !lean_is_exclusive(v_infoState_3182_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3199_ = v_infoState_3182_;
v_isShared_3200_ = v_isSharedCheck_3211_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_trees_3197_);
lean_inc(v_lazyAssignment_3196_);
lean_inc(v_assignment_3195_);
lean_dec(v_infoState_3182_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3211_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v___x_3201_; lean_object* v___x_3203_; 
v___x_3201_ = l_Lean_PersistentArray_push___redArg(v_trees_3197_, v_t_3173_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 2, v___x_3201_);
v___x_3203_ = v___x_3199_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_assignment_3195_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v_lazyAssignment_3196_);
lean_ctor_set(v_reuseFailAlloc_3210_, 2, v___x_3201_);
lean_ctor_set_uint8(v_reuseFailAlloc_3210_, sizeof(void*)*3, v_enabled_3194_);
v___x_3203_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
lean_object* v___x_3205_; 
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 7, v___x_3203_);
v___x_3205_ = v___x_3192_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_env_3183_);
lean_ctor_set(v_reuseFailAlloc_3209_, 1, v_nextMacroScope_3184_);
lean_ctor_set(v_reuseFailAlloc_3209_, 2, v_ngen_3185_);
lean_ctor_set(v_reuseFailAlloc_3209_, 3, v_auxDeclNGen_3186_);
lean_ctor_set(v_reuseFailAlloc_3209_, 4, v_traceState_3187_);
lean_ctor_set(v_reuseFailAlloc_3209_, 5, v_cache_3188_);
lean_ctor_set(v_reuseFailAlloc_3209_, 6, v_messages_3189_);
lean_ctor_set(v_reuseFailAlloc_3209_, 7, v___x_3203_);
lean_ctor_set(v_reuseFailAlloc_3209_, 8, v_snapshotTasks_3190_);
v___x_3205_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3206_ = lean_st_ref_set(v___y_3174_, v___x_3205_);
v___x_3207_ = lean_box(0);
v___x_3208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3207_);
return v___x_3208_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg___boxed(lean_object* v_t_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_){
_start:
{
lean_object* v_res_3216_; 
v_res_3216_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3213_, v___y_3214_);
lean_dec(v___y_3214_);
return v_res_3216_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3217_ = lean_unsigned_to_nat(32u);
v___x_3218_ = lean_mk_empty_array_with_capacity(v___x_3217_);
v___x_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3218_);
return v___x_3219_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1(void){
_start:
{
size_t v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3220_ = ((size_t)5ULL);
v___x_3221_ = lean_unsigned_to_nat(0u);
v___x_3222_ = lean_unsigned_to_nat(32u);
v___x_3223_ = lean_mk_empty_array_with_capacity(v___x_3222_);
v___x_3224_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0);
v___x_3225_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
lean_ctor_set(v___x_3225_, 1, v___x_3223_);
lean_ctor_set(v___x_3225_, 2, v___x_3221_);
lean_ctor_set(v___x_3225_, 3, v___x_3221_);
lean_ctor_set_usize(v___x_3225_, 4, v___x_3220_);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(lean_object* v_t_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v___x_3230_; lean_object* v_infoState_3231_; uint8_t v_enabled_3232_; 
v___x_3230_ = lean_st_ref_get(v___y_3228_);
v_infoState_3231_ = lean_ctor_get(v___x_3230_, 7);
lean_inc_ref(v_infoState_3231_);
lean_dec(v___x_3230_);
v_enabled_3232_ = lean_ctor_get_uint8(v_infoState_3231_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3231_);
if (v_enabled_3232_ == 0)
{
lean_object* v___x_3233_; lean_object* v___x_3234_; 
lean_dec_ref(v_t_3226_);
v___x_3233_ = lean_box(0);
v___x_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3233_);
return v___x_3234_;
}
else
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3235_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1);
v___x_3236_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3236_, 0, v_t_3226_);
lean_ctor_set(v___x_3236_, 1, v___x_3235_);
v___x_3237_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v___x_3236_, v___y_3228_);
return v___x_3237_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___boxed(lean_object* v_t_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_){
_start:
{
lean_object* v_res_3242_; 
v_res_3242_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v_t_3238_, v___y_3239_, v___y_3240_);
lean_dec(v___y_3240_);
lean_dec_ref(v___y_3239_);
return v_res_3242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0(lean_object* v___x_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v___x_3245_; 
v___x_3245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3243_);
lean_ctor_set(v___x_3245_, 1, v___y_3244_);
return v___x_3245_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3247_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__0));
v___x_3248_ = l_Lean_stringToMessageData(v___x_3247_);
return v___x_3248_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__2));
v___x_3251_ = l_Lean_stringToMessageData(v___x_3250_);
return v___x_3251_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29(void){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__28));
v___x_3301_ = l_Lean_Json_mkObj(v___x_3300_);
return v___x_3301_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30(void){
_start:
{
lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; 
v___x_3302_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29);
v___x_3303_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__19));
v___x_3304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
lean_ctor_set(v___x_3304_, 1, v___x_3302_);
return v___x_3304_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31(void){
_start:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3305_ = lean_box(0);
v___x_3306_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30);
v___x_3307_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3306_);
lean_ctor_set(v___x_3307_, 1, v___x_3305_);
return v___x_3307_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33(void){
_start:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__32));
v___x_3311_ = l_Lean_MessageData_ofFormat(v___x_3310_);
return v___x_3311_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35(void){
_start:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3313_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__34));
v___x_3314_ = l_Lean_stringToMessageData(v___x_3313_);
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(lean_object* v_suggestions_3316_, uint8_t v_forceList_3317_, lean_object* v_codeActionPrefix_x3f_3318_, lean_object* v_ref_3319_, lean_object* v_as_3320_, size_t v_sz_3321_, size_t v_i_3322_, lean_object* v_b_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
lean_object* v_a_3328_; lean_object* v___y_3333_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3344_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___y_3354_; lean_object* v___y_3355_; uint8_t v___x_3373_; 
v___x_3373_ = lean_usize_dec_lt(v_i_3322_, v_sz_3321_);
if (v___x_3373_ == 0)
{
lean_object* v___x_3374_; 
lean_dec(v_ref_3319_);
lean_dec(v_codeActionPrefix_x3f_3318_);
v___x_3374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3374_, 0, v_b_3323_);
return v___x_3374_;
}
else
{
lean_object* v_a_3375_; lean_object* v_span_x3f_3376_; lean_object* v___x_3377_; lean_object* v___y_3379_; lean_object* v___y_3380_; lean_object* v___y_3381_; lean_object* v___y_3382_; uint8_t v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; uint8_t v___y_3386_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; uint8_t v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; uint8_t v___y_3460_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; uint8_t v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; uint8_t v___y_3470_; lean_object* v___y_3474_; lean_object* v___y_3475_; uint8_t v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; uint8_t v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3484_; lean_object* v___y_3485_; uint8_t v___y_3486_; lean_object* v___y_3487_; uint8_t v___y_3488_; lean_object* v___y_3489_; lean_object* v_postInfo_x3f_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3495_; lean_object* v___y_3496_; uint8_t v___y_3497_; lean_object* v___y_3498_; uint8_t v___y_3499_; lean_object* v___y_3500_; lean_object* v_edits_3501_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; uint8_t v___y_3510_; lean_object* v___y_3511_; uint8_t v___y_3512_; lean_object* v___y_3513_; lean_object* v_stop_3514_; lean_object* v___y_3515_; lean_object* v_edits_3516_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v___y_3527_; uint8_t v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; uint8_t v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v_edits_3534_; lean_object* v___y_3535_; lean_object* v___x_3559_; lean_object* v___y_3561_; lean_object* v___y_3562_; uint8_t v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; uint8_t v___y_3566_; lean_object* v___y_3567_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3606_; lean_object* v___y_3607_; uint8_t v___y_3608_; lean_object* v___y_3609_; uint8_t v___y_3610_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3624_; 
v_a_3375_ = lean_array_uget_borrowed(v_as_3320_, v_i_3322_);
v_span_x3f_3376_ = lean_ctor_get(v_a_3375_, 1);
v___x_3377_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_3559_ = l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_;
if (lean_obj_tag(v_span_x3f_3376_) == 0)
{
lean_inc(v_ref_3319_);
v___y_3624_ = v_ref_3319_;
goto v___jp_3623_;
}
else
{
lean_object* v_val_3645_; 
v_val_3645_ = lean_ctor_get(v_span_x3f_3376_, 0);
lean_inc(v_val_3645_);
v___y_3624_ = v_val_3645_;
goto v___jp_3623_;
}
v___jp_3378_:
{
uint8_t v___x_3387_; 
v___x_3387_ = lean_bool_not(v___y_3386_);
if (v___x_3387_ == 0)
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___f_3402_; 
lean_dec_ref(v___y_3384_);
lean_inc_ref(v___y_3385_);
v___x_3388_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson(v___y_3385_);
v___x_3389_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__9));
v___x_3390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3389_);
lean_ctor_set(v___x_3390_, 1, v___x_3388_);
v___x_3391_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3392_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3392_, 0, v___y_3379_);
v___x_3393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3391_);
lean_ctor_set(v___x_3393_, 1, v___x_3392_);
v___x_3394_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3395_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3381_);
v___x_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3394_);
lean_ctor_set(v___x_3396_, 1, v___x_3395_);
v___x_3397_ = lean_box(0);
v___x_3398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3396_);
lean_ctor_set(v___x_3398_, 1, v___x_3397_);
v___x_3399_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3399_, 0, v___x_3393_);
lean_ctor_set(v___x_3399_, 1, v___x_3398_);
v___x_3400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3390_);
lean_ctor_set(v___x_3400_, 1, v___x_3399_);
v___x_3401_ = l_Lean_Json_mkObj(v___x_3400_);
lean_dec_ref_known(v___x_3400_, 2);
v___f_3402_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3402_, 0, v___x_3401_);
if (v___y_3383_ == 0)
{
lean_object* v___x_3403_; 
v___x_3403_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString(v___y_3385_);
v___y_3352_ = v___f_3402_;
v___y_3353_ = v___y_3380_;
v___y_3354_ = v___y_3382_;
v___y_3355_ = v___x_3403_;
goto v___jp_3351_;
}
else
{
lean_object* v___x_3404_; lean_object* v___x_3405_; uint8_t v___x_3406_; 
v___x_3404_ = lean_unsigned_to_nat(0u);
v___x_3405_ = lean_array_get_size(v___y_3385_);
v___x_3406_ = lean_nat_dec_lt(v___x_3404_, v___x_3405_);
if (v___x_3406_ == 0)
{
lean_dec_ref(v___y_3385_);
v___y_3352_ = v___f_3402_;
v___y_3353_ = v___y_3380_;
v___y_3354_ = v___y_3382_;
v___y_3355_ = v___x_3377_;
goto v___jp_3351_;
}
else
{
uint8_t v___x_3407_; 
v___x_3407_ = lean_nat_dec_le(v___x_3405_, v___x_3405_);
if (v___x_3407_ == 0)
{
if (v___x_3406_ == 0)
{
lean_dec_ref(v___y_3385_);
v___y_3352_ = v___f_3402_;
v___y_3353_ = v___y_3380_;
v___y_3354_ = v___y_3382_;
v___y_3355_ = v___x_3377_;
goto v___jp_3351_;
}
else
{
size_t v___x_3408_; size_t v___x_3409_; lean_object* v___x_3410_; 
v___x_3408_ = ((size_t)0ULL);
v___x_3409_ = lean_usize_of_nat(v___x_3405_);
v___x_3410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3385_, v___x_3408_, v___x_3409_, v___x_3377_);
lean_dec_ref(v___y_3385_);
v___y_3352_ = v___f_3402_;
v___y_3353_ = v___y_3380_;
v___y_3354_ = v___y_3382_;
v___y_3355_ = v___x_3410_;
goto v___jp_3351_;
}
}
else
{
size_t v___x_3411_; size_t v___x_3412_; lean_object* v___x_3413_; 
v___x_3411_ = ((size_t)0ULL);
v___x_3412_ = lean_usize_of_nat(v___x_3405_);
v___x_3413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3385_, v___x_3411_, v___x_3412_, v___x_3377_);
lean_dec_ref(v___y_3385_);
v___y_3352_ = v___f_3402_;
v___y_3353_ = v___y_3380_;
v___y_3354_ = v___y_3382_;
v___y_3355_ = v___x_3413_;
goto v___jp_3351_;
}
}
}
}
else
{
lean_object* v___x_3414_; uint64_t v_javascriptHash_3415_; lean_object* v_suggestion_3416_; lean_object* v_messageData_x3f_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___f_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
lean_dec_ref(v___y_3385_);
v___x_3414_ = l_Lean_Meta_Hint_textInsertionWidget;
v_javascriptHash_3415_ = lean_ctor_get_uint64(v___x_3414_, sizeof(void*)*1);
v_suggestion_3416_ = lean_ctor_get(v___y_3384_, 0);
lean_inc_ref(v_suggestion_3416_);
v_messageData_x3f_3417_ = lean_ctor_get(v___y_3384_, 4);
lean_inc(v_messageData_x3f_3417_);
lean_dec_ref(v___y_3384_);
v___x_3418_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18));
v___x_3419_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3420_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3381_);
v___x_3421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3421_, 0, v___x_3419_);
lean_ctor_set(v___x_3421_, 1, v___x_3420_);
v___x_3422_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3423_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3423_, 0, v___y_3379_);
v___x_3424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3422_);
lean_ctor_set(v___x_3424_, 1, v___x_3423_);
v___x_3425_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31);
v___x_3426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3424_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3421_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
v___x_3428_ = l_Lean_Json_mkObj(v___x_3427_);
lean_dec_ref_known(v___x_3427_, 2);
v___f_3429_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3429_, 0, v___x_3428_);
v___x_3430_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3430_, 0, v___x_3418_);
lean_ctor_set(v___x_3430_, 1, v___f_3429_);
lean_ctor_set_uint64(v___x_3430_, sizeof(void*)*2, v_javascriptHash_3415_);
v___x_3431_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33);
v___x_3432_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3430_);
lean_ctor_set(v___x_3432_, 1, v___x_3431_);
v___x_3433_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3434_, 0, v___x_3433_);
lean_ctor_set(v___x_3434_, 1, v___x_3432_);
v___x_3435_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35);
v___x_3436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3434_);
lean_ctor_set(v___x_3436_, 1, v___x_3435_);
v___x_3437_ = l_Lean_stringToMessageData(v___y_3382_);
v___x_3438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3436_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
if (lean_obj_tag(v_messageData_x3f_3417_) == 0)
{
if (lean_obj_tag(v_suggestion_3416_) == 0)
{
lean_object* v_a_3439_; lean_object* v___x_3440_; 
v_a_3439_ = lean_ctor_get(v_suggestion_3416_, 1);
lean_inc(v_a_3439_);
lean_dec_ref_known(v_suggestion_3416_, 2);
v___x_3440_ = l_Lean_MessageData_ofSyntax(v_a_3439_);
v___y_3337_ = v___y_3380_;
v___y_3338_ = v___x_3438_;
v___y_3339_ = v___x_3440_;
goto v___jp_3336_;
}
else
{
lean_object* v_a_3441_; lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3449_; 
v_a_3441_ = lean_ctor_get(v_suggestion_3416_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v_suggestion_3416_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3443_ = v_suggestion_3416_;
v_isShared_3444_ = v_isSharedCheck_3449_;
goto v_resetjp_3442_;
}
else
{
lean_inc(v_a_3441_);
lean_dec(v_suggestion_3416_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3449_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3446_; 
if (v_isShared_3444_ == 0)
{
lean_ctor_set_tag(v___x_3443_, 3);
v___x_3446_ = v___x_3443_;
goto v_reusejp_3445_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3441_);
v___x_3446_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3445_;
}
v_reusejp_3445_:
{
lean_object* v___x_3447_; 
v___x_3447_ = l_Lean_MessageData_ofFormat(v___x_3446_);
v___y_3337_ = v___y_3380_;
v___y_3338_ = v___x_3438_;
v___y_3339_ = v___x_3447_;
goto v___jp_3336_;
}
}
}
}
else
{
lean_object* v_val_3450_; 
lean_dec_ref(v_suggestion_3416_);
v_val_3450_ = lean_ctor_get(v_messageData_x3f_3417_, 0);
lean_inc(v_val_3450_);
lean_dec_ref_known(v_messageData_x3f_3417_, 1);
v___y_3337_ = v___y_3380_;
v___y_3338_ = v___x_3438_;
v___y_3339_ = v_val_3450_;
goto v___jp_3336_;
}
}
}
v___jp_3451_:
{
if (lean_obj_tag(v___y_3452_) == 0)
{
v___y_3379_ = v___y_3453_;
v___y_3380_ = v___y_3454_;
v___y_3381_ = v___y_3455_;
v___y_3382_ = v___y_3456_;
v___y_3383_ = v___y_3457_;
v___y_3384_ = v___y_3458_;
v___y_3385_ = v___y_3459_;
v___y_3386_ = v___y_3460_;
goto v___jp_3378_;
}
else
{
lean_dec_ref_known(v___y_3452_, 1);
v___y_3379_ = v___y_3453_;
v___y_3380_ = v___y_3454_;
v___y_3381_ = v___y_3455_;
v___y_3382_ = v___y_3456_;
v___y_3383_ = v___y_3457_;
v___y_3384_ = v___y_3458_;
v___y_3385_ = v___y_3459_;
v___y_3386_ = v___x_3373_;
goto v___jp_3378_;
}
}
v___jp_3461_:
{
uint8_t v___x_3471_; 
v___x_3471_ = lean_bool_not(v___y_3470_);
if (v___x_3471_ == 0)
{
v___y_3452_ = v___y_3462_;
v___y_3453_ = v___y_3463_;
v___y_3454_ = v___y_3464_;
v___y_3455_ = v___y_3465_;
v___y_3456_ = v___y_3467_;
v___y_3457_ = v___y_3470_;
v___y_3458_ = v___y_3468_;
v___y_3459_ = v___y_3469_;
v___y_3460_ = v___y_3466_;
goto v___jp_3451_;
}
else
{
lean_object* v_messageData_x3f_3472_; 
v_messageData_x3f_3472_ = lean_ctor_get(v___y_3468_, 4);
if (lean_obj_tag(v_messageData_x3f_3472_) == 0)
{
if (v___x_3471_ == 0)
{
v___y_3452_ = v___y_3462_;
v___y_3453_ = v___y_3463_;
v___y_3454_ = v___y_3464_;
v___y_3455_ = v___y_3465_;
v___y_3456_ = v___y_3467_;
v___y_3457_ = v___y_3470_;
v___y_3458_ = v___y_3468_;
v___y_3459_ = v___y_3469_;
v___y_3460_ = v___x_3471_;
goto v___jp_3451_;
}
else
{
lean_dec(v___y_3462_);
v___y_3379_ = v___y_3463_;
v___y_3380_ = v___y_3464_;
v___y_3381_ = v___y_3465_;
v___y_3382_ = v___y_3467_;
v___y_3383_ = v___y_3470_;
v___y_3384_ = v___y_3468_;
v___y_3385_ = v___y_3469_;
v___y_3386_ = v___x_3373_;
goto v___jp_3378_;
}
}
else
{
v___y_3452_ = v___y_3462_;
v___y_3453_ = v___y_3463_;
v___y_3454_ = v___y_3464_;
v___y_3455_ = v___y_3465_;
v___y_3456_ = v___y_3467_;
v___y_3457_ = v___y_3470_;
v___y_3458_ = v___y_3468_;
v___y_3459_ = v___y_3469_;
v___y_3460_ = v___y_3466_;
goto v___jp_3451_;
}
}
}
v___jp_3473_:
{
if (v___y_3476_ == 4)
{
v___y_3462_ = v___y_3474_;
v___y_3463_ = v___y_3475_;
v___y_3464_ = v___y_3482_;
v___y_3465_ = v___y_3477_;
v___y_3466_ = v___y_3479_;
v___y_3467_ = v___y_3478_;
v___y_3468_ = v___y_3480_;
v___y_3469_ = v___y_3481_;
v___y_3470_ = v___x_3373_;
goto v___jp_3461_;
}
else
{
v___y_3462_ = v___y_3474_;
v___y_3463_ = v___y_3475_;
v___y_3464_ = v___y_3482_;
v___y_3465_ = v___y_3477_;
v___y_3466_ = v___y_3479_;
v___y_3467_ = v___y_3478_;
v___y_3468_ = v___y_3480_;
v___y_3469_ = v___y_3481_;
v___y_3470_ = v___y_3479_;
goto v___jp_3461_;
}
}
v___jp_3483_:
{
if (lean_obj_tag(v_postInfo_x3f_3490_) == 0)
{
v___y_3474_ = v___y_3484_;
v___y_3475_ = v___y_3485_;
v___y_3476_ = v___y_3486_;
v___y_3477_ = v___y_3487_;
v___y_3478_ = v___y_3492_;
v___y_3479_ = v___y_3488_;
v___y_3480_ = v___y_3489_;
v___y_3481_ = v___y_3491_;
v___y_3482_ = v___x_3377_;
goto v___jp_3473_;
}
else
{
lean_object* v_val_3493_; 
v_val_3493_ = lean_ctor_get(v_postInfo_x3f_3490_, 0);
lean_inc(v_val_3493_);
lean_dec_ref_known(v_postInfo_x3f_3490_, 1);
v___y_3474_ = v___y_3484_;
v___y_3475_ = v___y_3485_;
v___y_3476_ = v___y_3486_;
v___y_3477_ = v___y_3487_;
v___y_3478_ = v___y_3492_;
v___y_3479_ = v___y_3488_;
v___y_3480_ = v___y_3489_;
v___y_3481_ = v___y_3491_;
v___y_3482_ = v_val_3493_;
goto v___jp_3473_;
}
}
v___jp_3494_:
{
lean_object* v_preInfo_x3f_3502_; 
v_preInfo_x3f_3502_ = lean_ctor_get(v___y_3500_, 1);
if (lean_obj_tag(v_preInfo_x3f_3502_) == 0)
{
lean_object* v_postInfo_x3f_3503_; 
v_postInfo_x3f_3503_ = lean_ctor_get(v___y_3500_, 2);
lean_inc(v_postInfo_x3f_3503_);
v___y_3484_ = v___y_3495_;
v___y_3485_ = v___y_3496_;
v___y_3486_ = v___y_3497_;
v___y_3487_ = v___y_3498_;
v___y_3488_ = v___y_3499_;
v___y_3489_ = v___y_3500_;
v_postInfo_x3f_3490_ = v_postInfo_x3f_3503_;
v___y_3491_ = v_edits_3501_;
v___y_3492_ = v___x_3377_;
goto v___jp_3483_;
}
else
{
lean_object* v_postInfo_x3f_3504_; lean_object* v_val_3505_; 
v_postInfo_x3f_3504_ = lean_ctor_get(v___y_3500_, 2);
lean_inc(v_postInfo_x3f_3504_);
v_val_3505_ = lean_ctor_get(v_preInfo_x3f_3502_, 0);
lean_inc(v_val_3505_);
v___y_3484_ = v___y_3495_;
v___y_3485_ = v___y_3496_;
v___y_3486_ = v___y_3497_;
v___y_3487_ = v___y_3498_;
v___y_3488_ = v___y_3499_;
v___y_3489_ = v___y_3500_;
v_postInfo_x3f_3490_ = v_postInfo_x3f_3504_;
v___y_3491_ = v_edits_3501_;
v___y_3492_ = v_val_3505_;
goto v___jp_3483_;
}
}
v___jp_3506_:
{
uint8_t v___x_3517_; 
v___x_3517_ = lean_nat_dec_lt(v___y_3513_, v_stop_3514_);
if (v___x_3517_ == 0)
{
lean_dec(v_stop_3514_);
lean_dec(v___y_3513_);
v___y_3495_ = v___y_3507_;
v___y_3496_ = v___y_3508_;
v___y_3497_ = v___y_3510_;
v___y_3498_ = v___y_3511_;
v___y_3499_ = v___y_3512_;
v___y_3500_ = v___y_3515_;
v_edits_3501_ = v_edits_3516_;
goto v___jp_3494_;
}
else
{
lean_object* v_source_3518_; uint8_t v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v_source_3518_ = lean_ctor_get(v___y_3509_, 0);
v___x_3519_ = 2;
v___x_3520_ = lean_string_utf8_extract(v_source_3518_, v___y_3513_, v_stop_3514_);
lean_dec(v_stop_3514_);
lean_dec(v___y_3513_);
v___x_3521_ = lean_box(v___x_3519_);
v___x_3522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
lean_ctor_set(v___x_3522_, 1, v___x_3520_);
v___x_3523_ = lean_array_push(v_edits_3516_, v___x_3522_);
v___y_3495_ = v___y_3507_;
v___y_3496_ = v___y_3508_;
v___y_3497_ = v___y_3510_;
v___y_3498_ = v___y_3511_;
v___y_3499_ = v___y_3512_;
v___y_3500_ = v___y_3515_;
v_edits_3501_ = v___x_3523_;
goto v___jp_3494_;
}
}
v___jp_3524_:
{
if (lean_obj_tag(v___y_3526_) == 0)
{
lean_dec_ref(v___y_3533_);
lean_dec(v___y_3530_);
lean_dec(v___y_3525_);
v___y_3495_ = v___y_3526_;
v___y_3496_ = v___y_3527_;
v___y_3497_ = v___y_3528_;
v___y_3498_ = v___y_3529_;
v___y_3499_ = v___y_3531_;
v___y_3500_ = v___y_3532_;
v_edits_3501_ = v_edits_3534_;
goto v___jp_3494_;
}
else
{
lean_object* v_val_3536_; lean_object* v___x_3537_; 
v_val_3536_ = lean_ctor_get(v___y_3526_, 0);
v___x_3537_ = l_Lean_Syntax_getRange_x3f(v_val_3536_, v___y_3531_);
if (lean_obj_tag(v___x_3537_) == 1)
{
lean_object* v_val_3538_; uint8_t v___x_3539_; 
v_val_3538_ = lean_ctor_get(v___x_3537_, 0);
lean_inc(v_val_3538_);
lean_dec_ref_known(v___x_3537_, 1);
v___x_3539_ = l_Lean_Syntax_Range_includes(v_val_3538_, v___y_3533_, v___y_3531_, v___y_3531_);
lean_dec_ref(v___y_3533_);
if (v___x_3539_ == 0)
{
lean_dec(v_val_3538_);
lean_dec(v___y_3530_);
lean_dec(v___y_3525_);
v___y_3495_ = v___y_3526_;
v___y_3496_ = v___y_3527_;
v___y_3497_ = v___y_3528_;
v___y_3498_ = v___y_3529_;
v___y_3499_ = v___y_3531_;
v___y_3500_ = v___y_3532_;
v_edits_3501_ = v_edits_3534_;
goto v___jp_3494_;
}
else
{
lean_object* v_fileMap_3540_; lean_object* v_start_3541_; lean_object* v_stop_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3558_; 
v_fileMap_3540_ = lean_ctor_get(v___y_3535_, 1);
v_start_3541_ = lean_ctor_get(v_val_3538_, 0);
v_stop_3542_ = lean_ctor_get(v_val_3538_, 1);
v_isSharedCheck_3558_ = !lean_is_exclusive(v_val_3538_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3544_ = v_val_3538_;
v_isShared_3545_ = v_isSharedCheck_3558_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_stop_3542_);
lean_inc(v_start_3541_);
lean_dec(v_val_3538_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3558_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
uint8_t v___x_3546_; 
v___x_3546_ = lean_nat_dec_lt(v_start_3541_, v___y_3525_);
if (v___x_3546_ == 0)
{
lean_del_object(v___x_3544_);
lean_dec(v_start_3541_);
lean_dec(v___y_3525_);
v___y_3507_ = v___y_3526_;
v___y_3508_ = v___y_3527_;
v___y_3509_ = v_fileMap_3540_;
v___y_3510_ = v___y_3528_;
v___y_3511_ = v___y_3529_;
v___y_3512_ = v___y_3531_;
v___y_3513_ = v___y_3530_;
v_stop_3514_ = v_stop_3542_;
v___y_3515_ = v___y_3532_;
v_edits_3516_ = v_edits_3534_;
goto v___jp_3506_;
}
else
{
lean_object* v_source_3547_; uint8_t v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3552_; 
v_source_3547_ = lean_ctor_get(v_fileMap_3540_, 0);
v___x_3548_ = 2;
v___x_3549_ = lean_string_utf8_extract(v_source_3547_, v_start_3541_, v___y_3525_);
lean_dec(v___y_3525_);
lean_dec(v_start_3541_);
v___x_3550_ = lean_box(v___x_3548_);
if (v_isShared_3545_ == 0)
{
lean_ctor_set(v___x_3544_, 1, v___x_3549_);
lean_ctor_set(v___x_3544_, 0, v___x_3550_);
v___x_3552_ = v___x_3544_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3550_);
lean_ctor_set(v_reuseFailAlloc_3557_, 1, v___x_3549_);
v___x_3552_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3553_ = lean_unsigned_to_nat(1u);
v___x_3554_ = lean_mk_empty_array_with_capacity(v___x_3553_);
v___x_3555_ = lean_array_push(v___x_3554_, v___x_3552_);
v___x_3556_ = l_Array_append___redArg(v___x_3555_, v_edits_3534_);
lean_dec_ref(v_edits_3534_);
v___y_3507_ = v___y_3526_;
v___y_3508_ = v___y_3527_;
v___y_3509_ = v_fileMap_3540_;
v___y_3510_ = v___y_3528_;
v___y_3511_ = v___y_3529_;
v___y_3512_ = v___y_3531_;
v___y_3513_ = v___y_3530_;
v_stop_3514_ = v_stop_3542_;
v___y_3515_ = v___y_3532_;
v_edits_3516_ = v___x_3556_;
goto v___jp_3506_;
}
}
}
}
}
else
{
lean_dec(v___x_3537_);
lean_dec_ref(v___y_3533_);
lean_dec(v___y_3530_);
lean_dec(v___y_3525_);
v___y_3495_ = v___y_3526_;
v___y_3496_ = v___y_3527_;
v___y_3497_ = v___y_3528_;
v___y_3498_ = v___y_3529_;
v___y_3499_ = v___y_3531_;
v___y_3500_ = v___y_3532_;
v_edits_3501_ = v_edits_3534_;
goto v___jp_3494_;
}
}
}
v___jp_3560_:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
lean_inc_ref(v___y_3568_);
v___x_3571_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3571_, 0, v___y_3567_);
lean_ctor_set(v___x_3571_, 1, v___y_3570_);
lean_ctor_set(v___x_3571_, 2, v___y_3568_);
v___x_3572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3559_);
lean_ctor_set(v___x_3572_, 1, v___x_3571_);
v___x_3573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3573_, 0, v___y_3565_);
lean_ctor_set(v___x_3573_, 1, v___x_3572_);
v___x_3574_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3573_);
v___x_3575_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v___x_3574_, v___y_3324_, v___y_3325_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v_messageData_x3f_3576_; 
lean_dec_ref_known(v___x_3575_, 1);
v_messageData_x3f_3576_ = lean_ctor_get(v___y_3568_, 4);
if (lean_obj_tag(v_messageData_x3f_3576_) == 1)
{
lean_object* v_start_3577_; lean_object* v_stop_3578_; lean_object* v_val_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; uint8_t v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
v_start_3577_ = lean_ctor_get(v___y_3569_, 0);
lean_inc(v_start_3577_);
v_stop_3578_ = lean_ctor_get(v___y_3569_, 1);
lean_inc(v_stop_3578_);
v_val_3579_ = lean_ctor_get(v_messageData_x3f_3576_, 0);
v___x_3580_ = lean_box(0);
lean_inc(v_val_3579_);
v___x_3581_ = l_Lean_MessageData_format(v_val_3579_, v___x_3580_);
v___x_3582_ = 0;
v___x_3583_ = l_Std_Format_defWidth;
v___x_3584_ = lean_unsigned_to_nat(0u);
v___x_3585_ = l_Std_Format_pretty(v___x_3581_, v___x_3583_, v___x_3584_, v___x_3584_);
v___x_3586_ = lean_box(v___x_3582_);
v___x_3587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3586_);
lean_ctor_set(v___x_3587_, 1, v___x_3585_);
v___x_3588_ = lean_unsigned_to_nat(1u);
v___x_3589_ = lean_mk_empty_array_with_capacity(v___x_3588_);
v___x_3590_ = lean_array_push(v___x_3589_, v___x_3587_);
v___y_3525_ = v_start_3577_;
v___y_3526_ = v___y_3561_;
v___y_3527_ = v___y_3562_;
v___y_3528_ = v___y_3563_;
v___y_3529_ = v___y_3564_;
v___y_3530_ = v_stop_3578_;
v___y_3531_ = v___y_3566_;
v___y_3532_ = v___y_3568_;
v___y_3533_ = v___y_3569_;
v_edits_3534_ = v___x_3590_;
v___y_3535_ = v___y_3324_;
goto v___jp_3524_;
}
else
{
lean_object* v_fileMap_3591_; lean_object* v_start_3592_; lean_object* v_stop_3593_; lean_object* v_source_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v_fileMap_3591_ = lean_ctor_get(v___y_3324_, 1);
v_start_3592_ = lean_ctor_get(v___y_3569_, 0);
lean_inc(v_start_3592_);
v_stop_3593_ = lean_ctor_get(v___y_3569_, 1);
lean_inc(v_stop_3593_);
v_source_3594_ = lean_ctor_get(v_fileMap_3591_, 0);
v___x_3595_ = lean_string_utf8_extract(v_source_3594_, v_start_3592_, v_stop_3593_);
lean_inc_ref(v___y_3562_);
v___x_3596_ = l_Lean_Meta_Hint_readableDiff(v___x_3595_, v___y_3562_, v___y_3563_);
v___y_3525_ = v_start_3592_;
v___y_3526_ = v___y_3561_;
v___y_3527_ = v___y_3562_;
v___y_3528_ = v___y_3563_;
v___y_3529_ = v___y_3564_;
v___y_3530_ = v_stop_3593_;
v___y_3531_ = v___y_3566_;
v___y_3532_ = v___y_3568_;
v___y_3533_ = v___y_3569_;
v_edits_3534_ = v___x_3596_;
v___y_3535_ = v___y_3324_;
goto v___jp_3524_;
}
}
else
{
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3604_; 
lean_dec_ref(v___y_3569_);
lean_dec_ref(v___y_3568_);
lean_dec_ref(v___y_3564_);
lean_dec_ref(v___y_3562_);
lean_dec(v___y_3561_);
lean_dec_ref(v_b_3323_);
lean_dec(v_ref_3319_);
lean_dec(v_codeActionPrefix_x3f_3318_);
v_a_3597_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3599_ = v___x_3575_;
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3575_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3602_; 
if (v_isShared_3600_ == 0)
{
v___x_3602_ = v___x_3599_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_a_3597_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
}
v___jp_3605_:
{
lean_object* v_toCodeActionTitle_x3f_3615_; lean_object* v___x_3616_; 
v_toCodeActionTitle_x3f_3615_ = lean_ctor_get(v___y_3612_, 5);
v___x_3616_ = l_Lean_Syntax_ofRange(v___y_3614_, v___x_3373_);
if (lean_obj_tag(v_toCodeActionTitle_x3f_3615_) == 0)
{
if (lean_obj_tag(v_codeActionPrefix_x3f_3318_) == 0)
{
lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3617_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__36));
v___x_3618_ = lean_string_append(v___x_3617_, v___y_3607_);
v___y_3561_ = v___y_3606_;
v___y_3562_ = v___y_3607_;
v___y_3563_ = v___y_3608_;
v___y_3564_ = v___y_3609_;
v___y_3565_ = v___x_3616_;
v___y_3566_ = v___y_3610_;
v___y_3567_ = v___y_3611_;
v___y_3568_ = v___y_3612_;
v___y_3569_ = v___y_3613_;
v___y_3570_ = v___x_3618_;
goto v___jp_3560_;
}
else
{
lean_object* v_val_3619_; lean_object* v___x_3620_; 
v_val_3619_ = lean_ctor_get(v_codeActionPrefix_x3f_3318_, 0);
lean_inc(v_val_3619_);
v___x_3620_ = lean_string_append(v_val_3619_, v___y_3607_);
v___y_3561_ = v___y_3606_;
v___y_3562_ = v___y_3607_;
v___y_3563_ = v___y_3608_;
v___y_3564_ = v___y_3609_;
v___y_3565_ = v___x_3616_;
v___y_3566_ = v___y_3610_;
v___y_3567_ = v___y_3611_;
v___y_3568_ = v___y_3612_;
v___y_3569_ = v___y_3613_;
v___y_3570_ = v___x_3620_;
goto v___jp_3560_;
}
}
else
{
lean_object* v_val_3621_; lean_object* v___x_3622_; 
v_val_3621_ = lean_ctor_get(v_toCodeActionTitle_x3f_3615_, 0);
lean_inc(v_val_3621_);
lean_inc_ref(v___y_3607_);
v___x_3622_ = lean_apply_1(v_val_3621_, v___y_3607_);
v___y_3561_ = v___y_3606_;
v___y_3562_ = v___y_3607_;
v___y_3563_ = v___y_3608_;
v___y_3564_ = v___y_3609_;
v___y_3565_ = v___x_3616_;
v___y_3566_ = v___y_3610_;
v___y_3567_ = v___y_3611_;
v___y_3568_ = v___y_3612_;
v___y_3569_ = v___y_3613_;
v___y_3570_ = v___x_3622_;
goto v___jp_3560_;
}
}
v___jp_3623_:
{
uint8_t v___x_3625_; lean_object* v___x_3626_; 
v___x_3625_ = 0;
v___x_3626_ = l_Lean_Syntax_getRange_x3f(v___y_3624_, v___x_3625_);
lean_dec(v___y_3624_);
if (lean_obj_tag(v___x_3626_) == 1)
{
lean_object* v_val_3627_; lean_object* v_toTryThisSuggestion_3628_; lean_object* v_previewSpan_x3f_3629_; uint8_t v_diffGranularity_3630_; lean_object* v___x_3631_; 
v_val_3627_ = lean_ctor_get(v___x_3626_, 0);
lean_inc_n(v_val_3627_, 2);
lean_dec_ref_known(v___x_3626_, 1);
v_toTryThisSuggestion_3628_ = lean_ctor_get(v_a_3375_, 0);
v_previewSpan_x3f_3629_ = lean_ctor_get(v_a_3375_, 2);
v_diffGranularity_3630_ = lean_ctor_get_uint8(v_a_3375_, sizeof(void*)*3);
lean_inc_ref(v_toTryThisSuggestion_3628_);
v___x_3631_ = l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(v_toTryThisSuggestion_3628_, v_val_3627_, v___y_3324_, v___y_3325_);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_object* v_a_3632_; lean_object* v_range_3633_; lean_object* v_newText_3634_; lean_object* v___x_3635_; 
v_a_3632_ = lean_ctor_get(v___x_3631_, 0);
lean_inc(v_a_3632_);
lean_dec_ref_known(v___x_3631_, 1);
v_range_3633_ = lean_ctor_get(v_a_3632_, 0);
lean_inc_ref(v_range_3633_);
v_newText_3634_ = lean_ctor_get(v_a_3632_, 1);
lean_inc_ref(v_newText_3634_);
v___x_3635_ = l_Lean_Syntax_getRange_x3f(v_ref_3319_, v___x_3625_);
if (lean_obj_tag(v___x_3635_) == 0)
{
lean_inc(v_val_3627_);
lean_inc_ref(v_toTryThisSuggestion_3628_);
lean_inc(v_previewSpan_x3f_3629_);
v___y_3606_ = v_previewSpan_x3f_3629_;
v___y_3607_ = v_newText_3634_;
v___y_3608_ = v_diffGranularity_3630_;
v___y_3609_ = v_range_3633_;
v___y_3610_ = v___x_3625_;
v___y_3611_ = v_a_3632_;
v___y_3612_ = v_toTryThisSuggestion_3628_;
v___y_3613_ = v_val_3627_;
v___y_3614_ = v_val_3627_;
goto v___jp_3605_;
}
else
{
lean_object* v_val_3636_; 
v_val_3636_ = lean_ctor_get(v___x_3635_, 0);
lean_inc(v_val_3636_);
lean_dec_ref_known(v___x_3635_, 1);
lean_inc_ref(v_toTryThisSuggestion_3628_);
lean_inc(v_previewSpan_x3f_3629_);
v___y_3606_ = v_previewSpan_x3f_3629_;
v___y_3607_ = v_newText_3634_;
v___y_3608_ = v_diffGranularity_3630_;
v___y_3609_ = v_range_3633_;
v___y_3610_ = v___x_3625_;
v___y_3611_ = v_a_3632_;
v___y_3612_ = v_toTryThisSuggestion_3628_;
v___y_3613_ = v_val_3627_;
v___y_3614_ = v_val_3636_;
goto v___jp_3605_;
}
}
else
{
lean_object* v_a_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3644_; 
lean_dec(v_val_3627_);
lean_dec_ref(v_b_3323_);
lean_dec(v_ref_3319_);
lean_dec(v_codeActionPrefix_x3f_3318_);
v_a_3637_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3639_ = v___x_3631_;
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_a_3637_);
lean_dec(v___x_3631_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3644_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3642_; 
if (v_isShared_3640_ == 0)
{
v___x_3642_ = v___x_3639_;
goto v_reusejp_3641_;
}
else
{
lean_object* v_reuseFailAlloc_3643_; 
v_reuseFailAlloc_3643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3643_, 0, v_a_3637_);
v___x_3642_ = v_reuseFailAlloc_3643_;
goto v_reusejp_3641_;
}
v_reusejp_3641_:
{
return v___x_3642_;
}
}
}
}
else
{
lean_dec(v___x_3626_);
v_a_3328_ = v_b_3323_;
goto v___jp_3327_;
}
}
}
v___jp_3327_:
{
size_t v___x_3329_; size_t v___x_3330_; 
v___x_3329_ = ((size_t)1ULL);
v___x_3330_ = lean_usize_add(v_i_3322_, v___x_3329_);
v_i_3322_ = v___x_3330_;
v_b_3323_ = v_a_3328_;
goto _start;
}
v___jp_3332_:
{
lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3334_ = l_Lean_MessageData_nestD(v___y_3333_);
v___x_3335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3335_, 0, v_b_3323_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
v_a_3328_ = v___x_3335_;
goto v___jp_3327_;
}
v___jp_3336_:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3340_, 0, v___y_3338_);
lean_ctor_set(v___x_3340_, 1, v___y_3339_);
v___x_3341_ = l_Lean_stringToMessageData(v___y_3337_);
v___x_3342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3340_);
lean_ctor_set(v___x_3342_, 1, v___x_3341_);
v___y_3333_ = v___x_3342_;
goto v___jp_3332_;
}
v___jp_3343_:
{
lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3345_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3346_ = lean_unsigned_to_nat(2u);
v___x_3347_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3);
v___x_3348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3347_);
lean_ctor_set(v___x_3348_, 1, v___y_3344_);
v___x_3349_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3346_);
lean_ctor_set(v___x_3349_, 1, v___x_3348_);
v___x_3350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3345_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
v___y_3333_ = v___x_3350_;
goto v___jp_3332_;
}
v___jp_3351_:
{
lean_object* v___x_3356_; uint64_t v_javascriptHash_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; uint8_t v___x_3369_; 
v___x_3356_ = l_Lean_Meta_Hint_tryThisDiffWidget;
v_javascriptHash_3357_ = lean_ctor_get_uint64(v___x_3356_, sizeof(void*)*1);
v___x_3358_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8));
v___x_3359_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3359_, 0, v___x_3358_);
lean_ctor_set(v___x_3359_, 1, v___y_3352_);
lean_ctor_set_uint64(v___x_3359_, sizeof(void*)*2, v_javascriptHash_3357_);
v___x_3360_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3360_, 0, v___y_3355_);
v___x_3361_ = l_Lean_MessageData_ofFormat(v___x_3360_);
v___x_3362_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3359_);
lean_ctor_set(v___x_3362_, 1, v___x_3361_);
v___x_3363_ = l_Lean_stringToMessageData(v___y_3354_);
v___x_3364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
lean_ctor_set(v___x_3364_, 1, v___x_3362_);
v___x_3365_ = l_Lean_stringToMessageData(v___y_3353_);
v___x_3366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3364_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
v___x_3367_ = lean_array_get_size(v_suggestions_3316_);
v___x_3368_ = lean_unsigned_to_nat(1u);
v___x_3369_ = lean_nat_dec_eq(v___x_3367_, v___x_3368_);
if (v___x_3369_ == 0)
{
v___y_3344_ = v___x_3366_;
goto v___jp_3343_;
}
else
{
uint8_t v___x_3370_; 
v___x_3370_ = lean_bool_not(v_forceList_3317_);
if (v___x_3370_ == 0)
{
v___y_3344_ = v___x_3366_;
goto v___jp_3343_;
}
else
{
lean_object* v___x_3371_; lean_object* v___x_3372_; 
v___x_3371_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3371_);
lean_ctor_set(v___x_3372_, 1, v___x_3366_);
v___y_3333_ = v___x_3372_;
goto v___jp_3332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___boxed(lean_object* v_suggestions_3646_, lean_object* v_forceList_3647_, lean_object* v_codeActionPrefix_x3f_3648_, lean_object* v_ref_3649_, lean_object* v_as_3650_, lean_object* v_sz_3651_, lean_object* v_i_3652_, lean_object* v_b_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_){
_start:
{
uint8_t v_forceList_boxed_3657_; size_t v_sz_boxed_3658_; size_t v_i_boxed_3659_; lean_object* v_res_3660_; 
v_forceList_boxed_3657_ = lean_unbox(v_forceList_3647_);
v_sz_boxed_3658_ = lean_unbox_usize(v_sz_3651_);
lean_dec(v_sz_3651_);
v_i_boxed_3659_ = lean_unbox_usize(v_i_3652_);
lean_dec(v_i_3652_);
v_res_3660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3646_, v_forceList_boxed_3657_, v_codeActionPrefix_x3f_3648_, v_ref_3649_, v_as_3650_, v_sz_boxed_3658_, v_i_boxed_3659_, v_b_3653_, v___y_3654_, v___y_3655_);
lean_dec(v___y_3655_);
lean_dec_ref(v___y_3654_);
lean_dec_ref(v_as_3650_);
lean_dec_ref(v_suggestions_3646_);
return v_res_3660_;
}
}
static lean_object* _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0(void){
_start:
{
lean_object* v___x_3661_; lean_object* v_msg_3662_; 
v___x_3661_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v_msg_3662_ = l_Lean_stringToMessageData(v___x_3661_);
return v_msg_3662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage(lean_object* v_suggestions_3663_, lean_object* v_ref_3664_, lean_object* v_codeActionPrefix_x3f_3665_, uint8_t v_forceList_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_){
_start:
{
lean_object* v_msg_3670_; size_t v_sz_3671_; size_t v___x_3672_; lean_object* v___x_3673_; 
v_msg_3670_ = lean_obj_once(&l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0, &l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0_once, _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0);
v_sz_3671_ = lean_array_size(v_suggestions_3663_);
v___x_3672_ = ((size_t)0ULL);
v___x_3673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3663_, v_forceList_3666_, v_codeActionPrefix_x3f_3665_, v_ref_3664_, v_suggestions_3663_, v_sz_3671_, v___x_3672_, v_msg_3670_, v_a_3667_, v_a_3668_);
return v___x_3673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage___boxed(lean_object* v_suggestions_3674_, lean_object* v_ref_3675_, lean_object* v_codeActionPrefix_x3f_3676_, lean_object* v_forceList_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_){
_start:
{
uint8_t v_forceList_boxed_3681_; lean_object* v_res_3682_; 
v_forceList_boxed_3681_ = lean_unbox(v_forceList_3677_);
v_res_3682_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3674_, v_ref_3675_, v_codeActionPrefix_x3f_3676_, v_forceList_boxed_3681_, v_a_3678_, v_a_3679_);
lean_dec(v_a_3679_);
lean_dec_ref(v_a_3678_);
lean_dec_ref(v_suggestions_3674_);
return v_res_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(lean_object* v_t_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_){
_start:
{
lean_object* v___x_3687_; 
v___x_3687_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3683_, v___y_3685_);
return v___x_3687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___boxed(lean_object* v_t_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(v_t_3688_, v___y_3689_, v___y_3690_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
return v_res_3692_;
}
}
static lean_object* _init_l_Lean_MessageData_hint___closed__3(void){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3697_ = ((lean_object*)(l_Lean_MessageData_hint___closed__2));
v___x_3698_ = l_Lean_stringToMessageData(v___x_3697_);
return v___x_3698_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint(lean_object* v_hint_3699_, lean_object* v_suggestions_3700_, lean_object* v_ref_x3f_3701_, lean_object* v_codeActionPrefix_x3f_3702_, uint8_t v_forceList_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_){
_start:
{
lean_object* v___y_3708_; 
if (lean_obj_tag(v_ref_x3f_3701_) == 0)
{
lean_object* v_ref_3723_; 
v_ref_3723_ = lean_ctor_get(v_a_3704_, 5);
lean_inc(v_ref_3723_);
v___y_3708_ = v_ref_3723_;
goto v___jp_3707_;
}
else
{
lean_object* v_val_3724_; 
v_val_3724_ = lean_ctor_get(v_ref_x3f_3701_, 0);
lean_inc(v_val_3724_);
lean_dec_ref_known(v_ref_x3f_3701_, 1);
v___y_3708_ = v_val_3724_;
goto v___jp_3707_;
}
v___jp_3707_:
{
lean_object* v___x_3709_; 
v___x_3709_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3700_, v___y_3708_, v_codeActionPrefix_x3f_3702_, v_forceList_3703_, v_a_3704_, v_a_3705_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v_a_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3722_; 
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3709_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3712_ = v___x_3709_;
v_isShared_3713_ = v_isSharedCheck_3722_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_a_3710_);
lean_dec(v___x_3709_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3722_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3720_; 
v___x_3714_ = ((lean_object*)(l_Lean_MessageData_hint___closed__1));
v___x_3715_ = lean_obj_once(&l_Lean_MessageData_hint___closed__3, &l_Lean_MessageData_hint___closed__3_once, _init_l_Lean_MessageData_hint___closed__3);
v___x_3716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3715_);
lean_ctor_set(v___x_3716_, 1, v_hint_3699_);
v___x_3717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3716_);
lean_ctor_set(v___x_3717_, 1, v_a_3710_);
v___x_3718_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3714_);
lean_ctor_set(v___x_3718_, 1, v___x_3717_);
if (v_isShared_3713_ == 0)
{
lean_ctor_set(v___x_3712_, 0, v___x_3718_);
v___x_3720_ = v___x_3712_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___x_3718_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
else
{
lean_dec_ref(v_hint_3699_);
return v___x_3709_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint___boxed(lean_object* v_hint_3725_, lean_object* v_suggestions_3726_, lean_object* v_ref_x3f_3727_, lean_object* v_codeActionPrefix_x3f_3728_, lean_object* v_forceList_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_){
_start:
{
uint8_t v_forceList_boxed_3733_; lean_object* v_res_3734_; 
v_forceList_boxed_3733_ = lean_unbox(v_forceList_3729_);
v_res_3734_ = l_Lean_MessageData_hint(v_hint_3725_, v_suggestions_3726_, v_ref_x3f_3727_, v_codeActionPrefix_x3f_3728_, v_forceList_boxed_3733_, v_a_3730_, v_a_3731_);
lean_dec(v_a_3731_);
lean_dec_ref(v_a_3730_);
lean_dec_ref(v_suggestions_3726_);
return v_res_3734_;
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
