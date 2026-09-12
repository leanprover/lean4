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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v_nbuckets_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_627_ = lean_array_get_size(v_data_626_);
v___x_628_ = lean_unsigned_to_nat(2u);
v_nbuckets_629_ = lean_nat_mul(v___x_627_, v___x_628_);
v___x_630_ = lean_unsigned_to_nat(0u);
v___x_631_ = lean_box(0);
v___x_632_ = lean_mk_array(v_nbuckets_629_, v___x_631_);
v___x_633_ = lean_array_propagate_mark(v_data_626_, v___x_632_);
v___x_634_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28___redArg(v___x_630_, v_data_626_, v___x_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(lean_object* v_m_635_, uint32_t v_a_636_, lean_object* v_b_637_){
_start:
{
lean_object* v_size_638_; lean_object* v_buckets_639_; lean_object* v___x_641_; uint8_t v_isShared_642_; uint8_t v_isSharedCheck_683_; 
v_size_638_ = lean_ctor_get(v_m_635_, 0);
v_buckets_639_ = lean_ctor_get(v_m_635_, 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v_m_635_);
if (v_isSharedCheck_683_ == 0)
{
v___x_641_ = v_m_635_;
v_isShared_642_ = v_isSharedCheck_683_;
goto v_resetjp_640_;
}
else
{
lean_inc(v_buckets_639_);
lean_inc(v_size_638_);
lean_dec(v_m_635_);
v___x_641_ = lean_box(0);
v_isShared_642_ = v_isSharedCheck_683_;
goto v_resetjp_640_;
}
v_resetjp_640_:
{
lean_object* v___x_643_; uint64_t v___x_644_; uint64_t v___x_645_; uint64_t v___x_646_; uint64_t v_fold_647_; uint64_t v___x_648_; uint64_t v___x_649_; uint64_t v___x_650_; size_t v___x_651_; size_t v___x_652_; size_t v___x_653_; size_t v___x_654_; size_t v___x_655_; lean_object* v_bkt_656_; uint8_t v___x_657_; 
v___x_643_ = lean_array_get_size(v_buckets_639_);
v___x_644_ = lean_uint32_to_uint64(v_a_636_);
v___x_645_ = 32ULL;
v___x_646_ = lean_uint64_shift_right(v___x_644_, v___x_645_);
v_fold_647_ = lean_uint64_xor(v___x_644_, v___x_646_);
v___x_648_ = 16ULL;
v___x_649_ = lean_uint64_shift_right(v_fold_647_, v___x_648_);
v___x_650_ = lean_uint64_xor(v_fold_647_, v___x_649_);
v___x_651_ = lean_uint64_to_usize(v___x_650_);
v___x_652_ = lean_usize_of_nat(v___x_643_);
v___x_653_ = ((size_t)1ULL);
v___x_654_ = lean_usize_sub(v___x_652_, v___x_653_);
v___x_655_ = lean_usize_land(v___x_651_, v___x_654_);
v_bkt_656_ = lean_array_uget_borrowed(v_buckets_639_, v___x_655_);
v___x_657_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(v_a_636_, v_bkt_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v_size_x27_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v_buckets_x27_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v___x_658_ = lean_unsigned_to_nat(1u);
v_size_x27_659_ = lean_nat_add(v_size_638_, v___x_658_);
lean_dec(v_size_638_);
v___x_660_ = lean_box_uint32(v_a_636_);
lean_inc(v_bkt_656_);
v___x_661_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v_b_637_);
lean_ctor_set(v___x_661_, 2, v_bkt_656_);
v_buckets_x27_662_ = lean_array_uset(v_buckets_639_, v___x_655_, v___x_661_);
v___x_663_ = lean_unsigned_to_nat(4u);
v___x_664_ = lean_nat_mul(v_size_x27_659_, v___x_663_);
v___x_665_ = lean_unsigned_to_nat(3u);
v___x_666_ = lean_nat_div(v___x_664_, v___x_665_);
lean_dec(v___x_664_);
v___x_667_ = lean_array_get_size(v_buckets_x27_662_);
v___x_668_ = lean_nat_dec_le(v___x_666_, v___x_667_);
lean_dec(v___x_666_);
if (v___x_668_ == 0)
{
lean_object* v_val_669_; lean_object* v___x_671_; 
v_val_669_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23___redArg(v_buckets_x27_662_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 1, v_val_669_);
lean_ctor_set(v___x_641_, 0, v_size_x27_659_);
v___x_671_ = v___x_641_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_size_x27_659_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v_val_669_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
else
{
lean_object* v___x_674_; 
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 1, v_buckets_x27_662_);
lean_ctor_set(v___x_641_, 0, v_size_x27_659_);
v___x_674_ = v___x_641_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_size_x27_659_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_buckets_x27_662_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
else
{
lean_object* v___x_676_; lean_object* v_buckets_x27_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
lean_inc(v_bkt_656_);
v___x_676_ = lean_box(0);
v_buckets_x27_677_ = lean_array_uset(v_buckets_639_, v___x_655_, v___x_676_);
v___x_678_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(v_a_636_, v_b_637_, v_bkt_656_);
v___x_679_ = lean_array_uset(v_buckets_x27_677_, v___x_655_, v___x_678_);
if (v_isShared_642_ == 0)
{
lean_ctor_set(v___x_641_, 1, v___x_679_);
v___x_681_ = v___x_641_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_size_638_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg___boxed(lean_object* v_m_684_, lean_object* v_a_685_, lean_object* v_b_686_){
_start:
{
uint32_t v_a_boxed_687_; lean_object* v_res_688_; 
v_a_boxed_687_ = lean_unbox_uint32(v_a_685_);
lean_dec(v_a_685_);
v_res_688_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_m_684_, v_a_boxed_687_, v_b_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(lean_object* v_histogram_689_, lean_object* v_index_690_, uint32_t v_val_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_histogram_689_, v_val_691_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_693_ = lean_unsigned_to_nat(0u);
v___x_694_ = lean_box(0);
v___x_695_ = lean_unsigned_to_nat(1u);
v___x_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_696_, 0, v_index_690_);
v___x_697_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_697_, 0, v___x_693_);
lean_ctor_set(v___x_697_, 1, v___x_694_);
lean_ctor_set(v___x_697_, 2, v___x_695_);
lean_ctor_set(v___x_697_, 3, v___x_696_);
v___x_698_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_689_, v_val_691_, v___x_697_);
return v___x_698_;
}
else
{
lean_object* v_val_699_; lean_object* v___x_701_; uint8_t v_isShared_702_; uint8_t v_isSharedCheck_720_; 
v_val_699_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_720_ == 0)
{
v___x_701_ = v___x_692_;
v_isShared_702_ = v_isSharedCheck_720_;
goto v_resetjp_700_;
}
else
{
lean_inc(v_val_699_);
lean_dec(v___x_692_);
v___x_701_ = lean_box(0);
v_isShared_702_ = v_isSharedCheck_720_;
goto v_resetjp_700_;
}
v_resetjp_700_:
{
lean_object* v_leftCount_703_; lean_object* v_leftIndex_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_717_; 
v_leftCount_703_ = lean_ctor_get(v_val_699_, 0);
v_leftIndex_704_ = lean_ctor_get(v_val_699_, 1);
v_isSharedCheck_717_ = !lean_is_exclusive(v_val_699_);
if (v_isSharedCheck_717_ == 0)
{
lean_object* v_unused_718_; lean_object* v_unused_719_; 
v_unused_718_ = lean_ctor_get(v_val_699_, 3);
lean_dec(v_unused_718_);
v_unused_719_ = lean_ctor_get(v_val_699_, 2);
lean_dec(v_unused_719_);
v___x_706_ = v_val_699_;
v_isShared_707_ = v_isSharedCheck_717_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_leftIndex_704_);
lean_inc(v_leftCount_703_);
lean_dec(v_val_699_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_717_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_708_ = lean_unsigned_to_nat(1u);
v___x_709_ = lean_nat_add(v_leftCount_703_, v___x_708_);
if (v_isShared_702_ == 0)
{
lean_ctor_set(v___x_701_, 0, v_index_690_);
v___x_711_ = v___x_701_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_index_690_);
v___x_711_ = v_reuseFailAlloc_716_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_713_; 
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 3, v___x_711_);
lean_ctor_set(v___x_706_, 2, v___x_709_);
v___x_713_ = v___x_706_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_leftCount_703_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_leftIndex_704_);
lean_ctor_set(v_reuseFailAlloc_715_, 2, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_715_, 3, v___x_711_);
v___x_713_ = v_reuseFailAlloc_715_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_714_; 
v___x_714_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_689_, v_val_691_, v___x_713_);
return v___x_714_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_histogram_721_, lean_object* v_index_722_, lean_object* v_val_723_){
_start:
{
uint32_t v_val_boxed_724_; lean_object* v_res_725_; 
v_val_boxed_724_ = lean_unbox_uint32(v_val_723_);
lean_dec(v_val_723_);
v_res_725_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(v_histogram_721_, v_index_722_, v_val_boxed_724_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(lean_object* v_upperBound_726_, lean_object* v___x_727_, lean_object* v_fst_728_, lean_object* v___x_729_, lean_object* v_a_730_, lean_object* v_b_731_){
_start:
{
uint8_t v___x_732_; 
v___x_732_ = lean_nat_dec_lt(v_a_730_, v_upperBound_726_);
if (v___x_732_ == 0)
{
lean_dec(v_a_730_);
return v_b_731_;
}
else
{
lean_object* v___x_733_; uint32_t v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_733_ = l_Subarray_get___redArg(v_fst_728_, v_a_730_);
v___x_734_ = lean_unbox_uint32(v___x_733_);
lean_dec(v___x_733_);
lean_inc(v_a_730_);
v___x_735_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(v_b_731_, v_a_730_, v___x_734_);
v___x_736_ = lean_unsigned_to_nat(1u);
v___x_737_ = lean_nat_add(v_a_730_, v___x_736_);
lean_dec(v_a_730_);
v_a_730_ = v___x_737_;
v_b_731_ = v___x_735_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg___boxed(lean_object* v_upperBound_739_, lean_object* v___x_740_, lean_object* v_fst_741_, lean_object* v___x_742_, lean_object* v_a_743_, lean_object* v_b_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(v_upperBound_739_, v___x_740_, v_fst_741_, v___x_742_, v_a_743_, v_b_744_);
lean_dec(v___x_742_);
lean_dec_ref(v_fst_741_);
lean_dec(v___x_740_);
lean_dec(v_upperBound_739_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(lean_object* v_as_x27_746_, lean_object* v_b_747_){
_start:
{
if (lean_obj_tag(v_as_x27_746_) == 0)
{
return v_b_747_;
}
else
{
lean_object* v_head_748_; lean_object* v_snd_749_; lean_object* v_leftIndex_750_; 
v_head_748_ = lean_ctor_get(v_as_x27_746_, 0);
v_snd_749_ = lean_ctor_get(v_head_748_, 1);
v_leftIndex_750_ = lean_ctor_get(v_snd_749_, 1);
if (lean_obj_tag(v_leftIndex_750_) == 1)
{
lean_object* v_rightIndex_751_; 
v_rightIndex_751_ = lean_ctor_get(v_snd_749_, 3);
if (lean_obj_tag(v_rightIndex_751_) == 1)
{
if (lean_obj_tag(v_b_747_) == 0)
{
lean_object* v_tail_752_; lean_object* v_fst_753_; lean_object* v_leftCount_754_; lean_object* v_rightCount_755_; lean_object* v_val_756_; lean_object* v_val_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v_tail_752_ = lean_ctor_get(v_as_x27_746_, 1);
v_fst_753_ = lean_ctor_get(v_head_748_, 0);
v_leftCount_754_ = lean_ctor_get(v_snd_749_, 0);
v_rightCount_755_ = lean_ctor_get(v_snd_749_, 2);
v_val_756_ = lean_ctor_get(v_leftIndex_750_, 0);
v_val_757_ = lean_ctor_get(v_rightIndex_751_, 0);
v___x_758_ = lean_nat_add(v_leftCount_754_, v_rightCount_755_);
lean_inc(v_val_757_);
lean_inc(v_val_756_);
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v_val_756_);
lean_ctor_set(v___x_759_, 1, v_val_757_);
lean_inc(v_fst_753_);
v___x_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_760_, 0, v_fst_753_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_758_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
v_as_x27_746_ = v_tail_752_;
v_b_747_ = v___x_762_;
goto _start;
}
else
{
lean_object* v_val_764_; lean_object* v_tail_765_; lean_object* v_fst_766_; lean_object* v_leftCount_767_; lean_object* v_rightCount_768_; lean_object* v_val_769_; lean_object* v_val_770_; lean_object* v_fst_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_792_; 
v_val_764_ = lean_ctor_get(v_b_747_, 0);
lean_inc(v_val_764_);
v_tail_765_ = lean_ctor_get(v_as_x27_746_, 1);
v_fst_766_ = lean_ctor_get(v_head_748_, 0);
v_leftCount_767_ = lean_ctor_get(v_snd_749_, 0);
v_rightCount_768_ = lean_ctor_get(v_snd_749_, 2);
v_val_769_ = lean_ctor_get(v_leftIndex_750_, 0);
v_val_770_ = lean_ctor_get(v_rightIndex_751_, 0);
v_fst_771_ = lean_ctor_get(v_val_764_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v_val_764_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; 
v_unused_793_ = lean_ctor_get(v_val_764_, 1);
lean_dec(v_unused_793_);
v___x_773_ = v_val_764_;
v_isShared_774_ = v_isSharedCheck_792_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_fst_771_);
lean_dec(v_val_764_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_792_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; uint8_t v___x_776_; 
v___x_775_ = lean_nat_add(v_leftCount_767_, v_rightCount_768_);
v___x_776_ = lean_nat_dec_lt(v___x_775_, v_fst_771_);
lean_dec(v_fst_771_);
if (v___x_776_ == 0)
{
lean_dec(v___x_775_);
lean_del_object(v___x_773_);
v_as_x27_746_ = v_tail_765_;
goto _start;
}
else
{
lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_790_; 
v_isSharedCheck_790_ = !lean_is_exclusive(v_b_747_);
if (v_isSharedCheck_790_ == 0)
{
lean_object* v_unused_791_; 
v_unused_791_ = lean_ctor_get(v_b_747_, 0);
lean_dec(v_unused_791_);
v___x_779_ = v_b_747_;
v_isShared_780_ = v_isSharedCheck_790_;
goto v_resetjp_778_;
}
else
{
lean_dec(v_b_747_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_790_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
lean_inc(v_val_770_);
lean_inc(v_val_769_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v_val_770_);
lean_ctor_set(v___x_773_, 0, v_val_769_);
v___x_782_ = v___x_773_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_val_769_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_val_770_);
v___x_782_ = v_reuseFailAlloc_789_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_786_; 
lean_inc(v_fst_766_);
v___x_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_783_, 0, v_fst_766_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v___x_775_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v___x_784_);
v___x_786_ = v___x_779_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_788_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
v_as_x27_746_ = v_tail_765_;
v_b_747_ = v___x_786_;
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
lean_object* v_tail_794_; 
v_tail_794_ = lean_ctor_get(v_as_x27_746_, 1);
v_as_x27_746_ = v_tail_794_;
goto _start;
}
}
else
{
lean_object* v_tail_796_; 
v_tail_796_ = lean_ctor_get(v_as_x27_746_, 1);
v_as_x27_746_ = v_tail_796_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_as_x27_798_, lean_object* v_b_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(v_as_x27_798_, v_b_799_);
lean_dec(v_as_x27_798_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(lean_object* v_a_801_, lean_object* v_b_802_){
_start:
{
lean_object* v_array_803_; lean_object* v_start_804_; lean_object* v_stop_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_818_; 
v_array_803_ = lean_ctor_get(v_a_801_, 0);
v_start_804_ = lean_ctor_get(v_a_801_, 1);
v_stop_805_ = lean_ctor_get(v_a_801_, 2);
v_isSharedCheck_818_ = !lean_is_exclusive(v_a_801_);
if (v_isSharedCheck_818_ == 0)
{
v___x_807_ = v_a_801_;
v_isShared_808_ = v_isSharedCheck_818_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_stop_805_);
lean_inc(v_start_804_);
lean_inc(v_array_803_);
lean_dec(v_a_801_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_818_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
uint8_t v___x_809_; 
v___x_809_ = lean_nat_dec_lt(v_start_804_, v_stop_805_);
if (v___x_809_ == 0)
{
lean_del_object(v___x_807_);
lean_dec(v_stop_805_);
lean_dec(v_start_804_);
lean_dec_ref(v_array_803_);
return v_b_802_;
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_813_; 
v___x_810_ = lean_unsigned_to_nat(1u);
v___x_811_ = lean_nat_add(v_start_804_, v___x_810_);
lean_inc_ref(v_array_803_);
if (v_isShared_808_ == 0)
{
lean_ctor_set(v___x_807_, 1, v___x_811_);
v___x_813_ = v___x_807_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_array_803_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_817_, 2, v_stop_805_);
v___x_813_ = v_reuseFailAlloc_817_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_814_ = lean_array_fget(v_array_803_, v_start_804_);
lean_dec(v_start_804_);
lean_dec_ref(v_array_803_);
v___x_815_ = lean_array_push(v_b_802_, v___x_814_);
v_a_801_ = v___x_813_;
v_b_802_ = v___x_815_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8(lean_object* v_left_819_, lean_object* v_right_820_, lean_object* v_i_821_){
_start:
{
lean_object* v_start_822_; lean_object* v_stop_823_; lean_object* v_start_824_; lean_object* v_stop_825_; lean_object* v___x_826_; uint8_t v___x_827_; lean_object* v___x_828_; uint8_t v___y_830_; 
v_start_822_ = lean_ctor_get(v_left_819_, 1);
v_stop_823_ = lean_ctor_get(v_left_819_, 2);
v_start_824_ = lean_ctor_get(v_right_820_, 1);
v_stop_825_ = lean_ctor_get(v_right_820_, 2);
v___x_826_ = lean_nat_sub(v_stop_823_, v_start_822_);
v___x_827_ = lean_nat_dec_lt(v_i_821_, v___x_826_);
v___x_828_ = lean_nat_sub(v_stop_825_, v_start_824_);
if (v___x_827_ == 0)
{
v___y_830_ = v___x_827_;
goto v___jp_829_;
}
else
{
uint8_t v___x_859_; 
v___x_859_ = lean_nat_dec_lt(v_i_821_, v___x_828_);
v___y_830_ = v___x_859_;
goto v___jp_829_;
}
v___jp_829_:
{
if (v___y_830_ == 0)
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_831_ = lean_nat_sub(v___x_826_, v_i_821_);
lean_dec(v___x_826_);
lean_inc_ref(v_left_819_);
v___x_832_ = l_Subarray_take___redArg(v_left_819_, v___x_831_);
v___x_833_ = lean_nat_sub(v___x_828_, v_i_821_);
lean_dec(v_i_821_);
lean_dec(v___x_828_);
v___x_834_ = l_Subarray_take___redArg(v_right_820_, v___x_833_);
lean_dec(v___x_833_);
v___x_835_ = l_Subarray_drop___redArg(v_left_819_, v___x_831_);
lean_dec(v___x_831_);
v___x_836_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_837_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(v___x_835_, v___x_836_);
v___x_838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_834_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_832_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
return v___x_839_;
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; uint32_t v___x_847_; uint32_t v___x_848_; uint8_t v___x_849_; 
v___x_840_ = lean_nat_sub(v___x_826_, v_i_821_);
lean_dec(v___x_826_);
v___x_841_ = lean_unsigned_to_nat(1u);
v___x_842_ = lean_nat_sub(v___x_840_, v___x_841_);
v___x_843_ = l_Subarray_get___redArg(v_left_819_, v___x_842_);
lean_dec(v___x_842_);
v___x_844_ = lean_nat_sub(v___x_828_, v_i_821_);
lean_dec(v___x_828_);
v___x_845_ = lean_nat_sub(v___x_844_, v___x_841_);
v___x_846_ = l_Subarray_get___redArg(v_right_820_, v___x_845_);
lean_dec(v___x_845_);
v___x_847_ = lean_unbox_uint32(v___x_843_);
lean_dec(v___x_843_);
v___x_848_ = lean_unbox_uint32(v___x_846_);
lean_dec(v___x_846_);
v___x_849_ = lean_uint32_dec_eq(v___x_847_, v___x_848_);
if (v___x_849_ == 0)
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; 
lean_dec(v_i_821_);
lean_inc_ref(v_left_819_);
v___x_850_ = l_Subarray_take___redArg(v_left_819_, v___x_840_);
v___x_851_ = l_Subarray_take___redArg(v_right_820_, v___x_844_);
lean_dec(v___x_844_);
v___x_852_ = l_Subarray_drop___redArg(v_left_819_, v___x_840_);
lean_dec(v___x_840_);
v___x_853_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_854_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(v___x_852_, v___x_853_);
v___x_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_851_);
lean_ctor_set(v___x_855_, 1, v___x_854_);
v___x_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_850_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
return v___x_856_;
}
else
{
lean_object* v___x_857_; 
lean_dec(v___x_844_);
lean_dec(v___x_840_);
v___x_857_ = lean_nat_add(v_i_821_, v___x_841_);
lean_dec(v_i_821_);
v_i_821_ = v___x_857_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6(lean_object* v_left_860_, lean_object* v_right_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_862_ = lean_unsigned_to_nat(0u);
v___x_863_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8(v_left_860_, v_right_861_, v___x_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(lean_object* v_x_864_, lean_object* v_x_865_){
_start:
{
if (lean_obj_tag(v_x_865_) == 0)
{
lean_inc(v_x_864_);
return v_x_864_;
}
else
{
lean_object* v_key_866_; lean_object* v_value_867_; lean_object* v_tail_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v_key_866_ = lean_ctor_get(v_x_865_, 0);
v_value_867_ = lean_ctor_get(v_x_865_, 1);
v_tail_868_ = lean_ctor_get(v_x_865_, 2);
v___x_869_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(v_x_864_, v_tail_868_);
lean_inc(v_value_867_);
lean_inc(v_key_866_);
v___x_870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_870_, 0, v_key_866_);
lean_ctor_set(v___x_870_, 1, v_value_867_);
v___x_871_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_870_);
lean_ctor_set(v___x_871_, 1, v___x_869_);
return v___x_871_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8___boxed(lean_object* v_x_872_, lean_object* v_x_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(v_x_872_, v_x_873_);
lean_dec(v_x_873_);
lean_dec(v_x_872_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9(lean_object* v_as_875_, size_t v_i_876_, size_t v_stop_877_, lean_object* v_b_878_){
_start:
{
uint8_t v___x_879_; 
v___x_879_ = lean_usize_dec_eq(v_i_876_, v_stop_877_);
if (v___x_879_ == 0)
{
size_t v___x_880_; size_t v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_880_ = ((size_t)1ULL);
v___x_881_ = lean_usize_sub(v_i_876_, v___x_880_);
v___x_882_ = lean_array_uget_borrowed(v_as_875_, v___x_881_);
v___x_883_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(v_b_878_, v___x_882_);
lean_dec(v_b_878_);
v_i_876_ = v___x_881_;
v_b_878_ = v___x_883_;
goto _start;
}
else
{
return v_b_878_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9___boxed(lean_object* v_as_885_, lean_object* v_i_886_, lean_object* v_stop_887_, lean_object* v_b_888_){
_start:
{
size_t v_i_boxed_889_; size_t v_stop_boxed_890_; lean_object* v_res_891_; 
v_i_boxed_889_ = lean_unbox_usize(v_i_886_);
lean_dec(v_i_886_);
v_stop_boxed_890_ = lean_unbox_usize(v_stop_887_);
lean_dec(v_stop_887_);
v_res_891_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9(v_as_885_, v_i_boxed_889_, v_stop_boxed_890_, v_b_888_);
lean_dec_ref(v_as_885_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5_spec__6(lean_object* v_left_892_, lean_object* v_right_893_, lean_object* v_pref_894_){
_start:
{
lean_object* v_start_895_; lean_object* v_stop_896_; lean_object* v_start_897_; lean_object* v_stop_898_; lean_object* v_i_899_; uint8_t v___y_901_; lean_object* v___x_917_; uint8_t v___x_918_; 
v_start_895_ = lean_ctor_get(v_left_892_, 1);
v_stop_896_ = lean_ctor_get(v_left_892_, 2);
v_start_897_ = lean_ctor_get(v_right_893_, 1);
v_stop_898_ = lean_ctor_get(v_right_893_, 2);
v_i_899_ = lean_array_get_size(v_pref_894_);
v___x_917_ = lean_nat_sub(v_stop_896_, v_start_895_);
v___x_918_ = lean_nat_dec_lt(v_i_899_, v___x_917_);
lean_dec(v___x_917_);
if (v___x_918_ == 0)
{
v___y_901_ = v___x_918_;
goto v___jp_900_;
}
else
{
lean_object* v___x_919_; uint8_t v___x_920_; 
v___x_919_ = lean_nat_sub(v_stop_898_, v_start_897_);
v___x_920_ = lean_nat_dec_lt(v_i_899_, v___x_919_);
lean_dec(v___x_919_);
v___y_901_ = v___x_920_;
goto v___jp_900_;
}
v___jp_900_:
{
if (v___y_901_ == 0)
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_902_ = l_Subarray_drop___redArg(v_left_892_, v_i_899_);
v___x_903_ = l_Subarray_drop___redArg(v_right_893_, v_i_899_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v_pref_894_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
return v___x_905_;
}
else
{
lean_object* v___x_906_; lean_object* v___x_907_; uint32_t v___x_908_; uint32_t v___x_909_; uint8_t v___x_910_; 
v___x_906_ = l_Subarray_get___redArg(v_left_892_, v_i_899_);
v___x_907_ = l_Subarray_get___redArg(v_right_893_, v_i_899_);
v___x_908_ = lean_unbox_uint32(v___x_906_);
v___x_909_ = lean_unbox_uint32(v___x_907_);
lean_dec(v___x_907_);
v___x_910_ = lean_uint32_dec_eq(v___x_908_, v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec(v___x_906_);
v___x_911_ = l_Subarray_drop___redArg(v_left_892_, v_i_899_);
v___x_912_ = l_Subarray_drop___redArg(v_right_893_, v_i_899_);
v___x_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_911_);
lean_ctor_set(v___x_913_, 1, v___x_912_);
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v_pref_894_);
lean_ctor_set(v___x_914_, 1, v___x_913_);
return v___x_914_;
}
else
{
lean_object* v___x_915_; 
v___x_915_ = lean_array_push(v_pref_894_, v___x_906_);
v_pref_894_ = v___x_915_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5(lean_object* v_left_921_, lean_object* v_right_922_){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_924_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5_spec__6(v_left_921_, v_right_922_, v___x_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(lean_object* v_histogram_925_, lean_object* v_index_926_, uint32_t v_val_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_histogram_925_, v_val_927_);
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
v___x_934_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_925_, v_val_927_, v___x_933_);
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
v___x_951_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_925_, v_val_927_, v___x_950_);
return v___x_951_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg___boxed(lean_object* v_histogram_957_, lean_object* v_index_958_, lean_object* v_val_959_){
_start:
{
uint32_t v_val_boxed_960_; lean_object* v_res_961_; 
v_val_boxed_960_ = lean_unbox_uint32(v_val_959_);
lean_dec(v_val_959_);
v_res_961_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(v_histogram_957_, v_index_958_, v_val_boxed_960_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(lean_object* v_upperBound_962_, lean_object* v_fst_963_, lean_object* v___x_964_, lean_object* v_fst_965_, lean_object* v_a_966_, lean_object* v_b_967_){
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
v___x_971_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(v_b_967_, v_a_966_, v___x_970_);
v___x_972_ = lean_unsigned_to_nat(1u);
v___x_973_ = lean_nat_add(v_a_966_, v___x_972_);
lean_dec(v_a_966_);
v_a_966_ = v___x_973_;
v_b_967_ = v___x_971_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg___boxed(lean_object* v_upperBound_975_, lean_object* v_fst_976_, lean_object* v___x_977_, lean_object* v_fst_978_, lean_object* v_a_979_, lean_object* v_b_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(v_upperBound_975_, v_fst_976_, v___x_977_, v_fst_978_, v_a_979_, v_b_980_);
lean_dec_ref(v_fst_978_);
lean_dec(v___x_977_);
lean_dec_ref(v_fst_976_);
lean_dec(v_upperBound_975_);
return v_res_981_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_982_ = lean_box(0);
v___x_983_ = lean_unsigned_to_nat(16u);
v___x_984_ = lean_mk_array(v___x_983_, v___x_982_);
return v___x_984_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1(void){
_start:
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v_hist_987_; 
v___x_985_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0);
v___x_986_ = lean_unsigned_to_nat(0u);
v_hist_987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_987_, 0, v___x_986_);
lean_ctor_set(v_hist_987_, 1, v___x_985_);
return v_hist_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(lean_object* v_left_988_, lean_object* v_right_989_){
_start:
{
lean_object* v___x_990_; lean_object* v_snd_991_; lean_object* v_fst_992_; lean_object* v_fst_993_; lean_object* v_snd_994_; lean_object* v___x_995_; lean_object* v_snd_996_; lean_object* v_fst_997_; lean_object* v_fst_998_; lean_object* v_snd_999_; lean_object* v_start_1000_; lean_object* v_stop_1001_; lean_object* v___x_1002_; lean_object* v_hist_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v_start_1006_; lean_object* v_stop_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v_buckets_1010_; lean_object* v___x_1011_; lean_object* v___y_1013_; lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_990_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5(v_left_988_, v_right_989_);
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
v___x_995_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6(v_fst_993_, v_snd_994_);
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
v_hist_1003_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1);
v___x_1004_ = lean_nat_sub(v_stop_1001_, v_start_1000_);
v___x_1005_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(v___x_1004_, v_fst_998_, v___x_1004_, v_fst_997_, v___x_1002_, v_hist_1003_);
v_start_1006_ = lean_ctor_get(v_fst_998_, 1);
v_stop_1007_ = lean_ctor_get(v_fst_998_, 2);
v___x_1008_ = lean_nat_sub(v_stop_1007_, v_start_1006_);
v___x_1009_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(v___x_1008_, v___x_1008_, v_fst_998_, v___x_1004_, v___x_1002_, v___x_1005_);
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
v___x_1044_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9(v_buckets_1010_, v___x_1042_, v___x_1043_, v___x_1039_);
lean_dec_ref(v_buckets_1010_);
v___y_1013_ = v___x_1044_;
goto v___jp_1012_;
}
v___jp_1012_:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(v___y_1013_, v___x_1011_);
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
v___x_1027_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v_fst_1022_, v_fst_1025_);
v___x_1028_ = l_Array_append___redArg(v_fst_992_, v___x_1027_);
lean_dec_ref(v___x_1027_);
v___x_1029_ = lean_unsigned_to_nat(1u);
v___x_1030_ = lean_mk_empty_array_with_capacity(v___x_1029_);
v___x_1031_ = lean_array_push(v___x_1030_, v_fst_1018_);
v___x_1032_ = l_Array_append___redArg(v___x_1028_, v___x_1031_);
lean_dec_ref(v___x_1031_);
v___x_1033_ = l_Subarray_drop___redArg(v_snd_1023_, v___x_1029_);
v___x_1034_ = l_Subarray_drop___redArg(v_snd_1026_, v___x_1029_);
v___x_1035_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v___x_1033_, v___x_1034_);
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
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = 65;
v___x_1094_ = lean_box_uint32(v___x_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(lean_object* v___x_1095_, lean_object* v_original_1096_, uint32_t v_a_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v_fst_1099_; lean_object* v_snd_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1125_; 
v_fst_1099_ = lean_ctor_get(v_a_1098_, 0);
v_snd_1100_ = lean_ctor_get(v_a_1098_, 1);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_a_1098_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1102_ = v_a_1098_;
v_isShared_1103_ = v_isSharedCheck_1125_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_snd_1100_);
lean_inc(v_fst_1099_);
lean_dec(v_a_1098_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1125_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
uint8_t v___x_1104_; 
v___x_1104_ = lean_nat_dec_lt(v_snd_1100_, v___x_1095_);
if (v___x_1104_ == 0)
{
lean_object* v___x_1106_; 
if (v_isShared_1103_ == 0)
{
v___x_1106_ = v___x_1102_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_fst_1099_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_snd_1100_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
else
{
lean_object* v___x_1108_; lean_object* v___x_1109_; uint32_t v___x_1110_; uint8_t v___x_1111_; 
v___x_1108_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed__const__1;
v___x_1109_ = lean_array_get_borrowed(v___x_1108_, v_original_1096_, v_snd_1100_);
v___x_1110_ = lean_unbox_uint32(v___x_1109_);
v___x_1111_ = lean_uint32_dec_eq(v___x_1110_, v_a_1097_);
if (v___x_1111_ == 0)
{
uint8_t v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1115_; 
v___x_1112_ = 1;
v___x_1113_ = lean_box(v___x_1112_);
lean_inc(v___x_1109_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 1, v___x_1109_);
lean_ctor_set(v___x_1102_, 0, v___x_1113_);
v___x_1115_ = v___x_1102_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1113_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v___x_1109_);
v___x_1115_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1116_ = lean_array_push(v_fst_1099_, v___x_1115_);
v___x_1117_ = lean_unsigned_to_nat(1u);
v___x_1118_ = lean_nat_add(v_snd_1100_, v___x_1117_);
lean_dec(v_snd_1100_);
v___x_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1116_);
lean_ctor_set(v___x_1119_, 1, v___x_1118_);
v_a_1098_ = v___x_1119_;
goto _start;
}
}
else
{
lean_object* v___x_1123_; 
if (v_isShared_1103_ == 0)
{
v___x_1123_ = v___x_1102_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_fst_1099_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_snd_1100_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed(lean_object* v___x_1126_, lean_object* v_original_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_){
_start:
{
uint32_t v_a_boxed_1130_; lean_object* v_res_1131_; 
v_a_boxed_1130_ = lean_unbox_uint32(v_a_1128_);
lean_dec(v_a_1128_);
v_res_1131_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1126_, v_original_1127_, v_a_boxed_1130_, v_a_1129_);
lean_dec_ref(v_original_1127_);
lean_dec(v___x_1126_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(lean_object* v___x_1132_, lean_object* v_edited_1133_, uint32_t v_a_1134_, lean_object* v_a_1135_){
_start:
{
lean_object* v_fst_1136_; lean_object* v_snd_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1162_; 
v_fst_1136_ = lean_ctor_get(v_a_1135_, 0);
v_snd_1137_ = lean_ctor_get(v_a_1135_, 1);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_a_1135_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1139_ = v_a_1135_;
v_isShared_1140_ = v_isSharedCheck_1162_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_snd_1137_);
lean_inc(v_fst_1136_);
lean_dec(v_a_1135_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1162_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
uint8_t v___x_1141_; 
v___x_1141_ = lean_nat_dec_lt(v_snd_1137_, v___x_1132_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1143_; 
if (v_isShared_1140_ == 0)
{
v___x_1143_ = v___x_1139_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_fst_1136_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_snd_1137_);
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
lean_object* v___x_1145_; lean_object* v___x_1146_; uint32_t v___x_1147_; uint8_t v___x_1148_; 
v___x_1145_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed__const__1;
v___x_1146_ = lean_array_get_borrowed(v___x_1145_, v_edited_1133_, v_snd_1137_);
v___x_1147_ = lean_unbox_uint32(v___x_1146_);
v___x_1148_ = lean_uint32_dec_eq(v___x_1147_, v_a_1134_);
if (v___x_1148_ == 0)
{
uint8_t v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1149_ = 0;
v___x_1150_ = lean_box(v___x_1149_);
lean_inc(v___x_1146_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v___x_1146_);
lean_ctor_set(v___x_1139_, 0, v___x_1150_);
v___x_1152_ = v___x_1139_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1150_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v___x_1146_);
v___x_1152_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1153_ = lean_array_push(v_fst_1136_, v___x_1152_);
v___x_1154_ = lean_unsigned_to_nat(1u);
v___x_1155_ = lean_nat_add(v_snd_1137_, v___x_1154_);
lean_dec(v_snd_1137_);
v___x_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1153_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
v_a_1135_ = v___x_1156_;
goto _start;
}
}
else
{
lean_object* v___x_1160_; 
if (v_isShared_1140_ == 0)
{
v___x_1160_ = v___x_1139_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_fst_1136_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_snd_1137_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg___boxed(lean_object* v___x_1163_, lean_object* v_edited_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_){
_start:
{
uint32_t v_a_boxed_1167_; lean_object* v_res_1168_; 
v_a_boxed_1167_ = lean_unbox_uint32(v_a_1165_);
lean_dec(v_a_1165_);
v_res_1168_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1163_, v_edited_1164_, v_a_boxed_1167_, v_a_1166_);
lean_dec_ref(v_edited_1164_);
lean_dec(v___x_1163_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(lean_object* v___x_1169_, lean_object* v_original_1170_, lean_object* v___x_1171_, lean_object* v_edited_1172_, lean_object* v_as_1173_, size_t v_sz_1174_, size_t v_i_1175_, lean_object* v_b_1176_){
_start:
{
uint8_t v___x_1177_; 
v___x_1177_ = lean_usize_dec_lt(v_i_1175_, v_sz_1174_);
if (v___x_1177_ == 0)
{
return v_b_1176_;
}
else
{
lean_object* v_snd_1178_; lean_object* v_fst_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1228_; 
v_snd_1178_ = lean_ctor_get(v_b_1176_, 1);
v_fst_1179_ = lean_ctor_get(v_b_1176_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v_b_1176_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1181_ = v_b_1176_;
v_isShared_1182_ = v_isSharedCheck_1228_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_snd_1178_);
lean_inc(v_fst_1179_);
lean_dec(v_b_1176_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1228_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v_fst_1183_; lean_object* v_snd_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1227_; 
v_fst_1183_ = lean_ctor_get(v_snd_1178_, 0);
v_snd_1184_ = lean_ctor_get(v_snd_1178_, 1);
v_isSharedCheck_1227_ = !lean_is_exclusive(v_snd_1178_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1186_ = v_snd_1178_;
v_isShared_1187_ = v_isSharedCheck_1227_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_snd_1184_);
lean_inc(v_fst_1183_);
lean_dec(v_snd_1178_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1227_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v_a_1188_; lean_object* v___x_1190_; 
v_a_1188_ = lean_array_uget_borrowed(v_as_1173_, v_i_1175_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 1, v_fst_1183_);
lean_ctor_set(v___x_1186_, 0, v_fst_1179_);
v___x_1190_ = v___x_1186_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_fst_1179_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_fst_1183_);
v___x_1190_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
uint32_t v___x_1191_; lean_object* v___x_1192_; lean_object* v_fst_1193_; lean_object* v_snd_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1225_; 
v___x_1191_ = lean_unbox_uint32(v_a_1188_);
v___x_1192_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1169_, v_original_1170_, v___x_1191_, v___x_1190_);
v_fst_1193_ = lean_ctor_get(v___x_1192_, 0);
v_snd_1194_ = lean_ctor_get(v___x_1192_, 1);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1196_ = v___x_1192_;
v_isShared_1197_ = v_isSharedCheck_1225_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_snd_1194_);
lean_inc(v_fst_1193_);
lean_dec(v___x_1192_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1225_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 1, v_snd_1184_);
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_fst_1193_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_snd_1184_);
v___x_1199_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
uint32_t v___x_1200_; lean_object* v___x_1201_; lean_object* v_fst_1202_; lean_object* v_snd_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1223_; 
v___x_1200_ = lean_unbox_uint32(v_a_1188_);
v___x_1201_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1171_, v_edited_1172_, v___x_1200_, v___x_1199_);
v_fst_1202_ = lean_ctor_get(v___x_1201_, 0);
v_snd_1203_ = lean_ctor_get(v___x_1201_, 1);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1205_ = v___x_1201_;
v_isShared_1206_ = v_isSharedCheck_1223_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_snd_1203_);
lean_inc(v_fst_1202_);
lean_dec(v___x_1201_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1223_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
uint8_t v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1210_; 
v___x_1207_ = 2;
v___x_1208_ = lean_box(v___x_1207_);
lean_inc(v_a_1188_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 1, v_a_1188_);
lean_ctor_set(v___x_1205_, 0, v___x_1208_);
v___x_1210_ = v___x_1205_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_a_1188_);
v___x_1210_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1211_ = lean_array_push(v_fst_1202_, v___x_1210_);
v___x_1212_ = lean_unsigned_to_nat(1u);
v___x_1213_ = lean_nat_add(v_snd_1194_, v___x_1212_);
lean_dec(v_snd_1194_);
v___x_1214_ = lean_nat_add(v_snd_1203_, v___x_1212_);
lean_dec(v_snd_1203_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 1, v___x_1214_);
lean_ctor_set(v___x_1181_, 0, v___x_1213_);
v___x_1216_ = v___x_1181_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v___x_1213_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
lean_object* v___x_1217_; size_t v___x_1218_; size_t v___x_1219_; 
v___x_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1211_);
lean_ctor_set(v___x_1217_, 1, v___x_1216_);
v___x_1218_ = ((size_t)1ULL);
v___x_1219_ = lean_usize_add(v_i_1175_, v___x_1218_);
v_i_1175_ = v___x_1219_;
v_b_1176_ = v___x_1217_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15___boxed(lean_object* v___x_1229_, lean_object* v_original_1230_, lean_object* v___x_1231_, lean_object* v_edited_1232_, lean_object* v_as_1233_, lean_object* v_sz_1234_, lean_object* v_i_1235_, lean_object* v_b_1236_){
_start:
{
size_t v_sz_boxed_1237_; size_t v_i_boxed_1238_; lean_object* v_res_1239_; 
v_sz_boxed_1237_ = lean_unbox_usize(v_sz_1234_);
lean_dec(v_sz_1234_);
v_i_boxed_1238_ = lean_unbox_usize(v_i_1235_);
lean_dec(v_i_1235_);
v_res_1239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(v___x_1229_, v_original_1230_, v___x_1231_, v_edited_1232_, v_as_1233_, v_sz_boxed_1237_, v_i_boxed_1238_, v_b_1236_);
lean_dec_ref(v_as_1233_);
lean_dec_ref(v_edited_1232_);
lean_dec(v___x_1231_);
lean_dec_ref(v_original_1230_);
lean_dec(v___x_1229_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(lean_object* v___x_1240_, lean_object* v_edited_1241_, lean_object* v___x_1242_, lean_object* v_original_1243_, lean_object* v_as_1244_, size_t v_sz_1245_, size_t v_i_1246_, lean_object* v_b_1247_){
_start:
{
uint8_t v___x_1248_; 
v___x_1248_ = lean_usize_dec_lt(v_i_1246_, v_sz_1245_);
if (v___x_1248_ == 0)
{
return v_b_1247_;
}
else
{
lean_object* v_snd_1249_; lean_object* v_fst_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1299_; 
v_snd_1249_ = lean_ctor_get(v_b_1247_, 1);
v_fst_1250_ = lean_ctor_get(v_b_1247_, 0);
v_isSharedCheck_1299_ = !lean_is_exclusive(v_b_1247_);
if (v_isSharedCheck_1299_ == 0)
{
v___x_1252_ = v_b_1247_;
v_isShared_1253_ = v_isSharedCheck_1299_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_snd_1249_);
lean_inc(v_fst_1250_);
lean_dec(v_b_1247_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1299_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v_fst_1254_; lean_object* v_snd_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1298_; 
v_fst_1254_ = lean_ctor_get(v_snd_1249_, 0);
v_snd_1255_ = lean_ctor_get(v_snd_1249_, 1);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_snd_1249_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1257_ = v_snd_1249_;
v_isShared_1258_ = v_isSharedCheck_1298_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_snd_1255_);
lean_inc(v_fst_1254_);
lean_dec(v_snd_1249_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1298_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v_a_1259_; lean_object* v___x_1261_; 
v_a_1259_ = lean_array_uget_borrowed(v_as_1244_, v_i_1246_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 1, v_fst_1254_);
lean_ctor_set(v___x_1257_, 0, v_fst_1250_);
v___x_1261_ = v___x_1257_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_fst_1250_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v_fst_1254_);
v___x_1261_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
uint32_t v___x_1262_; lean_object* v___x_1263_; lean_object* v_fst_1264_; lean_object* v_snd_1265_; lean_object* v___x_1267_; uint8_t v_isShared_1268_; uint8_t v_isSharedCheck_1296_; 
v___x_1262_ = lean_unbox_uint32(v_a_1259_);
v___x_1263_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1242_, v_original_1243_, v___x_1262_, v___x_1261_);
v_fst_1264_ = lean_ctor_get(v___x_1263_, 0);
v_snd_1265_ = lean_ctor_get(v___x_1263_, 1);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1267_ = v___x_1263_;
v_isShared_1268_ = v_isSharedCheck_1296_;
goto v_resetjp_1266_;
}
else
{
lean_inc(v_snd_1265_);
lean_inc(v_fst_1264_);
lean_dec(v___x_1263_);
v___x_1267_ = lean_box(0);
v_isShared_1268_ = v_isSharedCheck_1296_;
goto v_resetjp_1266_;
}
v_resetjp_1266_:
{
lean_object* v___x_1270_; 
if (v_isShared_1268_ == 0)
{
lean_ctor_set(v___x_1267_, 1, v_snd_1255_);
v___x_1270_ = v___x_1267_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v_fst_1264_);
lean_ctor_set(v_reuseFailAlloc_1295_, 1, v_snd_1255_);
v___x_1270_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
uint32_t v___x_1271_; lean_object* v___x_1272_; lean_object* v_fst_1273_; lean_object* v_snd_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1294_; 
v___x_1271_ = lean_unbox_uint32(v_a_1259_);
v___x_1272_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1240_, v_edited_1241_, v___x_1271_, v___x_1270_);
v_fst_1273_ = lean_ctor_get(v___x_1272_, 0);
v_snd_1274_ = lean_ctor_get(v___x_1272_, 1);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1276_ = v___x_1272_;
v_isShared_1277_ = v_isSharedCheck_1294_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_snd_1274_);
lean_inc(v_fst_1273_);
lean_dec(v___x_1272_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1294_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
uint8_t v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1281_; 
v___x_1278_ = 2;
v___x_1279_ = lean_box(v___x_1278_);
lean_inc(v_a_1259_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 1, v_a_1259_);
lean_ctor_set(v___x_1276_, 0, v___x_1279_);
v___x_1281_ = v___x_1276_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v___x_1279_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_a_1259_);
v___x_1281_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1287_; 
v___x_1282_ = lean_array_push(v_fst_1273_, v___x_1281_);
v___x_1283_ = lean_unsigned_to_nat(1u);
v___x_1284_ = lean_nat_add(v_snd_1265_, v___x_1283_);
lean_dec(v_snd_1265_);
v___x_1285_ = lean_nat_add(v_snd_1274_, v___x_1283_);
lean_dec(v_snd_1274_);
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 1, v___x_1285_);
lean_ctor_set(v___x_1252_, 0, v___x_1284_);
v___x_1287_ = v___x_1252_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1284_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v___x_1285_);
v___x_1287_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v___x_1288_; size_t v___x_1289_; size_t v___x_1290_; lean_object* v___x_1291_; 
v___x_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1288_, 0, v___x_1282_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
v___x_1289_ = ((size_t)1ULL);
v___x_1290_ = lean_usize_add(v_i_1246_, v___x_1289_);
v___x_1291_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(v___x_1242_, v_original_1243_, v___x_1240_, v_edited_1241_, v_as_1244_, v_sz_1245_, v___x_1290_, v___x_1288_);
return v___x_1291_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5___boxed(lean_object* v___x_1300_, lean_object* v_edited_1301_, lean_object* v___x_1302_, lean_object* v_original_1303_, lean_object* v_as_1304_, lean_object* v_sz_1305_, lean_object* v_i_1306_, lean_object* v_b_1307_){
_start:
{
size_t v_sz_boxed_1308_; size_t v_i_boxed_1309_; lean_object* v_res_1310_; 
v_sz_boxed_1308_ = lean_unbox_usize(v_sz_1305_);
lean_dec(v_sz_1305_);
v_i_boxed_1309_ = lean_unbox_usize(v_i_1306_);
lean_dec(v_i_1306_);
v_res_1310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v___x_1300_, v_edited_1301_, v___x_1302_, v_original_1303_, v_as_1304_, v_sz_boxed_1308_, v_i_boxed_1309_, v_b_1307_);
lean_dec_ref(v_as_1304_);
lean_dec_ref(v_original_1303_);
lean_dec(v___x_1302_);
lean_dec_ref(v_edited_1301_);
lean_dec(v___x_1300_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(lean_object* v_original_1318_, lean_object* v_edited_1319_){
_start:
{
lean_object* v_i_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v_i_1320_ = lean_unsigned_to_nat(0u);
v___x_1321_ = lean_array_get_size(v_original_1318_);
v___x_1322_ = lean_nat_dec_lt(v_i_1320_, v___x_1321_);
if (v___x_1322_ == 0)
{
size_t v_sz_1323_; size_t v___x_1324_; lean_object* v___x_1325_; 
lean_dec_ref(v_original_1318_);
v_sz_1323_ = lean_array_size(v_edited_1319_);
v___x_1324_ = ((size_t)0ULL);
v___x_1325_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(v_sz_1323_, v___x_1324_, v_edited_1319_);
return v___x_1325_;
}
else
{
lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1326_ = lean_array_get_size(v_edited_1319_);
v___x_1327_ = lean_nat_dec_lt(v_i_1320_, v___x_1326_);
if (v___x_1327_ == 0)
{
size_t v_sz_1328_; size_t v___x_1329_; lean_object* v___x_1330_; 
lean_dec_ref(v_edited_1319_);
v_sz_1328_ = lean_array_size(v_original_1318_);
v___x_1329_ = ((size_t)0ULL);
v___x_1330_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(v_sz_1328_, v___x_1329_, v_original_1318_);
return v___x_1330_;
}
else
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v_ds_1333_; lean_object* v___x_1334_; size_t v_sz_1335_; size_t v___x_1336_; lean_object* v___x_1337_; lean_object* v_snd_1338_; lean_object* v_fst_1339_; lean_object* v_fst_1340_; lean_object* v_snd_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1360_; 
lean_inc_ref(v_original_1318_);
v___x_1331_ = l_Array_toSubarray___redArg(v_original_1318_, v_i_1320_, v___x_1321_);
lean_inc_ref(v_edited_1319_);
v___x_1332_ = l_Array_toSubarray___redArg(v_edited_1319_, v_i_1320_, v___x_1326_);
v_ds_1333_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v___x_1331_, v___x_1332_);
v___x_1334_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__2));
v_sz_1335_ = lean_array_size(v_ds_1333_);
v___x_1336_ = ((size_t)0ULL);
v___x_1337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v___x_1326_, v_edited_1319_, v___x_1321_, v_original_1318_, v_ds_1333_, v_sz_1335_, v___x_1336_, v___x_1334_);
lean_dec_ref(v_ds_1333_);
v_snd_1338_ = lean_ctor_get(v___x_1337_, 1);
lean_inc(v_snd_1338_);
v_fst_1339_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_fst_1339_);
lean_dec_ref(v___x_1337_);
v_fst_1340_ = lean_ctor_get(v_snd_1338_, 0);
v_snd_1341_ = lean_ctor_get(v_snd_1338_, 1);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_snd_1338_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1343_ = v_snd_1338_;
v_isShared_1344_ = v_isSharedCheck_1360_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_snd_1341_);
lean_inc(v_fst_1340_);
lean_dec(v_snd_1338_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1360_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 1, v_fst_1340_);
lean_ctor_set(v___x_1343_, 0, v_fst_1339_);
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v_fst_1339_);
lean_ctor_set(v_reuseFailAlloc_1359_, 1, v_fst_1340_);
v___x_1346_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
lean_object* v___x_1347_; lean_object* v_fst_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1357_; 
v___x_1347_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_1321_, v_original_1318_, v___x_1346_);
lean_dec_ref(v_original_1318_);
v_fst_1348_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1357_ == 0)
{
lean_object* v_unused_1358_; 
v_unused_1358_ = lean_ctor_get(v___x_1347_, 1);
lean_dec(v_unused_1358_);
v___x_1350_ = v___x_1347_;
v_isShared_1351_ = v_isSharedCheck_1357_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_fst_1348_);
lean_dec(v___x_1347_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1357_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1353_; 
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 1, v_snd_1341_);
v___x_1353_ = v___x_1350_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_fst_1348_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_snd_1341_);
v___x_1353_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1354_; lean_object* v_fst_1355_; 
v___x_1354_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1326_, v_edited_1319_, v___x_1353_);
lean_dec_ref(v_edited_1319_);
v_fst_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_fst_1355_);
lean_dec_ref(v___x_1354_);
return v_fst_1355_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(lean_object* v_s_1361_, lean_object* v_a_1362_, uint8_t v_b_1363_){
_start:
{
lean_object* v_str_1364_; lean_object* v_startInclusive_1365_; lean_object* v_endExclusive_1366_; lean_object* v___x_1367_; uint8_t v_decide_1368_; 
v_str_1364_ = lean_ctor_get(v_s_1361_, 0);
v_startInclusive_1365_ = lean_ctor_get(v_s_1361_, 1);
v_endExclusive_1366_ = lean_ctor_get(v_s_1361_, 2);
v___x_1367_ = lean_nat_sub(v_endExclusive_1366_, v_startInclusive_1365_);
v_decide_1368_ = lean_nat_dec_eq(v_a_1362_, v___x_1367_);
lean_dec(v___x_1367_);
if (v_decide_1368_ == 0)
{
lean_object* v___x_1369_; uint32_t v___x_1370_; uint32_t v___x_1371_; uint8_t v___x_1372_; 
v___x_1369_ = lean_nat_add(v_startInclusive_1365_, v_a_1362_);
lean_dec(v_a_1362_);
v___x_1370_ = lean_string_utf8_get_fast(v_str_1364_, v___x_1369_);
v___x_1371_ = 10;
v___x_1372_ = lean_uint32_dec_eq(v___x_1370_, v___x_1371_);
if (v___x_1372_ == 0)
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1373_ = lean_string_utf8_next_fast(v_str_1364_, v___x_1369_);
lean_dec(v___x_1369_);
v___x_1374_ = lean_nat_sub(v___x_1373_, v_startInclusive_1365_);
v_a_1362_ = v___x_1374_;
v_b_1363_ = v___x_1372_;
goto _start;
}
else
{
lean_dec(v___x_1369_);
return v___x_1372_;
}
}
else
{
lean_dec(v_a_1362_);
return v_b_1363_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg___boxed(lean_object* v_s_1376_, lean_object* v_a_1377_, lean_object* v_b_1378_){
_start:
{
uint8_t v_b_boxed_1379_; uint8_t v_res_1380_; lean_object* v_r_1381_; 
v_b_boxed_1379_ = lean_unbox(v_b_1378_);
v_res_1380_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1376_, v_a_1377_, v_b_boxed_1379_);
lean_dec_ref(v_s_1376_);
v_r_1381_ = lean_box(v_res_1380_);
return v_r_1381_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(lean_object* v_s_1382_){
_start:
{
lean_object* v_searcher_1383_; uint8_t v___x_1384_; uint8_t v___x_1385_; 
v_searcher_1383_ = lean_unsigned_to_nat(0u);
v___x_1384_ = 0;
v___x_1385_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1382_, v_searcher_1383_, v___x_1384_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0___boxed(lean_object* v_s_1386_){
_start:
{
uint8_t v_res_1387_; lean_object* v_r_1388_; 
v_res_1387_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v_s_1386_);
lean_dec_ref(v_s_1386_);
v_r_1388_ = lean_box(v_res_1387_);
return v_r_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(lean_object* v_oldWs_1389_, lean_object* v_newWs_1390_){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1391_ = lean_unsigned_to_nat(0u);
v___x_1392_ = lean_string_utf8_byte_size(v_oldWs_1389_);
lean_inc_ref(v_oldWs_1389_);
v___x_1393_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1393_, 0, v_oldWs_1389_);
lean_ctor_set(v___x_1393_, 1, v___x_1391_);
lean_ctor_set(v___x_1393_, 2, v___x_1392_);
v___x_1394_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_1393_);
lean_dec_ref_known(v___x_1393_, 3);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1395_ = lean_string_data(v_oldWs_1389_);
v___x_1396_ = lean_array_mk(v___x_1395_);
v___x_1397_ = lean_string_data(v_newWs_1390_);
v___x_1398_ = lean_array_mk(v___x_1397_);
v___x_1399_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_1396_, v___x_1398_);
v___x_1400_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_1399_);
lean_dec_ref(v___x_1399_);
return v___x_1400_;
}
else
{
uint8_t v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
lean_dec_ref(v_oldWs_1389_);
v___x_1401_ = 2;
v___x_1402_ = lean_box(v___x_1401_);
v___x_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1402_);
lean_ctor_set(v___x_1403_, 1, v_newWs_1390_);
v___x_1404_ = lean_unsigned_to_nat(1u);
v___x_1405_ = lean_mk_empty_array_with_capacity(v___x_1404_);
v___x_1406_ = lean_array_push(v___x_1405_, v___x_1403_);
return v___x_1406_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(lean_object* v_s_1407_, lean_object* v_inst_1408_, lean_object* v_R_1409_, lean_object* v_a_1410_, uint8_t v_b_1411_, lean_object* v_c_1412_){
_start:
{
uint8_t v___x_1413_; 
v___x_1413_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1407_, v_a_1410_, v_b_1411_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___boxed(lean_object* v_s_1414_, lean_object* v_inst_1415_, lean_object* v_R_1416_, lean_object* v_a_1417_, lean_object* v_b_1418_, lean_object* v_c_1419_){
_start:
{
uint8_t v_b_boxed_1420_; uint8_t v_res_1421_; lean_object* v_r_1422_; 
v_b_boxed_1420_ = lean_unbox(v_b_1418_);
v_res_1421_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(v_s_1414_, v_inst_1415_, v_R_1416_, v_a_1417_, v_b_boxed_1420_, v_c_1419_);
lean_dec_ref(v_s_1414_);
v_r_1422_ = lean_box(v_res_1421_);
return v_r_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(lean_object* v___x_1423_, lean_object* v_original_1424_, uint32_t v_a_1425_, lean_object* v_inst_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1423_, v_original_1424_, v_a_1425_, v_a_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___boxed(lean_object* v___x_1429_, lean_object* v_original_1430_, lean_object* v_a_1431_, lean_object* v_inst_1432_, lean_object* v_a_1433_){
_start:
{
uint32_t v_a_boxed_1434_; lean_object* v_res_1435_; 
v_a_boxed_1434_ = lean_unbox_uint32(v_a_1431_);
lean_dec(v_a_1431_);
v_res_1435_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v___x_1429_, v_original_1430_, v_a_boxed_1434_, v_inst_1432_, v_a_1433_);
lean_dec_ref(v_original_1430_);
lean_dec(v___x_1429_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(lean_object* v___x_1436_, lean_object* v_edited_1437_, uint32_t v_a_1438_, lean_object* v_inst_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1436_, v_edited_1437_, v_a_1438_, v_a_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___boxed(lean_object* v___x_1442_, lean_object* v_edited_1443_, lean_object* v_a_1444_, lean_object* v_inst_1445_, lean_object* v_a_1446_){
_start:
{
uint32_t v_a_boxed_1447_; lean_object* v_res_1448_; 
v_a_boxed_1447_ = lean_unbox_uint32(v_a_1444_);
lean_dec(v_a_1444_);
v_res_1448_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(v___x_1442_, v_edited_1443_, v_a_boxed_1447_, v_inst_1445_, v_a_1446_);
lean_dec_ref(v_edited_1443_);
lean_dec(v___x_1442_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(lean_object* v___x_1449_, lean_object* v_original_1450_, lean_object* v_inst_1451_, lean_object* v_a_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_1449_, v_original_1450_, v_a_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___boxed(lean_object* v___x_1454_, lean_object* v_original_1455_, lean_object* v_inst_1456_, lean_object* v_a_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(v___x_1454_, v_original_1455_, v_inst_1456_, v_a_1457_);
lean_dec_ref(v_original_1455_);
lean_dec(v___x_1454_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(lean_object* v___x_1459_, lean_object* v_edited_1460_, lean_object* v_inst_1461_, lean_object* v_a_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1459_, v_edited_1460_, v_a_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___boxed(lean_object* v___x_1464_, lean_object* v_edited_1465_, lean_object* v_inst_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(v___x_1464_, v_edited_1465_, v_inst_1466_, v_a_1467_);
lean_dec_ref(v_edited_1465_);
lean_dec(v___x_1464_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7(lean_object* v_as_1469_, lean_object* v_as_x27_1470_, lean_object* v_b_1471_, lean_object* v_a_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(v_as_x27_1470_, v_b_1471_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___boxed(lean_object* v_as_1474_, lean_object* v_as_x27_1475_, lean_object* v_b_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7(v_as_1474_, v_as_x27_1475_, v_b_1476_, v_a_1477_);
lean_dec(v_as_x27_1475_);
lean_dec(v_as_1474_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10(lean_object* v_lsize_1479_, lean_object* v_rsize_1480_, lean_object* v_histogram_1481_, lean_object* v_index_1482_, uint32_t v_val_1483_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(v_histogram_1481_, v_index_1482_, v_val_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___boxed(lean_object* v_lsize_1485_, lean_object* v_rsize_1486_, lean_object* v_histogram_1487_, lean_object* v_index_1488_, lean_object* v_val_1489_){
_start:
{
uint32_t v_val_boxed_1490_; lean_object* v_res_1491_; 
v_val_boxed_1490_ = lean_unbox_uint32(v_val_1489_);
lean_dec(v_val_1489_);
v_res_1491_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10(v_lsize_1485_, v_rsize_1486_, v_histogram_1487_, v_index_1488_, v_val_boxed_1490_);
lean_dec(v_rsize_1486_);
lean_dec(v_lsize_1485_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11(lean_object* v_upperBound_1492_, lean_object* v___x_1493_, lean_object* v_fst_1494_, lean_object* v___x_1495_, lean_object* v_inst_1496_, lean_object* v_R_1497_, lean_object* v_a_1498_, lean_object* v_b_1499_, lean_object* v_c_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(v_upperBound_1492_, v___x_1493_, v_fst_1494_, v___x_1495_, v_a_1498_, v_b_1499_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___boxed(lean_object* v_upperBound_1502_, lean_object* v___x_1503_, lean_object* v_fst_1504_, lean_object* v___x_1505_, lean_object* v_inst_1506_, lean_object* v_R_1507_, lean_object* v_a_1508_, lean_object* v_b_1509_, lean_object* v_c_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11(v_upperBound_1502_, v___x_1503_, v_fst_1504_, v___x_1505_, v_inst_1506_, v_R_1507_, v_a_1508_, v_b_1509_, v_c_1510_);
lean_dec(v___x_1505_);
lean_dec_ref(v_fst_1504_);
lean_dec(v___x_1503_);
lean_dec(v_upperBound_1502_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12(lean_object* v_lsize_1512_, lean_object* v_rsize_1513_, lean_object* v_histogram_1514_, lean_object* v_index_1515_, uint32_t v_val_1516_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(v_histogram_1514_, v_index_1515_, v_val_1516_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___boxed(lean_object* v_lsize_1518_, lean_object* v_rsize_1519_, lean_object* v_histogram_1520_, lean_object* v_index_1521_, lean_object* v_val_1522_){
_start:
{
uint32_t v_val_boxed_1523_; lean_object* v_res_1524_; 
v_val_boxed_1523_ = lean_unbox_uint32(v_val_1522_);
lean_dec(v_val_1522_);
v_res_1524_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12(v_lsize_1518_, v_rsize_1519_, v_histogram_1520_, v_index_1521_, v_val_boxed_1523_);
lean_dec(v_rsize_1519_);
lean_dec(v_lsize_1518_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13(lean_object* v_upperBound_1525_, lean_object* v_fst_1526_, lean_object* v___x_1527_, lean_object* v_fst_1528_, lean_object* v_inst_1529_, lean_object* v_R_1530_, lean_object* v_a_1531_, lean_object* v_b_1532_, lean_object* v_c_1533_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(v_upperBound_1525_, v_fst_1526_, v___x_1527_, v_fst_1528_, v_a_1531_, v_b_1532_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___boxed(lean_object* v_upperBound_1535_, lean_object* v_fst_1536_, lean_object* v___x_1537_, lean_object* v_fst_1538_, lean_object* v_inst_1539_, lean_object* v_R_1540_, lean_object* v_a_1541_, lean_object* v_b_1542_, lean_object* v_c_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13(v_upperBound_1535_, v_fst_1536_, v___x_1537_, v_fst_1538_, v_inst_1539_, v_R_1540_, v_a_1541_, v_b_1542_, v_c_1543_);
lean_dec_ref(v_fst_1538_);
lean_dec(v___x_1537_);
lean_dec_ref(v_fst_1536_);
lean_dec(v_upperBound_1535_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13(lean_object* v_00_u03b2_1545_, lean_object* v_m_1546_, uint32_t v_a_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_m_1546_, v_a_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___boxed(lean_object* v_00_u03b2_1549_, lean_object* v_m_1550_, lean_object* v_a_1551_){
_start:
{
uint32_t v_a_boxed_1552_; lean_object* v_res_1553_; 
v_a_boxed_1552_ = lean_unbox_uint32(v_a_1551_);
lean_dec(v_a_1551_);
v_res_1553_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13(v_00_u03b2_1549_, v_m_1550_, v_a_boxed_1552_);
lean_dec_ref(v_m_1550_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14(lean_object* v_00_u03b2_1554_, lean_object* v_m_1555_, uint32_t v_a_1556_, lean_object* v_b_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_m_1555_, v_a_1556_, v_b_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___boxed(lean_object* v_00_u03b2_1559_, lean_object* v_m_1560_, lean_object* v_a_1561_, lean_object* v_b_1562_){
_start:
{
uint32_t v_a_boxed_1563_; lean_object* v_res_1564_; 
v_a_boxed_1563_ = lean_unbox_uint32(v_a_1561_);
lean_dec(v_a_1561_);
v_res_1564_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14(v_00_u03b2_1559_, v_m_1560_, v_a_boxed_1563_, v_b_1562_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14(lean_object* v_inst_1565_, lean_object* v_R_1566_, lean_object* v_a_1567_, lean_object* v_b_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(v_a_1567_, v_b_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20(lean_object* v_00_u03b2_1570_, uint32_t v_a_1571_, lean_object* v_x_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg(v_a_1571_, v_x_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___boxed(lean_object* v_00_u03b2_1574_, lean_object* v_a_1575_, lean_object* v_x_1576_){
_start:
{
uint32_t v_a_boxed_1577_; lean_object* v_res_1578_; 
v_a_boxed_1577_ = lean_unbox_uint32(v_a_1575_);
lean_dec(v_a_1575_);
v_res_1578_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20(v_00_u03b2_1574_, v_a_boxed_1577_, v_x_1576_);
lean_dec(v_x_1576_);
return v_res_1578_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22(lean_object* v_00_u03b2_1579_, uint32_t v_a_1580_, lean_object* v_x_1581_){
_start:
{
uint8_t v___x_1582_; 
v___x_1582_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(v_a_1580_, v_x_1581_);
return v___x_1582_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___boxed(lean_object* v_00_u03b2_1583_, lean_object* v_a_1584_, lean_object* v_x_1585_){
_start:
{
uint32_t v_a_boxed_1586_; uint8_t v_res_1587_; lean_object* v_r_1588_; 
v_a_boxed_1586_ = lean_unbox_uint32(v_a_1584_);
lean_dec(v_a_1584_);
v_res_1587_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22(v_00_u03b2_1583_, v_a_boxed_1586_, v_x_1585_);
lean_dec(v_x_1585_);
v_r_1588_ = lean_box(v_res_1587_);
return v_r_1588_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23(lean_object* v_00_u03b2_1589_, lean_object* v_data_1590_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23___redArg(v_data_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24(lean_object* v_00_u03b2_1592_, uint32_t v_a_1593_, lean_object* v_b_1594_, lean_object* v_x_1595_){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(v_a_1593_, v_b_1594_, v_x_1595_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___boxed(lean_object* v_00_u03b2_1597_, lean_object* v_a_1598_, lean_object* v_b_1599_, lean_object* v_x_1600_){
_start:
{
uint32_t v_a_boxed_1601_; lean_object* v_res_1602_; 
v_a_boxed_1601_ = lean_unbox_uint32(v_a_1598_);
lean_dec(v_a_1598_);
v_res_1602_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24(v_00_u03b2_1597_, v_a_boxed_1601_, v_b_1599_, v_x_1600_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28(lean_object* v_00_u03b2_1603_, lean_object* v_i_1604_, lean_object* v_source_1605_, lean_object* v_target_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28___redArg(v_i_1604_, v_source_1605_, v_target_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_1608_, lean_object* v_x_1609_, lean_object* v_x_1610_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29___redArg(v_x_1609_, v_x_1610_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(lean_object* v_s_1612_, lean_object* v_stopPos_1613_, lean_object* v_i_1614_){
_start:
{
uint8_t v___y_1616_; lean_object* v___x_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; 
v___x_1619_ = lean_unsigned_to_nat(1u);
v___x_1620_ = lean_nat_add(v_i_1614_, v___x_1619_);
v___x_1621_ = lean_nat_dec_le(v___x_1620_, v_stopPos_1613_);
lean_dec(v___x_1620_);
if (v___x_1621_ == 0)
{
return v_i_1614_;
}
else
{
if (v___x_1621_ == 0)
{
v___y_1616_ = v___x_1621_;
goto v___jp_1615_;
}
else
{
uint32_t v___x_1622_; uint32_t v___x_1623_; uint8_t v___x_1624_; 
v___x_1622_ = lean_string_utf8_get(v_s_1612_, v_i_1614_);
v___x_1623_ = 32;
v___x_1624_ = lean_uint32_dec_eq(v___x_1622_, v___x_1623_);
if (v___x_1624_ == 0)
{
uint32_t v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = 9;
v___x_1626_ = lean_uint32_dec_eq(v___x_1622_, v___x_1625_);
if (v___x_1626_ == 0)
{
uint32_t v___x_1627_; uint8_t v___x_1628_; 
v___x_1627_ = 13;
v___x_1628_ = lean_uint32_dec_eq(v___x_1622_, v___x_1627_);
if (v___x_1628_ == 0)
{
uint32_t v___x_1629_; uint8_t v___x_1630_; 
v___x_1629_ = 10;
v___x_1630_ = lean_uint32_dec_eq(v___x_1622_, v___x_1629_);
v___y_1616_ = v___x_1630_;
goto v___jp_1615_;
}
else
{
v___y_1616_ = v___x_1628_;
goto v___jp_1615_;
}
}
else
{
v___y_1616_ = v___x_1626_;
goto v___jp_1615_;
}
}
else
{
v___y_1616_ = v___x_1624_;
goto v___jp_1615_;
}
}
}
v___jp_1615_:
{
if (v___y_1616_ == 0)
{
return v_i_1614_;
}
else
{
lean_object* v___x_1617_; 
v___x_1617_ = lean_string_utf8_next(v_s_1612_, v_i_1614_);
lean_dec(v_i_1614_);
v_i_1614_ = v___x_1617_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0___boxed(lean_object* v_s_1631_, lean_object* v_stopPos_1632_, lean_object* v_i_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1631_, v_stopPos_1632_, v_i_1633_);
lean_dec(v_stopPos_1632_);
lean_dec_ref(v_s_1631_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(lean_object* v_s_1635_, lean_object* v_b_1636_, lean_object* v_i_1637_, lean_object* v_r_1638_, lean_object* v_ws_1639_){
_start:
{
uint8_t v___x_1648_; 
v___x_1648_ = lean_string_utf8_at_end(v_s_1635_, v_i_1637_);
if (v___x_1648_ == 0)
{
uint32_t v___x_1649_; uint32_t v___x_1650_; uint8_t v___x_1651_; 
v___x_1649_ = lean_string_utf8_get(v_s_1635_, v_i_1637_);
v___x_1650_ = 32;
v___x_1651_ = lean_uint32_dec_eq(v___x_1649_, v___x_1650_);
if (v___x_1651_ == 0)
{
uint32_t v___x_1652_; uint8_t v___x_1653_; 
v___x_1652_ = 9;
v___x_1653_ = lean_uint32_dec_eq(v___x_1649_, v___x_1652_);
if (v___x_1653_ == 0)
{
uint32_t v___x_1654_; uint8_t v___x_1655_; 
v___x_1654_ = 13;
v___x_1655_ = lean_uint32_dec_eq(v___x_1649_, v___x_1654_);
if (v___x_1655_ == 0)
{
uint32_t v___x_1656_; uint8_t v___x_1657_; 
v___x_1656_ = 10;
v___x_1657_ = lean_uint32_dec_eq(v___x_1649_, v___x_1656_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; 
v___x_1658_ = lean_string_utf8_next(v_s_1635_, v_i_1637_);
lean_dec(v_i_1637_);
v_i_1637_ = v___x_1658_;
goto _start;
}
else
{
goto v___jp_1640_;
}
}
else
{
goto v___jp_1640_;
}
}
else
{
goto v___jp_1640_;
}
}
else
{
goto v___jp_1640_;
}
}
else
{
lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1660_ = lean_string_utf8_extract(v_s_1635_, v_b_1636_, v_i_1637_);
lean_dec(v_i_1637_);
lean_dec(v_b_1636_);
v___x_1661_ = lean_array_push(v_r_1638_, v___x_1660_);
v___x_1662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1662_, 0, v___x_1661_);
lean_ctor_set(v___x_1662_, 1, v_ws_1639_);
return v___x_1662_;
}
v___jp_1640_:
{
lean_object* v___x_1641_; lean_object* v_e_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1641_ = lean_string_utf8_byte_size(v_s_1635_);
lean_inc(v_i_1637_);
v_e_1642_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1635_, v___x_1641_, v_i_1637_);
v___x_1643_ = lean_string_utf8_extract(v_s_1635_, v_b_1636_, v_i_1637_);
lean_dec(v_b_1636_);
v___x_1644_ = lean_array_push(v_r_1638_, v___x_1643_);
v___x_1645_ = lean_string_utf8_extract(v_s_1635_, v_i_1637_, v_e_1642_);
lean_dec(v_i_1637_);
v___x_1646_ = lean_array_push(v_ws_1639_, v___x_1645_);
lean_inc(v_e_1642_);
v_b_1636_ = v_e_1642_;
v_i_1637_ = v_e_1642_;
v_r_1638_ = v___x_1644_;
v_ws_1639_ = v___x_1646_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux___boxed(lean_object* v_s_1663_, lean_object* v_b_1664_, lean_object* v_i_1665_, lean_object* v_r_1666_, lean_object* v_ws_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1663_, v_b_1664_, v_i_1665_, v_r_1666_, v_ws_1667_);
lean_dec_ref(v_s_1663_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(lean_object* v_s_1671_){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1672_ = lean_unsigned_to_nat(0u);
v___x_1673_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_1674_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1671_, v___x_1672_, v___x_1672_, v___x_1673_, v___x_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___boxed(lean_object* v_s_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_1675_);
lean_dec_ref(v_s_1675_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(size_t v_sz_1677_, size_t v_i_1678_, lean_object* v_bs_1679_){
_start:
{
uint8_t v___x_1680_; 
v___x_1680_ = lean_usize_dec_lt(v_i_1678_, v_sz_1677_);
if (v___x_1680_ == 0)
{
return v_bs_1679_;
}
else
{
lean_object* v_v_1681_; lean_object* v_fst_1682_; lean_object* v_snd_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1717_; 
v_v_1681_ = lean_array_uget(v_bs_1679_, v_i_1678_);
v_fst_1682_ = lean_ctor_get(v_v_1681_, 0);
v_snd_1683_ = lean_ctor_get(v_v_1681_, 1);
v_isSharedCheck_1717_ = !lean_is_exclusive(v_v_1681_);
if (v_isSharedCheck_1717_ == 0)
{
v___x_1685_ = v_v_1681_;
v_isShared_1686_ = v_isSharedCheck_1717_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_snd_1683_);
lean_inc(v_fst_1682_);
lean_dec(v_v_1681_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1717_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1687_; lean_object* v_bs_x27_1688_; lean_object* v___y_1690_; lean_object* v___x_1695_; lean_object* v___x_1696_; uint8_t v___x_1697_; 
v___x_1687_ = lean_unsigned_to_nat(0u);
v_bs_x27_1688_ = lean_array_uset(v_bs_1679_, v_i_1678_, v___x_1687_);
v___x_1695_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_1696_ = lean_array_get_size(v_snd_1683_);
v___x_1697_ = lean_nat_dec_lt(v___x_1687_, v___x_1696_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1699_; 
lean_dec(v_snd_1683_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 1, v___x_1695_);
v___x_1699_ = v___x_1685_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_fst_1682_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v___x_1695_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
v___y_1690_ = v___x_1699_;
goto v___jp_1689_;
}
}
else
{
uint8_t v___x_1701_; 
v___x_1701_ = lean_nat_dec_le(v___x_1696_, v___x_1696_);
if (v___x_1701_ == 0)
{
if (v___x_1697_ == 0)
{
lean_object* v___x_1703_; 
lean_dec(v_snd_1683_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 1, v___x_1695_);
v___x_1703_ = v___x_1685_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_fst_1682_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v___x_1695_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
v___y_1690_ = v___x_1703_;
goto v___jp_1689_;
}
}
else
{
size_t v___x_1705_; size_t v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1709_; 
v___x_1705_ = ((size_t)0ULL);
v___x_1706_ = lean_usize_of_nat(v___x_1696_);
v___x_1707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_1683_, v___x_1705_, v___x_1706_, v___x_1695_);
lean_dec(v_snd_1683_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 1, v___x_1707_);
v___x_1709_ = v___x_1685_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_fst_1682_);
lean_ctor_set(v_reuseFailAlloc_1710_, 1, v___x_1707_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
v___y_1690_ = v___x_1709_;
goto v___jp_1689_;
}
}
}
else
{
size_t v___x_1711_; size_t v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1711_ = ((size_t)0ULL);
v___x_1712_ = lean_usize_of_nat(v___x_1696_);
v___x_1713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_1683_, v___x_1711_, v___x_1712_, v___x_1695_);
lean_dec(v_snd_1683_);
if (v_isShared_1686_ == 0)
{
lean_ctor_set(v___x_1685_, 1, v___x_1713_);
v___x_1715_ = v___x_1685_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v_fst_1682_);
lean_ctor_set(v_reuseFailAlloc_1716_, 1, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
v___y_1690_ = v___x_1715_;
goto v___jp_1689_;
}
}
}
v___jp_1689_:
{
size_t v___x_1691_; size_t v___x_1692_; lean_object* v___x_1693_; 
v___x_1691_ = ((size_t)1ULL);
v___x_1692_ = lean_usize_add(v_i_1678_, v___x_1691_);
v___x_1693_ = lean_array_uset(v_bs_x27_1688_, v_i_1678_, v___y_1690_);
v_i_1678_ = v___x_1692_;
v_bs_1679_ = v___x_1693_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0___boxed(lean_object* v_sz_1718_, lean_object* v_i_1719_, lean_object* v_bs_1720_){
_start:
{
size_t v_sz_boxed_1721_; size_t v_i_boxed_1722_; lean_object* v_res_1723_; 
v_sz_boxed_1721_ = lean_unbox_usize(v_sz_1718_);
lean_dec(v_sz_1718_);
v_i_boxed_1722_ = lean_unbox_usize(v_i_1719_);
lean_dec(v_i_1719_);
v_res_1723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_boxed_1721_, v_i_boxed_1722_, v_bs_1720_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(size_t v_sz_1724_, size_t v_i_1725_, lean_object* v_bs_1726_){
_start:
{
uint8_t v___x_1727_; 
v___x_1727_ = lean_usize_dec_lt(v_i_1725_, v_sz_1724_);
if (v___x_1727_ == 0)
{
return v_bs_1726_;
}
else
{
lean_object* v_v_1728_; lean_object* v___x_1729_; lean_object* v_bs_x27_1730_; uint8_t v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; size_t v___x_1734_; size_t v___x_1735_; lean_object* v___x_1736_; 
v_v_1728_ = lean_array_uget(v_bs_1726_, v_i_1725_);
v___x_1729_ = lean_unsigned_to_nat(0u);
v_bs_x27_1730_ = lean_array_uset(v_bs_1726_, v_i_1725_, v___x_1729_);
v___x_1731_ = 0;
v___x_1732_ = lean_box(v___x_1731_);
v___x_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1733_, 0, v___x_1732_);
lean_ctor_set(v___x_1733_, 1, v_v_1728_);
v___x_1734_ = ((size_t)1ULL);
v___x_1735_ = lean_usize_add(v_i_1725_, v___x_1734_);
v___x_1736_ = lean_array_uset(v_bs_x27_1730_, v_i_1725_, v___x_1733_);
v_i_1725_ = v___x_1735_;
v_bs_1726_ = v___x_1736_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8___boxed(lean_object* v_sz_1738_, lean_object* v_i_1739_, lean_object* v_bs_1740_){
_start:
{
size_t v_sz_boxed_1741_; size_t v_i_boxed_1742_; lean_object* v_res_1743_; 
v_sz_boxed_1741_ = lean_unbox_usize(v_sz_1738_);
lean_dec(v_sz_1738_);
v_i_boxed_1742_ = lean_unbox_usize(v_i_1739_);
lean_dec(v_i_1739_);
v_res_1743_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_boxed_1741_, v_i_boxed_1742_, v_bs_1740_);
return v_res_1743_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(lean_object* v_x_1744_, lean_object* v_x_1745_){
_start:
{
if (lean_obj_tag(v_x_1745_) == 0)
{
lean_inc(v_x_1744_);
return v_x_1744_;
}
else
{
lean_object* v_key_1746_; lean_object* v_value_1747_; lean_object* v_tail_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v_key_1746_ = lean_ctor_get(v_x_1745_, 0);
v_value_1747_ = lean_ctor_get(v_x_1745_, 1);
v_tail_1748_ = lean_ctor_get(v_x_1745_, 2);
v___x_1749_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(v_x_1744_, v_tail_1748_);
lean_inc(v_value_1747_);
lean_inc(v_key_1746_);
v___x_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1750_, 0, v_key_1746_);
lean_ctor_set(v___x_1750_, 1, v_value_1747_);
v___x_1751_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1751_, 0, v___x_1750_);
lean_ctor_set(v___x_1751_, 1, v___x_1749_);
return v___x_1751_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7___boxed(lean_object* v_x_1752_, lean_object* v_x_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(v_x_1752_, v_x_1753_);
lean_dec(v_x_1753_);
lean_dec(v_x_1752_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8(lean_object* v_as_1755_, size_t v_i_1756_, size_t v_stop_1757_, lean_object* v_b_1758_){
_start:
{
uint8_t v___x_1759_; 
v___x_1759_ = lean_usize_dec_eq(v_i_1756_, v_stop_1757_);
if (v___x_1759_ == 0)
{
size_t v___x_1760_; size_t v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1760_ = ((size_t)1ULL);
v___x_1761_ = lean_usize_sub(v_i_1756_, v___x_1760_);
v___x_1762_ = lean_array_uget_borrowed(v_as_1755_, v___x_1761_);
v___x_1763_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(v_b_1758_, v___x_1762_);
lean_dec(v_b_1758_);
v_i_1756_ = v___x_1761_;
v_b_1758_ = v___x_1763_;
goto _start;
}
else
{
return v_b_1758_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8___boxed(lean_object* v_as_1765_, lean_object* v_i_1766_, lean_object* v_stop_1767_, lean_object* v_b_1768_){
_start:
{
size_t v_i_boxed_1769_; size_t v_stop_boxed_1770_; lean_object* v_res_1771_; 
v_i_boxed_1769_ = lean_unbox_usize(v_i_1766_);
lean_dec(v_i_1766_);
v_stop_boxed_1770_ = lean_unbox_usize(v_stop_1767_);
lean_dec(v_stop_1767_);
v_res_1771_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8(v_as_1765_, v_i_boxed_1769_, v_stop_boxed_1770_, v_b_1768_);
lean_dec_ref(v_as_1765_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4_spec__6(lean_object* v_left_1772_, lean_object* v_right_1773_, lean_object* v_pref_1774_){
_start:
{
lean_object* v_start_1775_; lean_object* v_stop_1776_; lean_object* v_start_1777_; lean_object* v_stop_1778_; lean_object* v_i_1779_; uint8_t v___y_1781_; lean_object* v___x_1795_; uint8_t v___x_1796_; 
v_start_1775_ = lean_ctor_get(v_left_1772_, 1);
v_stop_1776_ = lean_ctor_get(v_left_1772_, 2);
v_start_1777_ = lean_ctor_get(v_right_1773_, 1);
v_stop_1778_ = lean_ctor_get(v_right_1773_, 2);
v_i_1779_ = lean_array_get_size(v_pref_1774_);
v___x_1795_ = lean_nat_sub(v_stop_1776_, v_start_1775_);
v___x_1796_ = lean_nat_dec_lt(v_i_1779_, v___x_1795_);
lean_dec(v___x_1795_);
if (v___x_1796_ == 0)
{
v___y_1781_ = v___x_1796_;
goto v___jp_1780_;
}
else
{
lean_object* v___x_1797_; uint8_t v___x_1798_; 
v___x_1797_ = lean_nat_sub(v_stop_1778_, v_start_1777_);
v___x_1798_ = lean_nat_dec_lt(v_i_1779_, v___x_1797_);
lean_dec(v___x_1797_);
v___y_1781_ = v___x_1798_;
goto v___jp_1780_;
}
v___jp_1780_:
{
if (v___y_1781_ == 0)
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1782_ = l_Subarray_drop___redArg(v_left_1772_, v_i_1779_);
v___x_1783_ = l_Subarray_drop___redArg(v_right_1773_, v_i_1779_);
v___x_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1782_);
lean_ctor_set(v___x_1784_, 1, v___x_1783_);
v___x_1785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1785_, 0, v_pref_1774_);
lean_ctor_set(v___x_1785_, 1, v___x_1784_);
return v___x_1785_;
}
else
{
lean_object* v___x_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; 
v___x_1786_ = l_Subarray_get___redArg(v_left_1772_, v_i_1779_);
v___x_1787_ = l_Subarray_get___redArg(v_right_1773_, v_i_1779_);
v___x_1788_ = lean_string_dec_eq(v___x_1786_, v___x_1787_);
lean_dec(v___x_1787_);
if (v___x_1788_ == 0)
{
lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
lean_dec(v___x_1786_);
v___x_1789_ = l_Subarray_drop___redArg(v_left_1772_, v_i_1779_);
v___x_1790_ = l_Subarray_drop___redArg(v_right_1773_, v_i_1779_);
v___x_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1791_, 0, v___x_1789_);
lean_ctor_set(v___x_1791_, 1, v___x_1790_);
v___x_1792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1792_, 0, v_pref_1774_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
return v___x_1792_;
}
else
{
lean_object* v___x_1793_; 
v___x_1793_ = lean_array_push(v_pref_1774_, v___x_1786_);
v_pref_1774_ = v___x_1793_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4(lean_object* v_left_1799_, lean_object* v_right_1800_){
_start:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1801_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_1802_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4_spec__6(v_left_1799_, v_right_1800_, v___x_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(lean_object* v_a_1803_, lean_object* v_x_1804_){
_start:
{
if (lean_obj_tag(v_x_1804_) == 0)
{
lean_object* v___x_1805_; 
v___x_1805_ = lean_box(0);
return v___x_1805_;
}
else
{
lean_object* v_key_1806_; lean_object* v_value_1807_; lean_object* v_tail_1808_; uint8_t v___x_1809_; 
v_key_1806_ = lean_ctor_get(v_x_1804_, 0);
v_value_1807_ = lean_ctor_get(v_x_1804_, 1);
v_tail_1808_ = lean_ctor_get(v_x_1804_, 2);
v___x_1809_ = lean_string_dec_eq(v_key_1806_, v_a_1803_);
if (v___x_1809_ == 0)
{
v_x_1804_ = v_tail_1808_;
goto _start;
}
else
{
lean_object* v___x_1811_; 
lean_inc(v_value_1807_);
v___x_1811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1811_, 0, v_value_1807_);
return v___x_1811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg___boxed(lean_object* v_a_1812_, lean_object* v_x_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(v_a_1812_, v_x_1813_);
lean_dec(v_x_1813_);
lean_dec_ref(v_a_1812_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(lean_object* v_m_1815_, lean_object* v_a_1816_){
_start:
{
lean_object* v_buckets_1817_; lean_object* v___x_1818_; uint64_t v___x_1819_; uint64_t v___x_1820_; uint64_t v___x_1821_; uint64_t v_fold_1822_; uint64_t v___x_1823_; uint64_t v___x_1824_; uint64_t v___x_1825_; size_t v___x_1826_; size_t v___x_1827_; size_t v___x_1828_; size_t v___x_1829_; size_t v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v_buckets_1817_ = lean_ctor_get(v_m_1815_, 1);
v___x_1818_ = lean_array_get_size(v_buckets_1817_);
v___x_1819_ = lean_string_hash(v_a_1816_);
v___x_1820_ = 32ULL;
v___x_1821_ = lean_uint64_shift_right(v___x_1819_, v___x_1820_);
v_fold_1822_ = lean_uint64_xor(v___x_1819_, v___x_1821_);
v___x_1823_ = 16ULL;
v___x_1824_ = lean_uint64_shift_right(v_fold_1822_, v___x_1823_);
v___x_1825_ = lean_uint64_xor(v_fold_1822_, v___x_1824_);
v___x_1826_ = lean_uint64_to_usize(v___x_1825_);
v___x_1827_ = lean_usize_of_nat(v___x_1818_);
v___x_1828_ = ((size_t)1ULL);
v___x_1829_ = lean_usize_sub(v___x_1827_, v___x_1828_);
v___x_1830_ = lean_usize_land(v___x_1826_, v___x_1829_);
v___x_1831_ = lean_array_uget_borrowed(v_buckets_1817_, v___x_1830_);
v___x_1832_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(v_a_1816_, v___x_1831_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg___boxed(lean_object* v_m_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_m_1833_, v_a_1834_);
lean_dec_ref(v_a_1834_);
lean_dec_ref(v_m_1833_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29___redArg(lean_object* v_x_1836_, lean_object* v_x_1837_){
_start:
{
if (lean_obj_tag(v_x_1837_) == 0)
{
return v_x_1836_;
}
else
{
lean_object* v_key_1838_; lean_object* v_value_1839_; lean_object* v_tail_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1863_; 
v_key_1838_ = lean_ctor_get(v_x_1837_, 0);
v_value_1839_ = lean_ctor_get(v_x_1837_, 1);
v_tail_1840_ = lean_ctor_get(v_x_1837_, 2);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_x_1837_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1842_ = v_x_1837_;
v_isShared_1843_ = v_isSharedCheck_1863_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_tail_1840_);
lean_inc(v_value_1839_);
lean_inc(v_key_1838_);
lean_dec(v_x_1837_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1863_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1844_; uint64_t v___x_1845_; uint64_t v___x_1846_; uint64_t v___x_1847_; uint64_t v_fold_1848_; uint64_t v___x_1849_; uint64_t v___x_1850_; uint64_t v___x_1851_; size_t v___x_1852_; size_t v___x_1853_; size_t v___x_1854_; size_t v___x_1855_; size_t v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1859_; 
v___x_1844_ = lean_array_get_size(v_x_1836_);
v___x_1845_ = lean_string_hash(v_key_1838_);
v___x_1846_ = 32ULL;
v___x_1847_ = lean_uint64_shift_right(v___x_1845_, v___x_1846_);
v_fold_1848_ = lean_uint64_xor(v___x_1845_, v___x_1847_);
v___x_1849_ = 16ULL;
v___x_1850_ = lean_uint64_shift_right(v_fold_1848_, v___x_1849_);
v___x_1851_ = lean_uint64_xor(v_fold_1848_, v___x_1850_);
v___x_1852_ = lean_uint64_to_usize(v___x_1851_);
v___x_1853_ = lean_usize_of_nat(v___x_1844_);
v___x_1854_ = ((size_t)1ULL);
v___x_1855_ = lean_usize_sub(v___x_1853_, v___x_1854_);
v___x_1856_ = lean_usize_land(v___x_1852_, v___x_1855_);
v___x_1857_ = lean_array_uget_borrowed(v_x_1836_, v___x_1856_);
lean_inc(v___x_1857_);
if (v_isShared_1843_ == 0)
{
lean_ctor_set(v___x_1842_, 2, v___x_1857_);
v___x_1859_ = v___x_1842_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_key_1838_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v_value_1839_);
lean_ctor_set(v_reuseFailAlloc_1862_, 2, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v___x_1860_; 
v___x_1860_ = lean_array_uset(v_x_1836_, v___x_1856_, v___x_1859_);
v_x_1836_ = v___x_1860_;
v_x_1837_ = v_tail_1840_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28___redArg(lean_object* v_i_1864_, lean_object* v_source_1865_, lean_object* v_target_1866_){
_start:
{
lean_object* v___x_1867_; uint8_t v___x_1868_; 
v___x_1867_ = lean_array_get_size(v_source_1865_);
v___x_1868_ = lean_nat_dec_lt(v_i_1864_, v___x_1867_);
if (v___x_1868_ == 0)
{
lean_dec_ref(v_source_1865_);
lean_dec(v_i_1864_);
return v_target_1866_;
}
else
{
lean_object* v_es_1869_; lean_object* v___x_1870_; lean_object* v_source_1871_; lean_object* v_target_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v_es_1869_ = lean_array_fget(v_source_1865_, v_i_1864_);
v___x_1870_ = lean_box(0);
v_source_1871_ = lean_array_fset(v_source_1865_, v_i_1864_, v___x_1870_);
v_target_1872_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29___redArg(v_target_1866_, v_es_1869_);
v___x_1873_ = lean_unsigned_to_nat(1u);
v___x_1874_ = lean_nat_add(v_i_1864_, v___x_1873_);
lean_dec(v_i_1864_);
v_i_1864_ = v___x_1874_;
v_source_1865_ = v_source_1871_;
v_target_1866_ = v_target_1872_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23___redArg(lean_object* v_data_1876_){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v_nbuckets_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1877_ = lean_array_get_size(v_data_1876_);
v___x_1878_ = lean_unsigned_to_nat(2u);
v_nbuckets_1879_ = lean_nat_mul(v___x_1877_, v___x_1878_);
v___x_1880_ = lean_unsigned_to_nat(0u);
v___x_1881_ = lean_box(0);
v___x_1882_ = lean_mk_array(v_nbuckets_1879_, v___x_1881_);
v___x_1883_ = lean_array_propagate_mark(v_data_1876_, v___x_1882_);
v___x_1884_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28___redArg(v___x_1880_, v_data_1876_, v___x_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(lean_object* v_a_1885_, lean_object* v_b_1886_, lean_object* v_x_1887_){
_start:
{
if (lean_obj_tag(v_x_1887_) == 0)
{
lean_dec(v_b_1886_);
lean_dec_ref(v_a_1885_);
return v_x_1887_;
}
else
{
lean_object* v_key_1888_; lean_object* v_value_1889_; lean_object* v_tail_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1902_; 
v_key_1888_ = lean_ctor_get(v_x_1887_, 0);
v_value_1889_ = lean_ctor_get(v_x_1887_, 1);
v_tail_1890_ = lean_ctor_get(v_x_1887_, 2);
v_isSharedCheck_1902_ = !lean_is_exclusive(v_x_1887_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1892_ = v_x_1887_;
v_isShared_1893_ = v_isSharedCheck_1902_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_tail_1890_);
lean_inc(v_value_1889_);
lean_inc(v_key_1888_);
lean_dec(v_x_1887_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1902_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
uint8_t v___x_1894_; 
v___x_1894_ = lean_string_dec_eq(v_key_1888_, v_a_1885_);
if (v___x_1894_ == 0)
{
lean_object* v___x_1895_; lean_object* v___x_1897_; 
v___x_1895_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(v_a_1885_, v_b_1886_, v_tail_1890_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 2, v___x_1895_);
v___x_1897_ = v___x_1892_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_key_1888_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v_value_1889_);
lean_ctor_set(v_reuseFailAlloc_1898_, 2, v___x_1895_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
else
{
lean_object* v___x_1900_; 
lean_dec(v_value_1889_);
lean_dec(v_key_1888_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 1, v_b_1886_);
lean_ctor_set(v___x_1892_, 0, v_a_1885_);
v___x_1900_ = v___x_1892_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1885_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_b_1886_);
lean_ctor_set(v_reuseFailAlloc_1901_, 2, v_tail_1890_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(lean_object* v_a_1903_, lean_object* v_x_1904_){
_start:
{
if (lean_obj_tag(v_x_1904_) == 0)
{
uint8_t v___x_1905_; 
v___x_1905_ = 0;
return v___x_1905_;
}
else
{
lean_object* v_key_1906_; lean_object* v_tail_1907_; uint8_t v___x_1908_; 
v_key_1906_ = lean_ctor_get(v_x_1904_, 0);
v_tail_1907_ = lean_ctor_get(v_x_1904_, 2);
v___x_1908_ = lean_string_dec_eq(v_key_1906_, v_a_1903_);
if (v___x_1908_ == 0)
{
v_x_1904_ = v_tail_1907_;
goto _start;
}
else
{
return v___x_1908_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg___boxed(lean_object* v_a_1910_, lean_object* v_x_1911_){
_start:
{
uint8_t v_res_1912_; lean_object* v_r_1913_; 
v_res_1912_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(v_a_1910_, v_x_1911_);
lean_dec(v_x_1911_);
lean_dec_ref(v_a_1910_);
v_r_1913_ = lean_box(v_res_1912_);
return v_r_1913_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(lean_object* v_m_1914_, lean_object* v_a_1915_, lean_object* v_b_1916_){
_start:
{
lean_object* v_size_1917_; lean_object* v_buckets_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1961_; 
v_size_1917_ = lean_ctor_get(v_m_1914_, 0);
v_buckets_1918_ = lean_ctor_get(v_m_1914_, 1);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_m_1914_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1920_ = v_m_1914_;
v_isShared_1921_ = v_isSharedCheck_1961_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_buckets_1918_);
lean_inc(v_size_1917_);
lean_dec(v_m_1914_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1961_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1922_; uint64_t v___x_1923_; uint64_t v___x_1924_; uint64_t v___x_1925_; uint64_t v_fold_1926_; uint64_t v___x_1927_; uint64_t v___x_1928_; uint64_t v___x_1929_; size_t v___x_1930_; size_t v___x_1931_; size_t v___x_1932_; size_t v___x_1933_; size_t v___x_1934_; lean_object* v_bkt_1935_; uint8_t v___x_1936_; 
v___x_1922_ = lean_array_get_size(v_buckets_1918_);
v___x_1923_ = lean_string_hash(v_a_1915_);
v___x_1924_ = 32ULL;
v___x_1925_ = lean_uint64_shift_right(v___x_1923_, v___x_1924_);
v_fold_1926_ = lean_uint64_xor(v___x_1923_, v___x_1925_);
v___x_1927_ = 16ULL;
v___x_1928_ = lean_uint64_shift_right(v_fold_1926_, v___x_1927_);
v___x_1929_ = lean_uint64_xor(v_fold_1926_, v___x_1928_);
v___x_1930_ = lean_uint64_to_usize(v___x_1929_);
v___x_1931_ = lean_usize_of_nat(v___x_1922_);
v___x_1932_ = ((size_t)1ULL);
v___x_1933_ = lean_usize_sub(v___x_1931_, v___x_1932_);
v___x_1934_ = lean_usize_land(v___x_1930_, v___x_1933_);
v_bkt_1935_ = lean_array_uget_borrowed(v_buckets_1918_, v___x_1934_);
v___x_1936_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(v_a_1915_, v_bkt_1935_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; lean_object* v_size_x27_1938_; lean_object* v___x_1939_; lean_object* v_buckets_x27_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; uint8_t v___x_1946_; 
v___x_1937_ = lean_unsigned_to_nat(1u);
v_size_x27_1938_ = lean_nat_add(v_size_1917_, v___x_1937_);
lean_dec(v_size_1917_);
lean_inc(v_bkt_1935_);
v___x_1939_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1939_, 0, v_a_1915_);
lean_ctor_set(v___x_1939_, 1, v_b_1916_);
lean_ctor_set(v___x_1939_, 2, v_bkt_1935_);
v_buckets_x27_1940_ = lean_array_uset(v_buckets_1918_, v___x_1934_, v___x_1939_);
v___x_1941_ = lean_unsigned_to_nat(4u);
v___x_1942_ = lean_nat_mul(v_size_x27_1938_, v___x_1941_);
v___x_1943_ = lean_unsigned_to_nat(3u);
v___x_1944_ = lean_nat_div(v___x_1942_, v___x_1943_);
lean_dec(v___x_1942_);
v___x_1945_ = lean_array_get_size(v_buckets_x27_1940_);
v___x_1946_ = lean_nat_dec_le(v___x_1944_, v___x_1945_);
lean_dec(v___x_1944_);
if (v___x_1946_ == 0)
{
lean_object* v_val_1947_; lean_object* v___x_1949_; 
v_val_1947_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23___redArg(v_buckets_x27_1940_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 1, v_val_1947_);
lean_ctor_set(v___x_1920_, 0, v_size_x27_1938_);
v___x_1949_ = v___x_1920_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_size_x27_1938_);
lean_ctor_set(v_reuseFailAlloc_1950_, 1, v_val_1947_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
else
{
lean_object* v___x_1952_; 
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 1, v_buckets_x27_1940_);
lean_ctor_set(v___x_1920_, 0, v_size_x27_1938_);
v___x_1952_ = v___x_1920_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_size_x27_1938_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v_buckets_x27_1940_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
else
{
lean_object* v___x_1954_; lean_object* v_buckets_x27_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1959_; 
lean_inc(v_bkt_1935_);
v___x_1954_ = lean_box(0);
v_buckets_x27_1955_ = lean_array_uset(v_buckets_1918_, v___x_1934_, v___x_1954_);
v___x_1956_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(v_a_1915_, v_b_1916_, v_bkt_1935_);
v___x_1957_ = lean_array_uset(v_buckets_x27_1955_, v___x_1934_, v___x_1956_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 1, v___x_1957_);
v___x_1959_ = v___x_1920_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_size_1917_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v___x_1957_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___redArg(lean_object* v_histogram_1962_, lean_object* v_index_1963_, lean_object* v_val_1964_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_histogram_1962_, v_val_1964_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1966_ = lean_unsigned_to_nat(0u);
v___x_1967_ = lean_box(0);
v___x_1968_ = lean_unsigned_to_nat(1u);
v___x_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1969_, 0, v_index_1963_);
v___x_1970_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1966_);
lean_ctor_set(v___x_1970_, 1, v___x_1967_);
lean_ctor_set(v___x_1970_, 2, v___x_1968_);
lean_ctor_set(v___x_1970_, 3, v___x_1969_);
v___x_1971_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_1962_, v_val_1964_, v___x_1970_);
return v___x_1971_;
}
else
{
lean_object* v_val_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_1993_; 
v_val_1972_ = lean_ctor_get(v___x_1965_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1974_ = v___x_1965_;
v_isShared_1975_ = v_isSharedCheck_1993_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_val_1972_);
lean_dec(v___x_1965_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_1993_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v_leftCount_1976_; lean_object* v_leftIndex_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1990_; 
v_leftCount_1976_ = lean_ctor_get(v_val_1972_, 0);
v_leftIndex_1977_ = lean_ctor_get(v_val_1972_, 1);
v_isSharedCheck_1990_ = !lean_is_exclusive(v_val_1972_);
if (v_isSharedCheck_1990_ == 0)
{
lean_object* v_unused_1991_; lean_object* v_unused_1992_; 
v_unused_1991_ = lean_ctor_get(v_val_1972_, 3);
lean_dec(v_unused_1991_);
v_unused_1992_ = lean_ctor_get(v_val_1972_, 2);
lean_dec(v_unused_1992_);
v___x_1979_ = v_val_1972_;
v_isShared_1980_ = v_isSharedCheck_1990_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_leftIndex_1977_);
lean_inc(v_leftCount_1976_);
lean_dec(v_val_1972_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1990_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1984_; 
v___x_1981_ = lean_unsigned_to_nat(1u);
v___x_1982_ = lean_nat_add(v_leftCount_1976_, v___x_1981_);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 0, v_index_1963_);
v___x_1984_ = v___x_1974_;
goto v_reusejp_1983_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_index_1963_);
v___x_1984_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1983_;
}
v_reusejp_1983_:
{
lean_object* v___x_1986_; 
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 3, v___x_1984_);
lean_ctor_set(v___x_1979_, 2, v___x_1982_);
v___x_1986_ = v___x_1979_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_leftCount_1976_);
lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_leftIndex_1977_);
lean_ctor_set(v_reuseFailAlloc_1988_, 2, v___x_1982_);
lean_ctor_set(v_reuseFailAlloc_1988_, 3, v___x_1984_);
v___x_1986_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
lean_object* v___x_1987_; 
v___x_1987_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_1962_, v_val_1964_, v___x_1986_);
return v___x_1987_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(lean_object* v_upperBound_1994_, lean_object* v___x_1995_, lean_object* v_fst_1996_, lean_object* v___x_1997_, lean_object* v_a_1998_, lean_object* v_b_1999_){
_start:
{
uint8_t v___x_2000_; 
v___x_2000_ = lean_nat_dec_lt(v_a_1998_, v_upperBound_1994_);
if (v___x_2000_ == 0)
{
lean_dec(v_a_1998_);
return v_b_1999_;
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2001_ = l_Subarray_get___redArg(v_fst_1996_, v_a_1998_);
lean_inc(v_a_1998_);
v___x_2002_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___redArg(v_b_1999_, v_a_1998_, v___x_2001_);
v___x_2003_ = lean_unsigned_to_nat(1u);
v___x_2004_ = lean_nat_add(v_a_1998_, v___x_2003_);
lean_dec(v_a_1998_);
v_a_1998_ = v___x_2004_;
v_b_1999_ = v___x_2002_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg___boxed(lean_object* v_upperBound_2006_, lean_object* v___x_2007_, lean_object* v_fst_2008_, lean_object* v___x_2009_, lean_object* v_a_2010_, lean_object* v_b_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(v_upperBound_2006_, v___x_2007_, v_fst_2008_, v___x_2009_, v_a_2010_, v_b_2011_);
lean_dec(v___x_2009_);
lean_dec_ref(v_fst_2008_);
lean_dec(v___x_2007_);
lean_dec(v_upperBound_2006_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(lean_object* v_as_x27_2013_, lean_object* v_b_2014_){
_start:
{
if (lean_obj_tag(v_as_x27_2013_) == 0)
{
return v_b_2014_;
}
else
{
lean_object* v_head_2015_; lean_object* v_snd_2016_; lean_object* v_leftIndex_2017_; 
v_head_2015_ = lean_ctor_get(v_as_x27_2013_, 0);
v_snd_2016_ = lean_ctor_get(v_head_2015_, 1);
v_leftIndex_2017_ = lean_ctor_get(v_snd_2016_, 1);
if (lean_obj_tag(v_leftIndex_2017_) == 1)
{
lean_object* v_rightIndex_2018_; 
v_rightIndex_2018_ = lean_ctor_get(v_snd_2016_, 3);
if (lean_obj_tag(v_rightIndex_2018_) == 1)
{
if (lean_obj_tag(v_b_2014_) == 0)
{
lean_object* v_tail_2019_; lean_object* v_fst_2020_; lean_object* v_leftCount_2021_; lean_object* v_rightCount_2022_; lean_object* v_val_2023_; lean_object* v_val_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v_tail_2019_ = lean_ctor_get(v_as_x27_2013_, 1);
v_fst_2020_ = lean_ctor_get(v_head_2015_, 0);
v_leftCount_2021_ = lean_ctor_get(v_snd_2016_, 0);
v_rightCount_2022_ = lean_ctor_get(v_snd_2016_, 2);
v_val_2023_ = lean_ctor_get(v_leftIndex_2017_, 0);
v_val_2024_ = lean_ctor_get(v_rightIndex_2018_, 0);
v___x_2025_ = lean_nat_add(v_leftCount_2021_, v_rightCount_2022_);
lean_inc(v_val_2024_);
lean_inc(v_val_2023_);
v___x_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2026_, 0, v_val_2023_);
lean_ctor_set(v___x_2026_, 1, v_val_2024_);
lean_inc(v_fst_2020_);
v___x_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2027_, 0, v_fst_2020_);
lean_ctor_set(v___x_2027_, 1, v___x_2026_);
v___x_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2025_);
lean_ctor_set(v___x_2028_, 1, v___x_2027_);
v___x_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2028_);
v_as_x27_2013_ = v_tail_2019_;
v_b_2014_ = v___x_2029_;
goto _start;
}
else
{
lean_object* v_val_2031_; lean_object* v_tail_2032_; lean_object* v_fst_2033_; lean_object* v_leftCount_2034_; lean_object* v_rightCount_2035_; lean_object* v_val_2036_; lean_object* v_val_2037_; lean_object* v_fst_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2059_; 
v_val_2031_ = lean_ctor_get(v_b_2014_, 0);
lean_inc(v_val_2031_);
v_tail_2032_ = lean_ctor_get(v_as_x27_2013_, 1);
v_fst_2033_ = lean_ctor_get(v_head_2015_, 0);
v_leftCount_2034_ = lean_ctor_get(v_snd_2016_, 0);
v_rightCount_2035_ = lean_ctor_get(v_snd_2016_, 2);
v_val_2036_ = lean_ctor_get(v_leftIndex_2017_, 0);
v_val_2037_ = lean_ctor_get(v_rightIndex_2018_, 0);
v_fst_2038_ = lean_ctor_get(v_val_2031_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_val_2031_);
if (v_isSharedCheck_2059_ == 0)
{
lean_object* v_unused_2060_; 
v_unused_2060_ = lean_ctor_get(v_val_2031_, 1);
lean_dec(v_unused_2060_);
v___x_2040_ = v_val_2031_;
v_isShared_2041_ = v_isSharedCheck_2059_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_fst_2038_);
lean_dec(v_val_2031_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2059_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2042_; uint8_t v___x_2043_; 
v___x_2042_ = lean_nat_add(v_leftCount_2034_, v_rightCount_2035_);
v___x_2043_ = lean_nat_dec_lt(v___x_2042_, v_fst_2038_);
lean_dec(v_fst_2038_);
if (v___x_2043_ == 0)
{
lean_dec(v___x_2042_);
lean_del_object(v___x_2040_);
v_as_x27_2013_ = v_tail_2032_;
goto _start;
}
else
{
lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2057_; 
v_isSharedCheck_2057_ = !lean_is_exclusive(v_b_2014_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; 
v_unused_2058_ = lean_ctor_get(v_b_2014_, 0);
lean_dec(v_unused_2058_);
v___x_2046_ = v_b_2014_;
v_isShared_2047_ = v_isSharedCheck_2057_;
goto v_resetjp_2045_;
}
else
{
lean_dec(v_b_2014_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2057_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
lean_inc(v_val_2037_);
lean_inc(v_val_2036_);
if (v_isShared_2041_ == 0)
{
lean_ctor_set(v___x_2040_, 1, v_val_2037_);
lean_ctor_set(v___x_2040_, 0, v_val_2036_);
v___x_2049_ = v___x_2040_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_val_2036_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_val_2037_);
v___x_2049_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2053_; 
lean_inc(v_fst_2033_);
v___x_2050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2050_, 0, v_fst_2033_);
lean_ctor_set(v___x_2050_, 1, v___x_2049_);
v___x_2051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2042_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v___x_2051_);
v___x_2053_ = v___x_2046_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2051_);
v___x_2053_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
v_as_x27_2013_ = v_tail_2032_;
v_b_2014_ = v___x_2053_;
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
lean_object* v_tail_2061_; 
v_tail_2061_ = lean_ctor_get(v_as_x27_2013_, 1);
v_as_x27_2013_ = v_tail_2061_;
goto _start;
}
}
else
{
lean_object* v_tail_2063_; 
v_tail_2063_ = lean_ctor_get(v_as_x27_2013_, 1);
v_as_x27_2013_ = v_tail_2063_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_as_x27_2065_, lean_object* v_b_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(v_as_x27_2065_, v_b_2066_);
lean_dec(v_as_x27_2065_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(lean_object* v_a_2068_, lean_object* v_b_2069_){
_start:
{
lean_object* v_array_2070_; lean_object* v_start_2071_; lean_object* v_stop_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2085_; 
v_array_2070_ = lean_ctor_get(v_a_2068_, 0);
v_start_2071_ = lean_ctor_get(v_a_2068_, 1);
v_stop_2072_ = lean_ctor_get(v_a_2068_, 2);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_a_2068_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2074_ = v_a_2068_;
v_isShared_2075_ = v_isSharedCheck_2085_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_stop_2072_);
lean_inc(v_start_2071_);
lean_inc(v_array_2070_);
lean_dec(v_a_2068_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2085_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
uint8_t v___x_2076_; 
v___x_2076_ = lean_nat_dec_lt(v_start_2071_, v_stop_2072_);
if (v___x_2076_ == 0)
{
lean_del_object(v___x_2074_);
lean_dec(v_stop_2072_);
lean_dec(v_start_2071_);
lean_dec_ref(v_array_2070_);
return v_b_2069_;
}
else
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2077_ = lean_unsigned_to_nat(1u);
v___x_2078_ = lean_nat_add(v_start_2071_, v___x_2077_);
lean_inc_ref(v_array_2070_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 1, v___x_2078_);
v___x_2080_ = v___x_2074_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_array_2070_);
lean_ctor_set(v_reuseFailAlloc_2084_, 1, v___x_2078_);
lean_ctor_set(v_reuseFailAlloc_2084_, 2, v_stop_2072_);
v___x_2080_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2081_ = lean_array_fget(v_array_2070_, v_start_2071_);
lean_dec(v_start_2071_);
lean_dec_ref(v_array_2070_);
v___x_2082_ = lean_array_push(v_b_2069_, v___x_2081_);
v_a_2068_ = v___x_2080_;
v_b_2069_ = v___x_2082_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8(lean_object* v_left_2086_, lean_object* v_right_2087_, lean_object* v_i_2088_){
_start:
{
lean_object* v_start_2089_; lean_object* v_stop_2090_; lean_object* v_start_2091_; lean_object* v_stop_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; lean_object* v___x_2095_; uint8_t v___y_2097_; 
v_start_2089_ = lean_ctor_get(v_left_2086_, 1);
v_stop_2090_ = lean_ctor_get(v_left_2086_, 2);
v_start_2091_ = lean_ctor_get(v_right_2087_, 1);
v_stop_2092_ = lean_ctor_get(v_right_2087_, 2);
v___x_2093_ = lean_nat_sub(v_stop_2090_, v_start_2089_);
v___x_2094_ = lean_nat_dec_lt(v_i_2088_, v___x_2093_);
v___x_2095_ = lean_nat_sub(v_stop_2092_, v_start_2091_);
if (v___x_2094_ == 0)
{
v___y_2097_ = v___x_2094_;
goto v___jp_2096_;
}
else
{
uint8_t v___x_2124_; 
v___x_2124_ = lean_nat_dec_lt(v_i_2088_, v___x_2095_);
v___y_2097_ = v___x_2124_;
goto v___jp_2096_;
}
v___jp_2096_:
{
if (v___y_2097_ == 0)
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2098_ = lean_nat_sub(v___x_2093_, v_i_2088_);
lean_dec(v___x_2093_);
lean_inc_ref(v_left_2086_);
v___x_2099_ = l_Subarray_take___redArg(v_left_2086_, v___x_2098_);
v___x_2100_ = lean_nat_sub(v___x_2095_, v_i_2088_);
lean_dec(v_i_2088_);
lean_dec(v___x_2095_);
v___x_2101_ = l_Subarray_take___redArg(v_right_2087_, v___x_2100_);
lean_dec(v___x_2100_);
v___x_2102_ = l_Subarray_drop___redArg(v_left_2086_, v___x_2098_);
lean_dec(v___x_2098_);
v___x_2103_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2104_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(v___x_2102_, v___x_2103_);
v___x_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2101_);
lean_ctor_set(v___x_2105_, 1, v___x_2104_);
v___x_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2106_, 0, v___x_2099_);
lean_ctor_set(v___x_2106_, 1, v___x_2105_);
return v___x_2106_;
}
else
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; 
v___x_2107_ = lean_nat_sub(v___x_2093_, v_i_2088_);
lean_dec(v___x_2093_);
v___x_2108_ = lean_unsigned_to_nat(1u);
v___x_2109_ = lean_nat_sub(v___x_2107_, v___x_2108_);
v___x_2110_ = l_Subarray_get___redArg(v_left_2086_, v___x_2109_);
lean_dec(v___x_2109_);
v___x_2111_ = lean_nat_sub(v___x_2095_, v_i_2088_);
lean_dec(v___x_2095_);
v___x_2112_ = lean_nat_sub(v___x_2111_, v___x_2108_);
v___x_2113_ = l_Subarray_get___redArg(v_right_2087_, v___x_2112_);
lean_dec(v___x_2112_);
v___x_2114_ = lean_string_dec_eq(v___x_2110_, v___x_2113_);
lean_dec(v___x_2113_);
lean_dec(v___x_2110_);
if (v___x_2114_ == 0)
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
lean_dec(v_i_2088_);
lean_inc_ref(v_left_2086_);
v___x_2115_ = l_Subarray_take___redArg(v_left_2086_, v___x_2107_);
v___x_2116_ = l_Subarray_take___redArg(v_right_2087_, v___x_2111_);
lean_dec(v___x_2111_);
v___x_2117_ = l_Subarray_drop___redArg(v_left_2086_, v___x_2107_);
lean_dec(v___x_2107_);
v___x_2118_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2119_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(v___x_2117_, v___x_2118_);
v___x_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2116_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
v___x_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2115_);
lean_ctor_set(v___x_2121_, 1, v___x_2120_);
return v___x_2121_;
}
else
{
lean_object* v___x_2122_; 
lean_dec(v___x_2111_);
lean_dec(v___x_2107_);
v___x_2122_ = lean_nat_add(v_i_2088_, v___x_2108_);
lean_dec(v_i_2088_);
v_i_2088_ = v___x_2122_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5(lean_object* v_left_2125_, lean_object* v_right_2126_){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2127_ = lean_unsigned_to_nat(0u);
v___x_2128_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8(v_left_2125_, v_right_2126_, v___x_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___redArg(lean_object* v_histogram_2129_, lean_object* v_index_2130_, lean_object* v_val_2131_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_histogram_2129_, v_val_2131_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
v___x_2133_ = lean_unsigned_to_nat(1u);
v___x_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2134_, 0, v_index_2130_);
v___x_2135_ = lean_unsigned_to_nat(0u);
v___x_2136_ = lean_box(0);
v___x_2137_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2133_);
lean_ctor_set(v___x_2137_, 1, v___x_2134_);
lean_ctor_set(v___x_2137_, 2, v___x_2135_);
lean_ctor_set(v___x_2137_, 3, v___x_2136_);
v___x_2138_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_2129_, v_val_2131_, v___x_2137_);
return v___x_2138_;
}
else
{
lean_object* v_val_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2160_; 
v_val_2139_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2141_ = v___x_2132_;
v_isShared_2142_ = v_isSharedCheck_2160_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_val_2139_);
lean_dec(v___x_2132_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2160_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v_leftCount_2143_; lean_object* v_rightCount_2144_; lean_object* v_rightIndex_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2158_; 
v_leftCount_2143_ = lean_ctor_get(v_val_2139_, 0);
v_rightCount_2144_ = lean_ctor_get(v_val_2139_, 2);
v_rightIndex_2145_ = lean_ctor_get(v_val_2139_, 3);
v_isSharedCheck_2158_ = !lean_is_exclusive(v_val_2139_);
if (v_isSharedCheck_2158_ == 0)
{
lean_object* v_unused_2159_; 
v_unused_2159_ = lean_ctor_get(v_val_2139_, 1);
lean_dec(v_unused_2159_);
v___x_2147_ = v_val_2139_;
v_isShared_2148_ = v_isSharedCheck_2158_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_rightIndex_2145_);
lean_inc(v_rightCount_2144_);
lean_inc(v_leftCount_2143_);
lean_dec(v_val_2139_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2158_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2152_; 
v___x_2149_ = lean_unsigned_to_nat(1u);
v___x_2150_ = lean_nat_add(v_leftCount_2143_, v___x_2149_);
lean_dec(v_leftCount_2143_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 0, v_index_2130_);
v___x_2152_ = v___x_2141_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_index_2130_);
v___x_2152_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2154_; 
if (v_isShared_2148_ == 0)
{
lean_ctor_set(v___x_2147_, 1, v___x_2152_);
lean_ctor_set(v___x_2147_, 0, v___x_2150_);
v___x_2154_ = v___x_2147_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v___x_2152_);
lean_ctor_set(v_reuseFailAlloc_2156_, 2, v_rightCount_2144_);
lean_ctor_set(v_reuseFailAlloc_2156_, 3, v_rightIndex_2145_);
v___x_2154_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; 
v___x_2155_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_2129_, v_val_2131_, v___x_2154_);
return v___x_2155_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(lean_object* v_upperBound_2161_, lean_object* v_fst_2162_, lean_object* v___x_2163_, lean_object* v_fst_2164_, lean_object* v_a_2165_, lean_object* v_b_2166_){
_start:
{
uint8_t v___x_2167_; 
v___x_2167_ = lean_nat_dec_lt(v_a_2165_, v_upperBound_2161_);
if (v___x_2167_ == 0)
{
lean_dec(v_a_2165_);
return v_b_2166_;
}
else
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2168_ = l_Subarray_get___redArg(v_fst_2164_, v_a_2165_);
lean_inc(v_a_2165_);
v___x_2169_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___redArg(v_b_2166_, v_a_2165_, v___x_2168_);
v___x_2170_ = lean_unsigned_to_nat(1u);
v___x_2171_ = lean_nat_add(v_a_2165_, v___x_2170_);
lean_dec(v_a_2165_);
v_a_2165_ = v___x_2171_;
v_b_2166_ = v___x_2169_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg___boxed(lean_object* v_upperBound_2173_, lean_object* v_fst_2174_, lean_object* v___x_2175_, lean_object* v_fst_2176_, lean_object* v_a_2177_, lean_object* v_b_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(v_upperBound_2173_, v_fst_2174_, v___x_2175_, v_fst_2176_, v_a_2177_, v_b_2178_);
lean_dec_ref(v_fst_2176_);
lean_dec(v___x_2175_);
lean_dec_ref(v_fst_2174_);
lean_dec(v_upperBound_2173_);
return v_res_2179_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2180_ = lean_box(0);
v___x_2181_ = lean_unsigned_to_nat(16u);
v___x_2182_ = lean_mk_array(v___x_2181_, v___x_2180_);
return v___x_2182_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v_hist_2185_; 
v___x_2183_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0);
v___x_2184_ = lean_unsigned_to_nat(0u);
v_hist_2185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_2185_, 0, v___x_2184_);
lean_ctor_set(v_hist_2185_, 1, v___x_2183_);
return v_hist_2185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(lean_object* v_left_2186_, lean_object* v_right_2187_){
_start:
{
lean_object* v___x_2188_; lean_object* v_snd_2189_; lean_object* v_fst_2190_; lean_object* v_fst_2191_; lean_object* v_snd_2192_; lean_object* v___x_2193_; lean_object* v_snd_2194_; lean_object* v_fst_2195_; lean_object* v_fst_2196_; lean_object* v_snd_2197_; lean_object* v_start_2198_; lean_object* v_stop_2199_; lean_object* v___x_2200_; lean_object* v_hist_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v_start_2204_; lean_object* v_stop_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v_buckets_2208_; lean_object* v___x_2209_; lean_object* v___y_2211_; lean_object* v___x_2237_; lean_object* v___x_2238_; uint8_t v___x_2239_; 
v___x_2188_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4(v_left_2186_, v_right_2187_);
v_snd_2189_ = lean_ctor_get(v___x_2188_, 1);
lean_inc(v_snd_2189_);
v_fst_2190_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_fst_2190_);
lean_dec_ref(v___x_2188_);
v_fst_2191_ = lean_ctor_get(v_snd_2189_, 0);
lean_inc(v_fst_2191_);
v_snd_2192_ = lean_ctor_get(v_snd_2189_, 1);
lean_inc(v_snd_2192_);
lean_dec(v_snd_2189_);
v___x_2193_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5(v_fst_2191_, v_snd_2192_);
v_snd_2194_ = lean_ctor_get(v___x_2193_, 1);
lean_inc(v_snd_2194_);
v_fst_2195_ = lean_ctor_get(v___x_2193_, 0);
lean_inc(v_fst_2195_);
lean_dec_ref(v___x_2193_);
v_fst_2196_ = lean_ctor_get(v_snd_2194_, 0);
lean_inc(v_fst_2196_);
v_snd_2197_ = lean_ctor_get(v_snd_2194_, 1);
lean_inc(v_snd_2197_);
lean_dec(v_snd_2194_);
v_start_2198_ = lean_ctor_get(v_fst_2195_, 1);
v_stop_2199_ = lean_ctor_get(v_fst_2195_, 2);
v___x_2200_ = lean_unsigned_to_nat(0u);
v_hist_2201_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1);
v___x_2202_ = lean_nat_sub(v_stop_2199_, v_start_2198_);
v___x_2203_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(v___x_2202_, v_fst_2196_, v___x_2202_, v_fst_2195_, v___x_2200_, v_hist_2201_);
v_start_2204_ = lean_ctor_get(v_fst_2196_, 1);
v_stop_2205_ = lean_ctor_get(v_fst_2196_, 2);
v___x_2206_ = lean_nat_sub(v_stop_2205_, v_start_2204_);
v___x_2207_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(v___x_2206_, v___x_2206_, v_fst_2196_, v___x_2202_, v___x_2200_, v___x_2203_);
lean_dec(v___x_2202_);
lean_dec(v___x_2206_);
v_buckets_2208_ = lean_ctor_get(v___x_2207_, 1);
lean_inc_ref(v_buckets_2208_);
lean_dec_ref(v___x_2207_);
v___x_2209_ = lean_box(0);
v___x_2237_ = lean_box(0);
v___x_2238_ = lean_array_get_size(v_buckets_2208_);
v___x_2239_ = lean_nat_dec_lt(v___x_2200_, v___x_2238_);
if (v___x_2239_ == 0)
{
lean_dec_ref(v_buckets_2208_);
v___y_2211_ = v___x_2237_;
goto v___jp_2210_;
}
else
{
size_t v___x_2240_; size_t v___x_2241_; lean_object* v___x_2242_; 
v___x_2240_ = lean_usize_of_nat(v___x_2238_);
v___x_2241_ = ((size_t)0ULL);
v___x_2242_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8(v_buckets_2208_, v___x_2240_, v___x_2241_, v___x_2237_);
lean_dec_ref(v_buckets_2208_);
v___y_2211_ = v___x_2242_;
goto v___jp_2210_;
}
v___jp_2210_:
{
lean_object* v___x_2212_; 
v___x_2212_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(v___y_2211_, v___x_2209_);
lean_dec(v___y_2211_);
if (lean_obj_tag(v___x_2212_) == 1)
{
lean_object* v_val_2213_; lean_object* v_snd_2214_; lean_object* v_snd_2215_; lean_object* v_fst_2216_; lean_object* v_fst_2217_; lean_object* v_snd_2218_; lean_object* v___x_2219_; lean_object* v_fst_2220_; lean_object* v_snd_2221_; lean_object* v___x_2222_; lean_object* v_fst_2223_; lean_object* v_snd_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v_val_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_val_2213_);
lean_dec_ref_known(v___x_2212_, 1);
v_snd_2214_ = lean_ctor_get(v_val_2213_, 1);
lean_inc(v_snd_2214_);
lean_dec(v_val_2213_);
v_snd_2215_ = lean_ctor_get(v_snd_2214_, 1);
lean_inc(v_snd_2215_);
v_fst_2216_ = lean_ctor_get(v_snd_2214_, 0);
lean_inc(v_fst_2216_);
lean_dec(v_snd_2214_);
v_fst_2217_ = lean_ctor_get(v_snd_2215_, 0);
lean_inc(v_fst_2217_);
v_snd_2218_ = lean_ctor_get(v_snd_2215_, 1);
lean_inc(v_snd_2218_);
lean_dec(v_snd_2215_);
v___x_2219_ = l_Subarray_split___redArg(v_fst_2195_, v_fst_2217_);
lean_dec(v_fst_2217_);
v_fst_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_fst_2220_);
v_snd_2221_ = lean_ctor_get(v___x_2219_, 1);
lean_inc(v_snd_2221_);
lean_dec_ref(v___x_2219_);
v___x_2222_ = l_Subarray_split___redArg(v_fst_2196_, v_snd_2218_);
lean_dec(v_snd_2218_);
v_fst_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_fst_2223_);
v_snd_2224_ = lean_ctor_get(v___x_2222_, 1);
lean_inc(v_snd_2224_);
lean_dec_ref(v___x_2222_);
v___x_2225_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v_fst_2220_, v_fst_2223_);
v___x_2226_ = l_Array_append___redArg(v_fst_2190_, v___x_2225_);
lean_dec_ref(v___x_2225_);
v___x_2227_ = lean_unsigned_to_nat(1u);
v___x_2228_ = lean_mk_empty_array_with_capacity(v___x_2227_);
v___x_2229_ = lean_array_push(v___x_2228_, v_fst_2216_);
v___x_2230_ = l_Array_append___redArg(v___x_2226_, v___x_2229_);
lean_dec_ref(v___x_2229_);
v___x_2231_ = l_Subarray_drop___redArg(v_snd_2221_, v___x_2227_);
v___x_2232_ = l_Subarray_drop___redArg(v_snd_2224_, v___x_2227_);
v___x_2233_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v___x_2231_, v___x_2232_);
v___x_2234_ = l_Array_append___redArg(v___x_2230_, v___x_2233_);
lean_dec_ref(v___x_2233_);
v___x_2235_ = l_Array_append___redArg(v___x_2234_, v_snd_2197_);
lean_dec(v_snd_2197_);
return v___x_2235_;
}
else
{
lean_object* v___x_2236_; 
lean_dec(v___x_2212_);
lean_dec(v_fst_2196_);
lean_dec(v_fst_2195_);
v___x_2236_ = l_Array_append___redArg(v_fst_2190_, v_snd_2197_);
lean_dec(v_snd_2197_);
return v___x_2236_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(lean_object* v___x_2243_, lean_object* v_original_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v_fst_2246_; lean_object* v_snd_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2266_; 
v_fst_2246_ = lean_ctor_get(v_a_2245_, 0);
v_snd_2247_ = lean_ctor_get(v_a_2245_, 1);
v_isSharedCheck_2266_ = !lean_is_exclusive(v_a_2245_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2249_ = v_a_2245_;
v_isShared_2250_ = v_isSharedCheck_2266_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_snd_2247_);
lean_inc(v_fst_2246_);
lean_dec(v_a_2245_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2266_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
uint8_t v___x_2251_; 
v___x_2251_ = lean_nat_dec_lt(v_snd_2247_, v___x_2243_);
if (v___x_2251_ == 0)
{
lean_object* v___x_2253_; 
if (v_isShared_2250_ == 0)
{
v___x_2253_ = v___x_2249_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_fst_2246_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_snd_2247_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
else
{
uint8_t v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2259_; 
v___x_2255_ = 1;
v___x_2256_ = lean_array_fget_borrowed(v_original_2244_, v_snd_2247_);
v___x_2257_ = lean_box(v___x_2255_);
lean_inc(v___x_2256_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 1, v___x_2256_);
lean_ctor_set(v___x_2249_, 0, v___x_2257_);
v___x_2259_ = v___x_2249_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v___x_2257_);
lean_ctor_set(v_reuseFailAlloc_2265_, 1, v___x_2256_);
v___x_2259_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2260_ = lean_array_push(v_fst_2246_, v___x_2259_);
v___x_2261_ = lean_unsigned_to_nat(1u);
v___x_2262_ = lean_nat_add(v_snd_2247_, v___x_2261_);
lean_dec(v_snd_2247_);
v___x_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2260_);
lean_ctor_set(v___x_2263_, 1, v___x_2262_);
v_a_2245_ = v___x_2263_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg___boxed(lean_object* v___x_2267_, lean_object* v_original_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2267_, v_original_2268_, v_a_2269_);
lean_dec_ref(v_original_2268_);
lean_dec(v___x_2267_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(lean_object* v___x_2271_, lean_object* v_edited_2272_, lean_object* v_a_2273_){
_start:
{
lean_object* v_fst_2274_; lean_object* v_snd_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2294_; 
v_fst_2274_ = lean_ctor_get(v_a_2273_, 0);
v_snd_2275_ = lean_ctor_get(v_a_2273_, 1);
v_isSharedCheck_2294_ = !lean_is_exclusive(v_a_2273_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2277_ = v_a_2273_;
v_isShared_2278_ = v_isSharedCheck_2294_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_snd_2275_);
lean_inc(v_fst_2274_);
lean_dec(v_a_2273_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2294_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
uint8_t v___x_2279_; 
v___x_2279_ = lean_nat_dec_lt(v_snd_2275_, v___x_2271_);
if (v___x_2279_ == 0)
{
lean_object* v___x_2281_; 
if (v_isShared_2278_ == 0)
{
v___x_2281_ = v___x_2277_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_fst_2274_);
lean_ctor_set(v_reuseFailAlloc_2282_, 1, v_snd_2275_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
else
{
uint8_t v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2287_; 
v___x_2283_ = 0;
v___x_2284_ = lean_array_fget_borrowed(v_edited_2272_, v_snd_2275_);
v___x_2285_ = lean_box(v___x_2283_);
lean_inc(v___x_2284_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 1, v___x_2284_);
lean_ctor_set(v___x_2277_, 0, v___x_2285_);
v___x_2287_ = v___x_2277_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v___x_2285_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v___x_2284_);
v___x_2287_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2288_ = lean_array_push(v_fst_2274_, v___x_2287_);
v___x_2289_ = lean_unsigned_to_nat(1u);
v___x_2290_ = lean_nat_add(v_snd_2275_, v___x_2289_);
lean_dec(v_snd_2275_);
v___x_2291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2288_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
v_a_2273_ = v___x_2291_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg___boxed(lean_object* v___x_2295_, lean_object* v_edited_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2295_, v_edited_2296_, v_a_2297_);
lean_dec_ref(v_edited_2296_);
lean_dec(v___x_2295_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(lean_object* v___x_2299_, lean_object* v_original_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v_fst_2303_; lean_object* v_snd_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2328_; 
v_fst_2303_ = lean_ctor_get(v_a_2302_, 0);
v_snd_2304_ = lean_ctor_get(v_a_2302_, 1);
v_isSharedCheck_2328_ = !lean_is_exclusive(v_a_2302_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2306_ = v_a_2302_;
v_isShared_2307_ = v_isSharedCheck_2328_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_snd_2304_);
lean_inc(v_fst_2303_);
lean_dec(v_a_2302_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2328_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
uint8_t v___x_2308_; 
v___x_2308_ = lean_nat_dec_lt(v_snd_2304_, v___x_2299_);
if (v___x_2308_ == 0)
{
lean_object* v___x_2310_; 
if (v_isShared_2307_ == 0)
{
v___x_2310_ = v___x_2306_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_fst_2303_);
lean_ctor_set(v_reuseFailAlloc_2311_, 1, v_snd_2304_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
else
{
lean_object* v___x_2312_; lean_object* v___x_2313_; uint8_t v___x_2314_; 
v___x_2312_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2313_ = lean_array_get_borrowed(v___x_2312_, v_original_2300_, v_snd_2304_);
v___x_2314_ = lean_string_dec_eq(v___x_2313_, v_a_2301_);
if (v___x_2314_ == 0)
{
uint8_t v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2318_; 
v___x_2315_ = 1;
v___x_2316_ = lean_box(v___x_2315_);
lean_inc(v___x_2313_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 1, v___x_2313_);
lean_ctor_set(v___x_2306_, 0, v___x_2316_);
v___x_2318_ = v___x_2306_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2316_);
lean_ctor_set(v_reuseFailAlloc_2324_, 1, v___x_2313_);
v___x_2318_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v___x_2319_ = lean_array_push(v_fst_2303_, v___x_2318_);
v___x_2320_ = lean_unsigned_to_nat(1u);
v___x_2321_ = lean_nat_add(v_snd_2304_, v___x_2320_);
lean_dec(v_snd_2304_);
v___x_2322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2319_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
v_a_2302_ = v___x_2322_;
goto _start;
}
}
else
{
lean_object* v___x_2326_; 
if (v_isShared_2307_ == 0)
{
v___x_2326_ = v___x_2306_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_fst_2303_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_snd_2304_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg___boxed(lean_object* v___x_2329_, lean_object* v_original_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2329_, v_original_2330_, v_a_2331_, v_a_2332_);
lean_dec_ref(v_a_2331_);
lean_dec_ref(v_original_2330_);
lean_dec(v___x_2329_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(lean_object* v___x_2334_, lean_object* v_edited_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_){
_start:
{
lean_object* v_fst_2338_; lean_object* v_snd_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2363_; 
v_fst_2338_ = lean_ctor_get(v_a_2337_, 0);
v_snd_2339_ = lean_ctor_get(v_a_2337_, 1);
v_isSharedCheck_2363_ = !lean_is_exclusive(v_a_2337_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2341_ = v_a_2337_;
v_isShared_2342_ = v_isSharedCheck_2363_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_snd_2339_);
lean_inc(v_fst_2338_);
lean_dec(v_a_2337_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2363_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
uint8_t v___x_2343_; 
v___x_2343_ = lean_nat_dec_lt(v_snd_2339_, v___x_2334_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2345_; 
if (v_isShared_2342_ == 0)
{
v___x_2345_ = v___x_2341_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_fst_2338_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v_snd_2339_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
else
{
lean_object* v___x_2347_; lean_object* v___x_2348_; uint8_t v___x_2349_; 
v___x_2347_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2348_ = lean_array_get_borrowed(v___x_2347_, v_edited_2335_, v_snd_2339_);
v___x_2349_ = lean_string_dec_eq(v___x_2348_, v_a_2336_);
if (v___x_2349_ == 0)
{
uint8_t v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2353_; 
v___x_2350_ = 0;
v___x_2351_ = lean_box(v___x_2350_);
lean_inc(v___x_2348_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 1, v___x_2348_);
lean_ctor_set(v___x_2341_, 0, v___x_2351_);
v___x_2353_ = v___x_2341_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2351_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v___x_2348_);
v___x_2353_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2354_ = lean_array_push(v_fst_2338_, v___x_2353_);
v___x_2355_ = lean_unsigned_to_nat(1u);
v___x_2356_ = lean_nat_add(v_snd_2339_, v___x_2355_);
lean_dec(v_snd_2339_);
v___x_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2354_);
lean_ctor_set(v___x_2357_, 1, v___x_2356_);
v_a_2337_ = v___x_2357_;
goto _start;
}
}
else
{
lean_object* v___x_2361_; 
if (v_isShared_2342_ == 0)
{
v___x_2361_ = v___x_2341_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_fst_2338_);
lean_ctor_set(v_reuseFailAlloc_2362_, 1, v_snd_2339_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg___boxed(lean_object* v___x_2364_, lean_object* v_edited_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_){
_start:
{
lean_object* v_res_2368_; 
v_res_2368_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2364_, v_edited_2365_, v_a_2366_, v_a_2367_);
lean_dec_ref(v_a_2366_);
lean_dec_ref(v_edited_2365_);
lean_dec(v___x_2364_);
return v_res_2368_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(lean_object* v___x_2369_, lean_object* v_original_2370_, lean_object* v___x_2371_, lean_object* v_edited_2372_, lean_object* v_as_2373_, size_t v_sz_2374_, size_t v_i_2375_, lean_object* v_b_2376_){
_start:
{
uint8_t v___x_2377_; 
v___x_2377_ = lean_usize_dec_lt(v_i_2375_, v_sz_2374_);
if (v___x_2377_ == 0)
{
return v_b_2376_;
}
else
{
lean_object* v_snd_2378_; lean_object* v_fst_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2426_; 
v_snd_2378_ = lean_ctor_get(v_b_2376_, 1);
v_fst_2379_ = lean_ctor_get(v_b_2376_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_b_2376_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2381_ = v_b_2376_;
v_isShared_2382_ = v_isSharedCheck_2426_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_snd_2378_);
lean_inc(v_fst_2379_);
lean_dec(v_b_2376_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2426_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v_fst_2383_; lean_object* v_snd_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2425_; 
v_fst_2383_ = lean_ctor_get(v_snd_2378_, 0);
v_snd_2384_ = lean_ctor_get(v_snd_2378_, 1);
v_isSharedCheck_2425_ = !lean_is_exclusive(v_snd_2378_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2386_ = v_snd_2378_;
v_isShared_2387_ = v_isSharedCheck_2425_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_snd_2384_);
lean_inc(v_fst_2383_);
lean_dec(v_snd_2378_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2425_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v_a_2388_; lean_object* v___x_2390_; 
v_a_2388_ = lean_array_uget_borrowed(v_as_2373_, v_i_2375_);
if (v_isShared_2387_ == 0)
{
lean_ctor_set(v___x_2386_, 1, v_fst_2383_);
lean_ctor_set(v___x_2386_, 0, v_fst_2379_);
v___x_2390_ = v___x_2386_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2424_; 
v_reuseFailAlloc_2424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2424_, 0, v_fst_2379_);
lean_ctor_set(v_reuseFailAlloc_2424_, 1, v_fst_2383_);
v___x_2390_ = v_reuseFailAlloc_2424_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
lean_object* v___x_2391_; lean_object* v_fst_2392_; lean_object* v_snd_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2423_; 
v___x_2391_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2369_, v_original_2370_, v_a_2388_, v___x_2390_);
v_fst_2392_ = lean_ctor_get(v___x_2391_, 0);
v_snd_2393_ = lean_ctor_get(v___x_2391_, 1);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2395_ = v___x_2391_;
v_isShared_2396_ = v_isSharedCheck_2423_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_snd_2393_);
lean_inc(v_fst_2392_);
lean_dec(v___x_2391_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2423_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 1, v_snd_2384_);
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_fst_2392_);
lean_ctor_set(v_reuseFailAlloc_2422_, 1, v_snd_2384_);
v___x_2398_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
lean_object* v___x_2399_; lean_object* v_fst_2400_; lean_object* v_snd_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2421_; 
v___x_2399_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2371_, v_edited_2372_, v_a_2388_, v___x_2398_);
v_fst_2400_ = lean_ctor_get(v___x_2399_, 0);
v_snd_2401_ = lean_ctor_get(v___x_2399_, 1);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2403_ = v___x_2399_;
v_isShared_2404_ = v_isSharedCheck_2421_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_snd_2401_);
lean_inc(v_fst_2400_);
lean_dec(v___x_2399_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2421_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
uint8_t v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2408_; 
v___x_2405_ = 2;
v___x_2406_ = lean_box(v___x_2405_);
lean_inc(v_a_2388_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 1, v_a_2388_);
lean_ctor_set(v___x_2403_, 0, v___x_2406_);
v___x_2408_ = v___x_2403_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_a_2388_);
v___x_2408_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2414_; 
v___x_2409_ = lean_array_push(v_fst_2400_, v___x_2408_);
v___x_2410_ = lean_unsigned_to_nat(1u);
v___x_2411_ = lean_nat_add(v_snd_2393_, v___x_2410_);
lean_dec(v_snd_2393_);
v___x_2412_ = lean_nat_add(v_snd_2401_, v___x_2410_);
lean_dec(v_snd_2401_);
if (v_isShared_2382_ == 0)
{
lean_ctor_set(v___x_2381_, 1, v___x_2412_);
lean_ctor_set(v___x_2381_, 0, v___x_2411_);
v___x_2414_ = v___x_2381_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v___x_2411_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v___x_2412_);
v___x_2414_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
lean_object* v___x_2415_; size_t v___x_2416_; size_t v___x_2417_; 
v___x_2415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2415_, 0, v___x_2409_);
lean_ctor_set(v___x_2415_, 1, v___x_2414_);
v___x_2416_ = ((size_t)1ULL);
v___x_2417_ = lean_usize_add(v_i_2375_, v___x_2416_);
v_i_2375_ = v___x_2417_;
v_b_2376_ = v___x_2415_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14___boxed(lean_object* v___x_2427_, lean_object* v_original_2428_, lean_object* v___x_2429_, lean_object* v_edited_2430_, lean_object* v_as_2431_, lean_object* v_sz_2432_, lean_object* v_i_2433_, lean_object* v_b_2434_){
_start:
{
size_t v_sz_boxed_2435_; size_t v_i_boxed_2436_; lean_object* v_res_2437_; 
v_sz_boxed_2435_ = lean_unbox_usize(v_sz_2432_);
lean_dec(v_sz_2432_);
v_i_boxed_2436_ = lean_unbox_usize(v_i_2433_);
lean_dec(v_i_2433_);
v_res_2437_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v___x_2427_, v_original_2428_, v___x_2429_, v_edited_2430_, v_as_2431_, v_sz_boxed_2435_, v_i_boxed_2436_, v_b_2434_);
lean_dec_ref(v_as_2431_);
lean_dec_ref(v_edited_2430_);
lean_dec(v___x_2429_);
lean_dec_ref(v_original_2428_);
lean_dec(v___x_2427_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(lean_object* v___x_2438_, lean_object* v_edited_2439_, lean_object* v___x_2440_, lean_object* v_original_2441_, lean_object* v_as_2442_, size_t v_sz_2443_, size_t v_i_2444_, lean_object* v_b_2445_){
_start:
{
uint8_t v___x_2446_; 
v___x_2446_ = lean_usize_dec_lt(v_i_2444_, v_sz_2443_);
if (v___x_2446_ == 0)
{
return v_b_2445_;
}
else
{
lean_object* v_snd_2447_; lean_object* v_fst_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2495_; 
v_snd_2447_ = lean_ctor_get(v_b_2445_, 1);
v_fst_2448_ = lean_ctor_get(v_b_2445_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v_b_2445_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2450_ = v_b_2445_;
v_isShared_2451_ = v_isSharedCheck_2495_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_snd_2447_);
lean_inc(v_fst_2448_);
lean_dec(v_b_2445_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2495_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v_fst_2452_; lean_object* v_snd_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2494_; 
v_fst_2452_ = lean_ctor_get(v_snd_2447_, 0);
v_snd_2453_ = lean_ctor_get(v_snd_2447_, 1);
v_isSharedCheck_2494_ = !lean_is_exclusive(v_snd_2447_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2455_ = v_snd_2447_;
v_isShared_2456_ = v_isSharedCheck_2494_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_snd_2453_);
lean_inc(v_fst_2452_);
lean_dec(v_snd_2447_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2494_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v_a_2457_; lean_object* v___x_2459_; 
v_a_2457_ = lean_array_uget_borrowed(v_as_2442_, v_i_2444_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 1, v_fst_2452_);
lean_ctor_set(v___x_2455_, 0, v_fst_2448_);
v___x_2459_ = v___x_2455_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_fst_2448_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v_fst_2452_);
v___x_2459_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
lean_object* v___x_2460_; lean_object* v_fst_2461_; lean_object* v_snd_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2492_; 
v___x_2460_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2440_, v_original_2441_, v_a_2457_, v___x_2459_);
v_fst_2461_ = lean_ctor_get(v___x_2460_, 0);
v_snd_2462_ = lean_ctor_get(v___x_2460_, 1);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2464_ = v___x_2460_;
v_isShared_2465_ = v_isSharedCheck_2492_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_snd_2462_);
lean_inc(v_fst_2461_);
lean_dec(v___x_2460_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2492_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
lean_ctor_set(v___x_2464_, 1, v_snd_2453_);
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_fst_2461_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v_snd_2453_);
v___x_2467_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
lean_object* v___x_2468_; lean_object* v_fst_2469_; lean_object* v_snd_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2490_; 
v___x_2468_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2438_, v_edited_2439_, v_a_2457_, v___x_2467_);
v_fst_2469_ = lean_ctor_get(v___x_2468_, 0);
v_snd_2470_ = lean_ctor_get(v___x_2468_, 1);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2472_ = v___x_2468_;
v_isShared_2473_ = v_isSharedCheck_2490_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_snd_2470_);
lean_inc(v_fst_2469_);
lean_dec(v___x_2468_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2490_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
uint8_t v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2477_; 
v___x_2474_ = 2;
v___x_2475_ = lean_box(v___x_2474_);
lean_inc(v_a_2457_);
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 1, v_a_2457_);
lean_ctor_set(v___x_2472_, 0, v___x_2475_);
v___x_2477_ = v___x_2472_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v_a_2457_);
v___x_2477_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2483_; 
v___x_2478_ = lean_array_push(v_fst_2469_, v___x_2477_);
v___x_2479_ = lean_unsigned_to_nat(1u);
v___x_2480_ = lean_nat_add(v_snd_2462_, v___x_2479_);
lean_dec(v_snd_2462_);
v___x_2481_ = lean_nat_add(v_snd_2470_, v___x_2479_);
lean_dec(v_snd_2470_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 1, v___x_2481_);
lean_ctor_set(v___x_2450_, 0, v___x_2480_);
v___x_2483_ = v___x_2450_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2488_; 
v_reuseFailAlloc_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2488_, 0, v___x_2480_);
lean_ctor_set(v_reuseFailAlloc_2488_, 1, v___x_2481_);
v___x_2483_ = v_reuseFailAlloc_2488_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
lean_object* v___x_2484_; size_t v___x_2485_; size_t v___x_2486_; lean_object* v___x_2487_; 
v___x_2484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2478_);
lean_ctor_set(v___x_2484_, 1, v___x_2483_);
v___x_2485_ = ((size_t)1ULL);
v___x_2486_ = lean_usize_add(v_i_2444_, v___x_2485_);
v___x_2487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v___x_2440_, v_original_2441_, v___x_2438_, v_edited_2439_, v_as_2442_, v_sz_2443_, v___x_2486_, v___x_2484_);
return v___x_2487_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4___boxed(lean_object* v___x_2496_, lean_object* v_edited_2497_, lean_object* v___x_2498_, lean_object* v_original_2499_, lean_object* v_as_2500_, lean_object* v_sz_2501_, lean_object* v_i_2502_, lean_object* v_b_2503_){
_start:
{
size_t v_sz_boxed_2504_; size_t v_i_boxed_2505_; lean_object* v_res_2506_; 
v_sz_boxed_2504_ = lean_unbox_usize(v_sz_2501_);
lean_dec(v_sz_2501_);
v_i_boxed_2505_ = lean_unbox_usize(v_i_2502_);
lean_dec(v_i_2502_);
v_res_2506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v___x_2496_, v_edited_2497_, v___x_2498_, v_original_2499_, v_as_2500_, v_sz_boxed_2504_, v_i_boxed_2505_, v_b_2503_);
lean_dec_ref(v_as_2500_);
lean_dec_ref(v_original_2499_);
lean_dec(v___x_2498_);
lean_dec_ref(v_edited_2497_);
lean_dec(v___x_2496_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(size_t v_sz_2507_, size_t v_i_2508_, lean_object* v_bs_2509_){
_start:
{
uint8_t v___x_2510_; 
v___x_2510_ = lean_usize_dec_lt(v_i_2508_, v_sz_2507_);
if (v___x_2510_ == 0)
{
return v_bs_2509_;
}
else
{
lean_object* v_v_2511_; lean_object* v___x_2512_; lean_object* v_bs_x27_2513_; uint8_t v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; size_t v___x_2517_; size_t v___x_2518_; lean_object* v___x_2519_; 
v_v_2511_ = lean_array_uget(v_bs_2509_, v_i_2508_);
v___x_2512_ = lean_unsigned_to_nat(0u);
v_bs_x27_2513_ = lean_array_uset(v_bs_2509_, v_i_2508_, v___x_2512_);
v___x_2514_ = 1;
v___x_2515_ = lean_box(v___x_2514_);
v___x_2516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2515_);
lean_ctor_set(v___x_2516_, 1, v_v_2511_);
v___x_2517_ = ((size_t)1ULL);
v___x_2518_ = lean_usize_add(v_i_2508_, v___x_2517_);
v___x_2519_ = lean_array_uset(v_bs_x27_2513_, v_i_2508_, v___x_2516_);
v_i_2508_ = v___x_2518_;
v_bs_2509_ = v___x_2519_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7___boxed(lean_object* v_sz_2521_, lean_object* v_i_2522_, lean_object* v_bs_2523_){
_start:
{
size_t v_sz_boxed_2524_; size_t v_i_boxed_2525_; lean_object* v_res_2526_; 
v_sz_boxed_2524_ = lean_unbox_usize(v_sz_2521_);
lean_dec(v_sz_2521_);
v_i_boxed_2525_ = lean_unbox_usize(v_i_2522_);
lean_dec(v_i_2522_);
v_res_2526_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_boxed_2524_, v_i_boxed_2525_, v_bs_2523_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(lean_object* v_original_2532_, lean_object* v_edited_2533_){
_start:
{
lean_object* v_i_2534_; lean_object* v___x_2535_; uint8_t v___x_2536_; 
v_i_2534_ = lean_unsigned_to_nat(0u);
v___x_2535_ = lean_array_get_size(v_original_2532_);
v___x_2536_ = lean_nat_dec_lt(v_i_2534_, v___x_2535_);
if (v___x_2536_ == 0)
{
size_t v_sz_2537_; size_t v___x_2538_; lean_object* v___x_2539_; 
lean_dec_ref(v_original_2532_);
v_sz_2537_ = lean_array_size(v_edited_2533_);
v___x_2538_ = ((size_t)0ULL);
v___x_2539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_2537_, v___x_2538_, v_edited_2533_);
return v___x_2539_;
}
else
{
lean_object* v___x_2540_; uint8_t v___x_2541_; 
v___x_2540_ = lean_array_get_size(v_edited_2533_);
v___x_2541_ = lean_nat_dec_lt(v_i_2534_, v___x_2540_);
if (v___x_2541_ == 0)
{
size_t v_sz_2542_; size_t v___x_2543_; lean_object* v___x_2544_; 
lean_dec_ref(v_edited_2533_);
v_sz_2542_ = lean_array_size(v_original_2532_);
v___x_2543_ = ((size_t)0ULL);
v___x_2544_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_2542_, v___x_2543_, v_original_2532_);
return v___x_2544_;
}
else
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v_ds_2547_; lean_object* v___x_2548_; size_t v_sz_2549_; size_t v___x_2550_; lean_object* v___x_2551_; lean_object* v_snd_2552_; lean_object* v_fst_2553_; lean_object* v_fst_2554_; lean_object* v_snd_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2574_; 
lean_inc_ref(v_original_2532_);
v___x_2545_ = l_Array_toSubarray___redArg(v_original_2532_, v_i_2534_, v___x_2535_);
lean_inc_ref(v_edited_2533_);
v___x_2546_ = l_Array_toSubarray___redArg(v_edited_2533_, v_i_2534_, v___x_2540_);
v_ds_2547_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v___x_2545_, v___x_2546_);
v___x_2548_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__1));
v_sz_2549_ = lean_array_size(v_ds_2547_);
v___x_2550_ = ((size_t)0ULL);
v___x_2551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v___x_2540_, v_edited_2533_, v___x_2535_, v_original_2532_, v_ds_2547_, v_sz_2549_, v___x_2550_, v___x_2548_);
lean_dec_ref(v_ds_2547_);
v_snd_2552_ = lean_ctor_get(v___x_2551_, 1);
lean_inc(v_snd_2552_);
v_fst_2553_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_fst_2553_);
lean_dec_ref(v___x_2551_);
v_fst_2554_ = lean_ctor_get(v_snd_2552_, 0);
v_snd_2555_ = lean_ctor_get(v_snd_2552_, 1);
v_isSharedCheck_2574_ = !lean_is_exclusive(v_snd_2552_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2557_ = v_snd_2552_;
v_isShared_2558_ = v_isSharedCheck_2574_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_snd_2555_);
lean_inc(v_fst_2554_);
lean_dec(v_snd_2552_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2574_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 1, v_fst_2554_);
lean_ctor_set(v___x_2557_, 0, v_fst_2553_);
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_fst_2553_);
lean_ctor_set(v_reuseFailAlloc_2573_, 1, v_fst_2554_);
v___x_2560_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
lean_object* v___x_2561_; lean_object* v_fst_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2571_; 
v___x_2561_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2535_, v_original_2532_, v___x_2560_);
lean_dec_ref(v_original_2532_);
v_fst_2562_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2571_ == 0)
{
lean_object* v_unused_2572_; 
v_unused_2572_ = lean_ctor_get(v___x_2561_, 1);
lean_dec(v_unused_2572_);
v___x_2564_ = v___x_2561_;
v_isShared_2565_ = v_isSharedCheck_2571_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_fst_2562_);
lean_dec(v___x_2561_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2571_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 1, v_snd_2555_);
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_fst_2562_);
lean_ctor_set(v_reuseFailAlloc_2570_, 1, v_snd_2555_);
v___x_2567_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
lean_object* v___x_2568_; lean_object* v_fst_2569_; 
v___x_2568_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2540_, v_edited_2533_, v___x_2567_);
lean_dec_ref(v_edited_2533_);
v_fst_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_fst_2569_);
lean_dec_ref(v___x_2568_);
return v_fst_2569_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(lean_object* v___x_2575_, uint8_t v_inSubst_2576_, lean_object* v___x_2577_, lean_object* v_____r_2578_, lean_object* v_wssIdx_2579_){
_start:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2580_ = lean_box(v_inSubst_2576_);
v___x_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2575_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
v___x_2582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2582_, 0, v_wssIdx_2579_);
lean_ctor_set(v___x_2582_, 1, v___x_2581_);
v___x_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2577_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
v___x_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1___boxed(lean_object* v___x_2585_, lean_object* v_inSubst_2586_, lean_object* v___x_2587_, lean_object* v_____r_2588_, lean_object* v_wssIdx_2589_){
_start:
{
uint8_t v_inSubst_boxed_2590_; lean_object* v_res_2591_; 
v_inSubst_boxed_2590_ = lean_unbox(v_inSubst_2586_);
v_res_2591_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2585_, v_inSubst_boxed_2590_, v___x_2587_, v_____r_2588_, v_wssIdx_2589_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(lean_object* v_fst_2592_, uint8_t v___x_2593_, lean_object* v_fst_2594_, lean_object* v___x_2595_, lean_object* v_00___2596_){
_start:
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2597_ = lean_box(v___x_2593_);
v___x_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2598_, 0, v_fst_2592_);
lean_ctor_set(v___x_2598_, 1, v___x_2597_);
v___x_2599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2599_, 0, v_fst_2594_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
v___x_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2595_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
v___x_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
return v___x_2601_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0___boxed(lean_object* v_fst_2602_, lean_object* v___x_2603_, lean_object* v_fst_2604_, lean_object* v___x_2605_, lean_object* v_00___2606_){
_start:
{
uint8_t v___x_9163__boxed_2607_; lean_object* v_res_2608_; 
v___x_9163__boxed_2607_ = lean_unbox(v___x_2603_);
v_res_2608_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2602_, v___x_9163__boxed_2607_, v_fst_2604_, v___x_2605_, v_00___2606_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(uint8_t v_inSubst_2609_, lean_object* v_snd_2610_, lean_object* v_fst_2611_, lean_object* v_____r_2612_, lean_object* v_withWs_2613_, lean_object* v_wssIdx_2614_){
_start:
{
lean_object* v_wss_x27Idx_2616_; uint8_t v___x_2622_; 
v___x_2622_ = lean_unbox(v_snd_2610_);
if (v___x_2622_ == 0)
{
v_wss_x27Idx_2616_ = v_fst_2611_;
goto v___jp_2615_;
}
else
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = lean_unsigned_to_nat(1u);
v___x_2624_ = lean_nat_add(v_fst_2611_, v___x_2623_);
lean_dec(v_fst_2611_);
v_wss_x27Idx_2616_ = v___x_2624_;
goto v___jp_2615_;
}
v___jp_2615_:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
v___x_2617_ = lean_box(v_inSubst_2609_);
v___x_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2618_, 0, v_wss_x27Idx_2616_);
lean_ctor_set(v___x_2618_, 1, v___x_2617_);
v___x_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2619_, 0, v_wssIdx_2614_);
lean_ctor_set(v___x_2619_, 1, v___x_2618_);
v___x_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2620_, 0, v_withWs_2613_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
v___x_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2621_, 0, v___x_2620_);
return v___x_2621_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2___boxed(lean_object* v_inSubst_2625_, lean_object* v_snd_2626_, lean_object* v_fst_2627_, lean_object* v_____r_2628_, lean_object* v_withWs_2629_, lean_object* v_wssIdx_2630_){
_start:
{
uint8_t v_inSubst_boxed_2631_; lean_object* v_res_2632_; 
v_inSubst_boxed_2631_ = lean_unbox(v_inSubst_2625_);
v_res_2632_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_boxed_2631_, v_snd_2626_, v_fst_2627_, v_____r_2628_, v_withWs_2629_, v_wssIdx_2630_);
lean_dec(v_snd_2626_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(lean_object* v_upperBound_2633_, lean_object* v_diff_2634_, lean_object* v_snd_2635_, lean_object* v_snd_2636_, lean_object* v_a_2637_, lean_object* v_b_2638_){
_start:
{
lean_object* v_a_2640_; lean_object* v___y_2645_; uint8_t v___x_2648_; 
v___x_2648_ = lean_nat_dec_lt(v_a_2637_, v_upperBound_2633_);
if (v___x_2648_ == 0)
{
lean_dec(v_a_2637_);
return v_b_2638_;
}
else
{
lean_object* v___x_2649_; lean_object* v_snd_2650_; lean_object* v_snd_2651_; lean_object* v_fst_2652_; lean_object* v_fst_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2793_; 
v___x_2649_ = lean_array_fget_borrowed(v_diff_2634_, v_a_2637_);
v_snd_2650_ = lean_ctor_get(v_b_2638_, 1);
lean_inc(v_snd_2650_);
v_snd_2651_ = lean_ctor_get(v_snd_2650_, 1);
lean_inc(v_snd_2651_);
v_fst_2652_ = lean_ctor_get(v___x_2649_, 0);
v_fst_2653_ = lean_ctor_get(v_b_2638_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v_b_2638_);
if (v_isSharedCheck_2793_ == 0)
{
lean_object* v_unused_2794_; 
v_unused_2794_ = lean_ctor_get(v_b_2638_, 1);
lean_dec(v_unused_2794_);
v___x_2655_ = v_b_2638_;
v_isShared_2656_ = v_isSharedCheck_2793_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_fst_2653_);
lean_dec(v_b_2638_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2793_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v_fst_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2791_; 
v_fst_2657_ = lean_ctor_get(v_snd_2650_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v_snd_2650_);
if (v_isSharedCheck_2791_ == 0)
{
lean_object* v_unused_2792_; 
v_unused_2792_ = lean_ctor_get(v_snd_2650_, 1);
lean_dec(v_unused_2792_);
v___x_2659_ = v_snd_2650_;
v_isShared_2660_ = v_isSharedCheck_2791_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_fst_2657_);
lean_dec(v_snd_2650_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2791_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v_fst_2661_; lean_object* v_snd_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2790_; 
v_fst_2661_ = lean_ctor_get(v_snd_2651_, 0);
v_snd_2662_ = lean_ctor_get(v_snd_2651_, 1);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_snd_2651_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2664_ = v_snd_2651_;
v_isShared_2665_ = v_isSharedCheck_2790_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_snd_2662_);
lean_inc(v_fst_2661_);
lean_dec(v_snd_2651_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2790_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2666_; lean_object* v___y_2668_; lean_object* v___y_2683_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; 
lean_inc(v___x_2649_);
v___x_2666_ = lean_array_push(v_fst_2653_, v___x_2649_);
v___x_2691_ = lean_unsigned_to_nat(1u);
v___x_2692_ = lean_nat_add(v_a_2637_, v___x_2691_);
v___x_2693_ = lean_array_get_size(v_diff_2634_);
v___x_2694_ = lean_nat_dec_lt(v___x_2692_, v___x_2693_);
if (v___x_2694_ == 0)
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
lean_dec(v___x_2692_);
lean_del_object(v___x_2664_);
lean_del_object(v___x_2659_);
lean_del_object(v___x_2655_);
v___x_2695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2695_, 0, v_fst_2661_);
lean_ctor_set(v___x_2695_, 1, v_snd_2662_);
v___x_2696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2696_, 0, v_fst_2657_);
lean_ctor_set(v___x_2696_, 1, v___x_2695_);
v___x_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2666_);
lean_ctor_set(v___x_2697_, 1, v___x_2696_);
v_a_2640_ = v___x_2697_;
goto v___jp_2639_;
}
else
{
lean_object* v___x_2698_; lean_object* v_fst_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2788_; 
v___x_2698_ = lean_array_fget(v_diff_2634_, v___x_2692_);
lean_dec(v___x_2692_);
v_fst_2699_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2788_ == 0)
{
lean_object* v_unused_2789_; 
v_unused_2789_ = lean_ctor_get(v___x_2698_, 1);
lean_dec(v_unused_2789_);
v___x_2701_ = v___x_2698_;
v_isShared_2702_ = v_isSharedCheck_2788_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_fst_2699_);
lean_dec(v___x_2698_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2788_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
uint8_t v_inSubst_2703_; lean_object* v___y_2705_; lean_object* v___x_2714_; uint8_t v___x_2715_; 
v_inSubst_2703_ = 0;
v___x_2714_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2715_ = lean_unbox(v_fst_2652_);
switch(v___x_2715_)
{
case 0:
{
uint8_t v___x_2716_; 
lean_del_object(v___x_2664_);
lean_del_object(v___x_2659_);
lean_del_object(v___x_2655_);
v___x_2716_ = lean_unbox(v_fst_2699_);
switch(v___x_2716_)
{
case 0:
{
lean_object* v___x_2717_; lean_object* v___x_2719_; 
v___x_2717_ = lean_array_get_borrowed(v___x_2714_, v_snd_2635_, v_fst_2661_);
lean_inc(v___x_2717_);
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 1, v___x_2717_);
v___x_2719_ = v___x_2701_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_fst_2699_);
lean_ctor_set(v_reuseFailAlloc_2725_, 1, v___x_2717_);
v___x_2719_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2720_ = lean_array_push(v___x_2666_, v___x_2719_);
v___x_2721_ = lean_nat_add(v_fst_2661_, v___x_2691_);
lean_dec(v_fst_2661_);
v___x_2722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
lean_ctor_set(v___x_2722_, 1, v_snd_2662_);
v___x_2723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2723_, 0, v_fst_2657_);
lean_ctor_set(v___x_2723_, 1, v___x_2722_);
v___x_2724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2720_);
lean_ctor_set(v___x_2724_, 1, v___x_2723_);
v_a_2640_ = v___x_2724_;
goto v___jp_2639_;
}
}
case 1:
{
lean_object* v___x_2726_; lean_object* v___x_2727_; 
lean_del_object(v___x_2701_);
lean_dec(v_fst_2699_);
lean_dec(v_snd_2662_);
v___x_2726_ = lean_box(0);
v___x_2727_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2661_, v___x_2648_, v_fst_2657_, v___x_2666_, v___x_2726_);
v___y_2645_ = v___x_2727_;
goto v___jp_2644_;
}
default: 
{
lean_object* v___x_2728_; uint8_t v___x_2729_; 
lean_dec(v_fst_2699_);
v___x_2728_ = lean_array_get_borrowed(v___x_2714_, v_snd_2635_, v_fst_2661_);
v___x_2729_ = lean_unbox(v_snd_2662_);
if (v___x_2729_ == 0)
{
lean_object* v___x_2731_; 
lean_inc(v___x_2728_);
lean_inc(v_fst_2652_);
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 1, v___x_2728_);
lean_ctor_set(v___x_2701_, 0, v_fst_2652_);
v___x_2731_ = v___x_2701_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_fst_2652_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v___x_2728_);
v___x_2731_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2732_ = lean_mk_empty_array_with_capacity(v___x_2691_);
v___x_2733_ = lean_array_push(v___x_2732_, v___x_2731_);
v___y_2705_ = v___x_2733_;
goto v___jp_2704_;
}
}
else
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
lean_del_object(v___x_2701_);
v___x_2735_ = lean_array_get_borrowed(v___x_2714_, v_snd_2636_, v_fst_2657_);
lean_inc(v___x_2728_);
lean_inc(v___x_2735_);
v___x_2736_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2735_, v___x_2728_);
v___y_2705_ = v___x_2736_;
goto v___jp_2704_;
}
}
}
}
case 1:
{
uint8_t v___x_2737_; 
lean_del_object(v___x_2664_);
lean_del_object(v___x_2659_);
lean_del_object(v___x_2655_);
v___x_2737_ = lean_unbox(v_fst_2699_);
switch(v___x_2737_)
{
case 0:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; 
lean_del_object(v___x_2701_);
lean_dec(v_fst_2699_);
lean_dec(v_snd_2662_);
v___x_2738_ = lean_box(0);
v___x_2739_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2661_, v___x_2648_, v_fst_2657_, v___x_2666_, v___x_2738_);
v___y_2645_ = v___x_2739_;
goto v___jp_2644_;
}
case 1:
{
lean_object* v___x_2740_; lean_object* v___x_2742_; 
v___x_2740_ = lean_array_get_borrowed(v___x_2714_, v_snd_2636_, v_fst_2657_);
lean_inc(v___x_2740_);
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 1, v___x_2740_);
v___x_2742_ = v___x_2701_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_fst_2699_);
lean_ctor_set(v_reuseFailAlloc_2748_, 1, v___x_2740_);
v___x_2742_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2743_ = lean_array_push(v___x_2666_, v___x_2742_);
v___x_2744_ = lean_nat_add(v_fst_2657_, v___x_2691_);
lean_dec(v_fst_2657_);
v___x_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2745_, 0, v_fst_2661_);
lean_ctor_set(v___x_2745_, 1, v_snd_2662_);
v___x_2746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2744_);
lean_ctor_set(v___x_2746_, 1, v___x_2745_);
v___x_2747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2743_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
v_a_2640_ = v___x_2747_;
goto v___jp_2639_;
}
}
default: 
{
uint8_t v___x_2752_; 
lean_dec(v_fst_2699_);
v___x_2752_ = lean_unbox(v_snd_2662_);
if (v___x_2752_ == 0)
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; uint8_t v___x_2757_; 
v___x_2753_ = lean_array_get_borrowed(v___x_2714_, v_snd_2636_, v_fst_2657_);
v___x_2754_ = lean_unsigned_to_nat(0u);
v___x_2755_ = lean_string_utf8_byte_size(v___x_2753_);
lean_inc(v___x_2753_);
v___x_2756_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2753_);
lean_ctor_set(v___x_2756_, 1, v___x_2754_);
lean_ctor_set(v___x_2756_, 2, v___x_2755_);
v___x_2757_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_2756_);
lean_dec_ref_known(v___x_2756_, 3);
if (v___x_2757_ == 0)
{
lean_object* v___x_2759_; 
lean_inc(v___x_2753_);
lean_inc(v_fst_2652_);
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 1, v___x_2753_);
lean_ctor_set(v___x_2701_, 0, v_fst_2652_);
v___x_2759_ = v___x_2701_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_fst_2652_);
lean_ctor_set(v_reuseFailAlloc_2764_, 1, v___x_2753_);
v___x_2759_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2760_ = lean_array_push(v___x_2666_, v___x_2759_);
v___x_2761_ = lean_nat_add(v_fst_2657_, v___x_2691_);
lean_dec(v_fst_2657_);
v___x_2762_ = lean_box(0);
v___x_2763_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2703_, v_snd_2662_, v_fst_2661_, v___x_2762_, v___x_2760_, v___x_2761_);
lean_dec(v_snd_2662_);
v___y_2645_ = v___x_2763_;
goto v___jp_2644_;
}
}
else
{
lean_del_object(v___x_2701_);
goto v___jp_2749_;
}
}
else
{
lean_del_object(v___x_2701_);
goto v___jp_2749_;
}
v___jp_2749_:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = lean_box(0);
v___x_2751_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2703_, v_snd_2662_, v_fst_2661_, v___x_2750_, v___x_2666_, v_fst_2657_);
lean_dec(v_snd_2662_);
v___y_2645_ = v___x_2751_;
goto v___jp_2644_;
}
}
}
}
default: 
{
uint8_t v___x_2765_; 
v___x_2765_ = lean_unbox(v_fst_2699_);
if (v___x_2765_ == 1)
{
lean_object* v___x_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; 
v___x_2766_ = lean_array_get_borrowed(v___x_2714_, v_snd_2636_, v_fst_2657_);
v___x_2767_ = lean_array_get_size(v_snd_2635_);
v___x_2768_ = lean_nat_dec_lt(v_fst_2661_, v___x_2767_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2770_; 
lean_inc(v___x_2766_);
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 1, v___x_2766_);
v___x_2770_ = v___x_2701_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_fst_2699_);
lean_ctor_set(v_reuseFailAlloc_2773_, 1, v___x_2766_);
v___x_2770_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = lean_mk_empty_array_with_capacity(v___x_2691_);
v___x_2772_ = lean_array_push(v___x_2771_, v___x_2770_);
v___y_2668_ = v___x_2772_;
goto v___jp_2667_;
}
}
else
{
lean_object* v___x_2774_; lean_object* v___x_2775_; 
lean_del_object(v___x_2701_);
lean_dec(v_fst_2699_);
v___x_2774_ = lean_array_fget_borrowed(v_snd_2635_, v_fst_2661_);
lean_inc(v___x_2774_);
lean_inc(v___x_2766_);
v___x_2775_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2766_, v___x_2774_);
v___y_2668_ = v___x_2775_;
goto v___jp_2667_;
}
}
else
{
lean_object* v___x_2776_; lean_object* v___x_2777_; uint8_t v___x_2778_; 
lean_dec(v_fst_2699_);
lean_del_object(v___x_2664_);
lean_del_object(v___x_2659_);
lean_del_object(v___x_2655_);
v___x_2776_ = lean_array_get_borrowed(v___x_2714_, v_snd_2635_, v_fst_2661_);
v___x_2777_ = lean_array_get_size(v_snd_2636_);
v___x_2778_ = lean_nat_dec_lt(v_fst_2657_, v___x_2777_);
if (v___x_2778_ == 0)
{
uint8_t v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2782_; 
v___x_2779_ = 0;
v___x_2780_ = lean_box(v___x_2779_);
lean_inc(v___x_2776_);
if (v_isShared_2702_ == 0)
{
lean_ctor_set(v___x_2701_, 1, v___x_2776_);
lean_ctor_set(v___x_2701_, 0, v___x_2780_);
v___x_2782_ = v___x_2701_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v___x_2780_);
lean_ctor_set(v_reuseFailAlloc_2785_, 1, v___x_2776_);
v___x_2782_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = lean_mk_empty_array_with_capacity(v___x_2691_);
v___x_2784_ = lean_array_push(v___x_2783_, v___x_2782_);
v___y_2683_ = v___x_2784_;
goto v___jp_2682_;
}
}
else
{
lean_object* v___x_2786_; lean_object* v___x_2787_; 
lean_del_object(v___x_2701_);
v___x_2786_ = lean_array_fget_borrowed(v_snd_2636_, v_fst_2657_);
lean_inc(v___x_2776_);
lean_inc(v___x_2786_);
v___x_2787_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2786_, v___x_2776_);
v___y_2683_ = v___x_2787_;
goto v___jp_2682_;
}
}
}
}
v___jp_2704_:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; uint8_t v___x_2708_; 
v___x_2706_ = l_Array_append___redArg(v___x_2666_, v___y_2705_);
lean_dec_ref(v___y_2705_);
v___x_2707_ = lean_nat_add(v_fst_2661_, v___x_2691_);
lean_dec(v_fst_2661_);
v___x_2708_ = lean_unbox(v_snd_2662_);
lean_dec(v_snd_2662_);
if (v___x_2708_ == 0)
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2709_ = lean_box(0);
v___x_2710_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2707_, v_inSubst_2703_, v___x_2706_, v___x_2709_, v_fst_2657_);
v___y_2645_ = v___x_2710_;
goto v___jp_2644_;
}
else
{
lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v___x_2711_ = lean_nat_add(v_fst_2657_, v___x_2691_);
lean_dec(v_fst_2657_);
v___x_2712_ = lean_box(0);
v___x_2713_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2707_, v_inSubst_2703_, v___x_2706_, v___x_2712_, v___x_2711_);
v___y_2645_ = v___x_2713_;
goto v___jp_2644_;
}
}
}
}
v___jp_2667_:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2674_; 
v___x_2669_ = l_Array_append___redArg(v___x_2666_, v___y_2668_);
lean_dec_ref(v___y_2668_);
v___x_2670_ = lean_unsigned_to_nat(1u);
v___x_2671_ = lean_nat_add(v_fst_2657_, v___x_2670_);
lean_dec(v_fst_2657_);
v___x_2672_ = lean_nat_add(v_fst_2661_, v___x_2670_);
lean_dec(v_fst_2661_);
if (v_isShared_2665_ == 0)
{
lean_ctor_set(v___x_2664_, 0, v___x_2672_);
v___x_2674_ = v___x_2664_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v___x_2672_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v_snd_2662_);
v___x_2674_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
lean_object* v___x_2676_; 
if (v_isShared_2660_ == 0)
{
lean_ctor_set(v___x_2659_, 1, v___x_2674_);
lean_ctor_set(v___x_2659_, 0, v___x_2671_);
v___x_2676_ = v___x_2659_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v___x_2671_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v___x_2674_);
v___x_2676_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
lean_object* v___x_2678_; 
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 1, v___x_2676_);
lean_ctor_set(v___x_2655_, 0, v___x_2669_);
v___x_2678_ = v___x_2655_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v___x_2669_);
lean_ctor_set(v_reuseFailAlloc_2679_, 1, v___x_2676_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
v_a_2640_ = v___x_2678_;
goto v___jp_2639_;
}
}
}
}
v___jp_2682_:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2684_ = l_Array_append___redArg(v___x_2666_, v___y_2683_);
lean_dec_ref(v___y_2683_);
v___x_2685_ = lean_unsigned_to_nat(1u);
v___x_2686_ = lean_nat_add(v_fst_2657_, v___x_2685_);
lean_dec(v_fst_2657_);
v___x_2687_ = lean_nat_add(v_fst_2661_, v___x_2685_);
lean_dec(v_fst_2661_);
v___x_2688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2688_, 0, v___x_2687_);
lean_ctor_set(v___x_2688_, 1, v_snd_2662_);
v___x_2689_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2689_, 0, v___x_2686_);
lean_ctor_set(v___x_2689_, 1, v___x_2688_);
v___x_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2684_);
lean_ctor_set(v___x_2690_, 1, v___x_2689_);
v_a_2640_ = v___x_2690_;
goto v___jp_2639_;
}
}
}
}
}
v___jp_2639_:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; 
v___x_2641_ = lean_unsigned_to_nat(1u);
v___x_2642_ = lean_nat_add(v_a_2637_, v___x_2641_);
lean_dec(v_a_2637_);
v_a_2637_ = v___x_2642_;
v_b_2638_ = v_a_2640_;
goto _start;
}
v___jp_2644_:
{
if (lean_obj_tag(v___y_2645_) == 0)
{
lean_object* v_a_2646_; 
lean_dec(v_a_2637_);
v_a_2646_ = lean_ctor_get(v___y_2645_, 0);
lean_inc(v_a_2646_);
lean_dec_ref_known(v___y_2645_, 1);
return v_a_2646_;
}
else
{
lean_object* v_a_2647_; 
v_a_2647_ = lean_ctor_get(v___y_2645_, 0);
lean_inc(v_a_2647_);
lean_dec_ref_known(v___y_2645_, 1);
v_a_2640_ = v_a_2647_;
goto v___jp_2639_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___boxed(lean_object* v_upperBound_2795_, lean_object* v_diff_2796_, lean_object* v_snd_2797_, lean_object* v_snd_2798_, lean_object* v_a_2799_, lean_object* v_b_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2795_, v_diff_2796_, v_snd_2797_, v_snd_2798_, v_a_2799_, v_b_2800_);
lean_dec_ref(v_snd_2798_);
lean_dec_ref(v_snd_2797_);
lean_dec_ref(v_diff_2796_);
lean_dec(v_upperBound_2795_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(lean_object* v_s_2812_, lean_object* v_s_x27_2813_){
_start:
{
lean_object* v___x_2814_; lean_object* v_fst_2815_; lean_object* v_snd_2816_; lean_object* v___x_2817_; lean_object* v_fst_2818_; lean_object* v_snd_2819_; lean_object* v_diff_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v_fst_2825_; lean_object* v___x_2826_; size_t v_sz_2827_; size_t v___x_2828_; lean_object* v___x_2829_; 
v___x_2814_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_2812_);
v_fst_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_fst_2815_);
v_snd_2816_ = lean_ctor_get(v___x_2814_, 1);
lean_inc(v_snd_2816_);
lean_dec_ref(v___x_2814_);
v___x_2817_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_x27_2813_);
v_fst_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_fst_2818_);
v_snd_2819_ = lean_ctor_get(v___x_2817_, 1);
lean_inc(v_snd_2819_);
lean_dec_ref(v___x_2817_);
v_diff_2820_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(v_fst_2815_, v_fst_2818_);
v___x_2821_ = lean_unsigned_to_nat(0u);
v___x_2822_ = lean_array_get_size(v_diff_2820_);
v___x_2823_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__2));
v___x_2824_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v___x_2822_, v_diff_2820_, v_snd_2819_, v_snd_2816_, v___x_2821_, v___x_2823_);
lean_dec(v_snd_2816_);
lean_dec(v_snd_2819_);
lean_dec_ref(v_diff_2820_);
v_fst_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_fst_2825_);
lean_dec_ref(v___x_2824_);
v___x_2826_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_fst_2825_);
lean_dec(v_fst_2825_);
v_sz_2827_ = lean_array_size(v___x_2826_);
v___x_2828_ = ((size_t)0ULL);
v___x_2829_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_2827_, v___x_2828_, v___x_2826_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___boxed(lean_object* v_s_2830_, lean_object* v_s_x27_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_2830_, v_s_x27_2831_);
lean_dec_ref(v_s_x27_2831_);
lean_dec_ref(v_s_2830_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(lean_object* v_upperBound_2833_, lean_object* v_diff_2834_, lean_object* v_snd_2835_, lean_object* v_snd_2836_, lean_object* v_inst_2837_, lean_object* v_R_2838_, lean_object* v_a_2839_, lean_object* v_b_2840_, lean_object* v_c_2841_){
_start:
{
lean_object* v___x_2842_; 
v___x_2842_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2833_, v_diff_2834_, v_snd_2835_, v_snd_2836_, v_a_2839_, v_b_2840_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___boxed(lean_object* v_upperBound_2843_, lean_object* v_diff_2844_, lean_object* v_snd_2845_, lean_object* v_snd_2846_, lean_object* v_inst_2847_, lean_object* v_R_2848_, lean_object* v_a_2849_, lean_object* v_b_2850_, lean_object* v_c_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(v_upperBound_2843_, v_diff_2844_, v_snd_2845_, v_snd_2846_, v_inst_2847_, v_R_2848_, v_a_2849_, v_b_2850_, v_c_2851_);
lean_dec_ref(v_snd_2846_);
lean_dec_ref(v_snd_2845_);
lean_dec_ref(v_diff_2844_);
lean_dec(v_upperBound_2843_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(lean_object* v___x_2853_, lean_object* v_original_2854_, lean_object* v_a_2855_, lean_object* v_inst_2856_, lean_object* v_a_2857_){
_start:
{
lean_object* v___x_2858_; 
v___x_2858_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2853_, v_original_2854_, v_a_2855_, v_a_2857_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___boxed(lean_object* v___x_2859_, lean_object* v_original_2860_, lean_object* v_a_2861_, lean_object* v_inst_2862_, lean_object* v_a_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v___x_2859_, v_original_2860_, v_a_2861_, v_inst_2862_, v_a_2863_);
lean_dec_ref(v_a_2861_);
lean_dec_ref(v_original_2860_);
lean_dec(v___x_2859_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(lean_object* v___x_2865_, lean_object* v_edited_2866_, lean_object* v_a_2867_, lean_object* v_inst_2868_, lean_object* v_a_2869_){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2865_, v_edited_2866_, v_a_2867_, v_a_2869_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___boxed(lean_object* v___x_2871_, lean_object* v_edited_2872_, lean_object* v_a_2873_, lean_object* v_inst_2874_, lean_object* v_a_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(v___x_2871_, v_edited_2872_, v_a_2873_, v_inst_2874_, v_a_2875_);
lean_dec_ref(v_a_2873_);
lean_dec_ref(v_edited_2872_);
lean_dec(v___x_2871_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(lean_object* v___x_2877_, lean_object* v_original_2878_, lean_object* v_inst_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v___x_2881_; 
v___x_2881_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2877_, v_original_2878_, v_a_2880_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___boxed(lean_object* v___x_2882_, lean_object* v_original_2883_, lean_object* v_inst_2884_, lean_object* v_a_2885_){
_start:
{
lean_object* v_res_2886_; 
v_res_2886_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(v___x_2882_, v_original_2883_, v_inst_2884_, v_a_2885_);
lean_dec_ref(v_original_2883_);
lean_dec(v___x_2882_);
return v_res_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(lean_object* v___x_2887_, lean_object* v_edited_2888_, lean_object* v_inst_2889_, lean_object* v_a_2890_){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2887_, v_edited_2888_, v_a_2890_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___boxed(lean_object* v___x_2892_, lean_object* v_edited_2893_, lean_object* v_inst_2894_, lean_object* v_a_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(v___x_2892_, v_edited_2893_, v_inst_2894_, v_a_2895_);
lean_dec_ref(v_edited_2893_);
lean_dec(v___x_2892_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6(lean_object* v_as_2897_, lean_object* v_as_x27_2898_, lean_object* v_b_2899_, lean_object* v_a_2900_){
_start:
{
lean_object* v___x_2901_; 
v___x_2901_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(v_as_x27_2898_, v_b_2899_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___boxed(lean_object* v_as_2902_, lean_object* v_as_x27_2903_, lean_object* v_b_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6(v_as_2902_, v_as_x27_2903_, v_b_2904_, v_a_2905_);
lean_dec(v_as_x27_2903_);
lean_dec(v_as_2902_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9(lean_object* v_lsize_2907_, lean_object* v_rsize_2908_, lean_object* v_histogram_2909_, lean_object* v_index_2910_, lean_object* v_val_2911_){
_start:
{
lean_object* v___x_2912_; 
v___x_2912_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___redArg(v_histogram_2909_, v_index_2910_, v_val_2911_);
return v___x_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___boxed(lean_object* v_lsize_2913_, lean_object* v_rsize_2914_, lean_object* v_histogram_2915_, lean_object* v_index_2916_, lean_object* v_val_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9(v_lsize_2913_, v_rsize_2914_, v_histogram_2915_, v_index_2916_, v_val_2917_);
lean_dec(v_rsize_2914_);
lean_dec(v_lsize_2913_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10(lean_object* v_upperBound_2919_, lean_object* v___x_2920_, lean_object* v_fst_2921_, lean_object* v___x_2922_, lean_object* v_inst_2923_, lean_object* v_R_2924_, lean_object* v_a_2925_, lean_object* v_b_2926_, lean_object* v_c_2927_){
_start:
{
lean_object* v___x_2928_; 
v___x_2928_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(v_upperBound_2919_, v___x_2920_, v_fst_2921_, v___x_2922_, v_a_2925_, v_b_2926_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___boxed(lean_object* v_upperBound_2929_, lean_object* v___x_2930_, lean_object* v_fst_2931_, lean_object* v___x_2932_, lean_object* v_inst_2933_, lean_object* v_R_2934_, lean_object* v_a_2935_, lean_object* v_b_2936_, lean_object* v_c_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10(v_upperBound_2929_, v___x_2930_, v_fst_2931_, v___x_2932_, v_inst_2933_, v_R_2934_, v_a_2935_, v_b_2936_, v_c_2937_);
lean_dec(v___x_2932_);
lean_dec_ref(v_fst_2931_);
lean_dec(v___x_2930_);
lean_dec(v_upperBound_2929_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11(lean_object* v_lsize_2939_, lean_object* v_rsize_2940_, lean_object* v_histogram_2941_, lean_object* v_index_2942_, lean_object* v_val_2943_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___redArg(v_histogram_2941_, v_index_2942_, v_val_2943_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___boxed(lean_object* v_lsize_2945_, lean_object* v_rsize_2946_, lean_object* v_histogram_2947_, lean_object* v_index_2948_, lean_object* v_val_2949_){
_start:
{
lean_object* v_res_2950_; 
v_res_2950_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11(v_lsize_2945_, v_rsize_2946_, v_histogram_2947_, v_index_2948_, v_val_2949_);
lean_dec(v_rsize_2946_);
lean_dec(v_lsize_2945_);
return v_res_2950_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12(lean_object* v_upperBound_2951_, lean_object* v_fst_2952_, lean_object* v___x_2953_, lean_object* v_fst_2954_, lean_object* v_inst_2955_, lean_object* v_R_2956_, lean_object* v_a_2957_, lean_object* v_b_2958_, lean_object* v_c_2959_){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(v_upperBound_2951_, v_fst_2952_, v___x_2953_, v_fst_2954_, v_a_2957_, v_b_2958_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___boxed(lean_object* v_upperBound_2961_, lean_object* v_fst_2962_, lean_object* v___x_2963_, lean_object* v_fst_2964_, lean_object* v_inst_2965_, lean_object* v_R_2966_, lean_object* v_a_2967_, lean_object* v_b_2968_, lean_object* v_c_2969_){
_start:
{
lean_object* v_res_2970_; 
v_res_2970_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12(v_upperBound_2961_, v_fst_2962_, v___x_2963_, v_fst_2964_, v_inst_2965_, v_R_2966_, v_a_2967_, v_b_2968_, v_c_2969_);
lean_dec_ref(v_fst_2964_);
lean_dec(v___x_2963_);
lean_dec_ref(v_fst_2962_);
lean_dec(v_upperBound_2961_);
return v_res_2970_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13(lean_object* v_00_u03b2_2971_, lean_object* v_m_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v___x_2974_; 
v___x_2974_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_m_2972_, v_a_2973_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___boxed(lean_object* v_00_u03b2_2975_, lean_object* v_m_2976_, lean_object* v_a_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13(v_00_u03b2_2975_, v_m_2976_, v_a_2977_);
lean_dec_ref(v_a_2977_);
lean_dec_ref(v_m_2976_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_2979_, lean_object* v_m_2980_, lean_object* v_a_2981_, lean_object* v_b_2982_){
_start:
{
lean_object* v___x_2983_; 
v___x_2983_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_m_2980_, v_a_2981_, v_b_2982_);
return v___x_2983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14(lean_object* v_inst_2984_, lean_object* v_R_2985_, lean_object* v_a_2986_, lean_object* v_b_2987_){
_start:
{
lean_object* v___x_2988_; 
v___x_2988_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(v_a_2986_, v_b_2987_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20(lean_object* v_00_u03b2_2989_, lean_object* v_a_2990_, lean_object* v_x_2991_){
_start:
{
lean_object* v___x_2992_; 
v___x_2992_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(v_a_2990_, v_x_2991_);
return v___x_2992_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___boxed(lean_object* v_00_u03b2_2993_, lean_object* v_a_2994_, lean_object* v_x_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20(v_00_u03b2_2993_, v_a_2994_, v_x_2995_);
lean_dec(v_x_2995_);
lean_dec_ref(v_a_2994_);
return v_res_2996_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22(lean_object* v_00_u03b2_2997_, lean_object* v_a_2998_, lean_object* v_x_2999_){
_start:
{
uint8_t v___x_3000_; 
v___x_3000_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(v_a_2998_, v_x_2999_);
return v___x_3000_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___boxed(lean_object* v_00_u03b2_3001_, lean_object* v_a_3002_, lean_object* v_x_3003_){
_start:
{
uint8_t v_res_3004_; lean_object* v_r_3005_; 
v_res_3004_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22(v_00_u03b2_3001_, v_a_3002_, v_x_3003_);
lean_dec(v_x_3003_);
lean_dec_ref(v_a_3002_);
v_r_3005_ = lean_box(v_res_3004_);
return v_r_3005_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23(lean_object* v_00_u03b2_3006_, lean_object* v_data_3007_){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23___redArg(v_data_3007_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24(lean_object* v_00_u03b2_3009_, lean_object* v_a_3010_, lean_object* v_b_3011_, lean_object* v_x_3012_){
_start:
{
lean_object* v___x_3013_; 
v___x_3013_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(v_a_3010_, v_b_3011_, v_x_3012_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28(lean_object* v_00_u03b2_3014_, lean_object* v_i_3015_, lean_object* v_source_3016_, lean_object* v_target_3017_){
_start:
{
lean_object* v___x_3018_; 
v___x_3018_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28___redArg(v_i_3015_, v_source_3016_, v_target_3017_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_3019_, lean_object* v_x_3020_, lean_object* v_x_3021_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29___redArg(v_x_3020_, v_x_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(lean_object* v_s_3023_){
_start:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3024_ = lean_string_data(v_s_3023_);
v___x_3025_ = lean_array_mk(v___x_3024_);
return v___x_3025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(lean_object* v_s_3026_, lean_object* v_s_x27_3027_){
_start:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3028_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3026_);
v___x_3029_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3027_);
v___x_3030_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3028_, v___x_3029_);
v___x_3031_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_3030_);
lean_dec_ref(v___x_3030_);
return v___x_3031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(lean_object* v_s_3032_, lean_object* v_s_x27_3033_){
_start:
{
uint8_t v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; uint8_t v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3034_ = 1;
v___x_3035_ = lean_box(v___x_3034_);
v___x_3036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
lean_ctor_set(v___x_3036_, 1, v_s_3032_);
v___x_3037_ = 0;
v___x_3038_ = lean_box(v___x_3037_);
v___x_3039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3038_);
lean_ctor_set(v___x_3039_, 1, v_s_x27_3033_);
v___x_3040_ = lean_unsigned_to_nat(2u);
v___x_3041_ = lean_mk_empty_array_with_capacity(v___x_3040_);
v___x_3042_ = lean_array_push(v___x_3041_, v___x_3036_);
v___x_3043_ = lean_array_push(v___x_3042_, v___x_3039_);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(lean_object* v_as_3044_, size_t v_i_3045_, size_t v_stop_3046_, lean_object* v_b_3047_){
_start:
{
lean_object* v___y_3049_; uint8_t v___x_3053_; 
v___x_3053_ = lean_usize_dec_eq(v_i_3045_, v_stop_3046_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; lean_object* v_fst_3055_; uint8_t v___x_3056_; uint8_t v___x_3057_; uint8_t v___x_3058_; 
v___x_3054_ = lean_array_uget_borrowed(v_as_3044_, v_i_3045_);
v_fst_3055_ = lean_ctor_get(v___x_3054_, 0);
v___x_3056_ = 2;
v___x_3057_ = lean_unbox(v_fst_3055_);
v___x_3058_ = l_Lean_Diff_instBEqAction_beq(v___x_3057_, v___x_3056_);
if (v___x_3058_ == 0)
{
lean_object* v___x_3059_; 
lean_inc(v___x_3054_);
v___x_3059_ = lean_array_push(v_b_3047_, v___x_3054_);
v___y_3049_ = v___x_3059_;
goto v___jp_3048_;
}
else
{
v___y_3049_ = v_b_3047_;
goto v___jp_3048_;
}
}
else
{
return v_b_3047_;
}
v___jp_3048_:
{
size_t v___x_3050_; size_t v___x_3051_; 
v___x_3050_ = ((size_t)1ULL);
v___x_3051_ = lean_usize_add(v_i_3045_, v___x_3050_);
v_i_3045_ = v___x_3051_;
v_b_3047_ = v___y_3049_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0___boxed(lean_object* v_as_3060_, lean_object* v_i_3061_, lean_object* v_stop_3062_, lean_object* v_b_3063_){
_start:
{
size_t v_i_boxed_3064_; size_t v_stop_boxed_3065_; lean_object* v_res_3066_; 
v_i_boxed_3064_ = lean_unbox_usize(v_i_3061_);
lean_dec(v_i_3061_);
v_stop_boxed_3065_ = lean_unbox_usize(v_stop_3062_);
lean_dec(v_stop_3062_);
v_res_3066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_as_3060_, v_i_boxed_3064_, v_stop_boxed_3065_, v_b_3063_);
lean_dec_ref(v_as_3060_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff(lean_object* v_s_3067_, lean_object* v_s_x27_3068_, uint8_t v_granularity_3069_){
_start:
{
lean_object* v___y_3071_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3090_; lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; 
switch(v_granularity_3069_)
{
case 0:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___y_3113_; uint8_t v___x_3119_; 
v___x_3110_ = lean_string_length(v_s_3067_);
v___x_3111_ = lean_string_length(v_s_x27_3068_);
v___x_3119_ = lean_nat_dec_le(v___x_3110_, v___x_3111_);
if (v___x_3119_ == 0)
{
v___y_3113_ = v___x_3111_;
goto v___jp_3112_;
}
else
{
v___y_3113_ = v___x_3110_;
goto v___jp_3112_;
}
v___jp_3112_:
{
lean_object* v___x_3114_; lean_object* v_maxCharDiffDistance_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; uint8_t v___x_3118_; 
v___x_3114_ = lean_unsigned_to_nat(5u);
v_maxCharDiffDistance_3115_ = lean_nat_div(v___y_3113_, v___x_3114_);
v___x_3116_ = lean_unsigned_to_nat(1u);
v___x_3117_ = lean_nat_shiftr(v___y_3113_, v___x_3116_);
lean_dec(v___y_3113_);
v___x_3118_ = lean_nat_dec_le(v___x_3110_, v___x_3111_);
if (v___x_3118_ == 0)
{
v___y_3090_ = v___x_3117_;
v___y_3091_ = v___x_3116_;
v___y_3092_ = v_maxCharDiffDistance_3115_;
v___y_3093_ = v___x_3110_;
goto v___jp_3089_;
}
else
{
v___y_3090_ = v___x_3117_;
v___y_3091_ = v___x_3116_;
v___y_3092_ = v_maxCharDiffDistance_3115_;
v___y_3093_ = v___x_3111_;
goto v___jp_3089_;
}
}
}
case 1:
{
lean_object* v___x_3120_; 
v___x_3120_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(v_s_3067_, v_s_x27_3068_);
return v___x_3120_;
}
case 2:
{
lean_object* v___x_3121_; 
v___x_3121_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3067_, v_s_x27_3068_);
lean_dec_ref(v_s_x27_3068_);
lean_dec_ref(v_s_3067_);
return v___x_3121_;
}
case 3:
{
lean_object* v___x_3122_; 
v___x_3122_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3067_, v_s_x27_3068_);
return v___x_3122_;
}
default: 
{
uint8_t v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
lean_dec_ref(v_s_3067_);
v___x_3123_ = 0;
v___x_3124_ = lean_box(v___x_3123_);
v___x_3125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3124_);
lean_ctor_set(v___x_3125_, 1, v_s_x27_3068_);
v___x_3126_ = lean_unsigned_to_nat(1u);
v___x_3127_ = lean_mk_empty_array_with_capacity(v___x_3126_);
v___x_3128_ = lean_array_push(v___x_3127_, v___x_3125_);
return v___x_3128_;
}
}
v___jp_3070_:
{
size_t v_sz_3072_; size_t v___x_3073_; lean_object* v___x_3074_; 
v_sz_3072_ = lean_array_size(v___y_3071_);
v___x_3073_ = ((size_t)0ULL);
v___x_3074_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_3072_, v___x_3073_, v___y_3071_);
return v___x_3074_;
}
v___jp_3075_:
{
lean_object* v_charArrDiff_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; uint8_t v___x_3083_; 
v_charArrDiff_3080_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v___y_3077_);
lean_dec_ref(v___y_3077_);
v___x_3081_ = lean_array_get_size(v_charArrDiff_3080_);
v___x_3082_ = lean_unsigned_to_nat(3u);
v___x_3083_ = lean_nat_dec_le(v___x_3081_, v___x_3082_);
if (v___x_3083_ == 0)
{
lean_object* v_approxEditDistance_3084_; uint8_t v___x_3085_; 
v_approxEditDistance_3084_ = lean_array_get_size(v___y_3079_);
lean_dec_ref(v___y_3079_);
v___x_3085_ = lean_nat_dec_le(v_approxEditDistance_3084_, v___y_3078_);
lean_dec(v___y_3078_);
if (v___x_3085_ == 0)
{
uint8_t v___x_3086_; 
lean_dec_ref(v_charArrDiff_3080_);
v___x_3086_ = lean_nat_dec_le(v_approxEditDistance_3084_, v___y_3076_);
lean_dec(v___y_3076_);
if (v___x_3086_ == 0)
{
lean_object* v___x_3087_; 
v___x_3087_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3067_, v_s_x27_3068_);
return v___x_3087_;
}
else
{
lean_object* v___x_3088_; 
v___x_3088_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3067_, v_s_x27_3068_);
lean_dec_ref(v_s_x27_3068_);
lean_dec_ref(v_s_3067_);
return v___x_3088_;
}
}
else
{
lean_dec(v___y_3076_);
lean_dec_ref(v_s_x27_3068_);
lean_dec_ref(v_s_3067_);
v___y_3071_ = v_charArrDiff_3080_;
goto v___jp_3070_;
}
}
else
{
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec(v___y_3076_);
lean_dec_ref(v_s_x27_3068_);
lean_dec_ref(v_s_3067_);
v___y_3071_ = v_charArrDiff_3080_;
goto v___jp_3070_;
}
}
v___jp_3089_:
{
lean_object* v___x_3094_; lean_object* v_maxWordDiffDistance_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v_charDiffRaw_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; uint8_t v___x_3102_; 
v___x_3094_ = lean_nat_shiftr(v___y_3093_, v___y_3091_);
lean_dec(v___y_3093_);
v_maxWordDiffDistance_3095_ = lean_nat_add(v___y_3090_, v___x_3094_);
lean_dec(v___x_3094_);
lean_dec(v___y_3090_);
lean_inc_ref(v_s_3067_);
v___x_3096_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3067_);
lean_inc_ref(v_s_x27_3068_);
v___x_3097_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3068_);
v_charDiffRaw_3098_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3096_, v___x_3097_);
v___x_3099_ = lean_unsigned_to_nat(0u);
v___x_3100_ = lean_array_get_size(v_charDiffRaw_3098_);
v___x_3101_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0));
v___x_3102_ = lean_nat_dec_lt(v___x_3099_, v___x_3100_);
if (v___x_3102_ == 0)
{
v___y_3076_ = v_maxWordDiffDistance_3095_;
v___y_3077_ = v_charDiffRaw_3098_;
v___y_3078_ = v___y_3092_;
v___y_3079_ = v___x_3101_;
goto v___jp_3075_;
}
else
{
uint8_t v___x_3103_; 
v___x_3103_ = lean_nat_dec_le(v___x_3100_, v___x_3100_);
if (v___x_3103_ == 0)
{
if (v___x_3102_ == 0)
{
v___y_3076_ = v_maxWordDiffDistance_3095_;
v___y_3077_ = v_charDiffRaw_3098_;
v___y_3078_ = v___y_3092_;
v___y_3079_ = v___x_3101_;
goto v___jp_3075_;
}
else
{
size_t v___x_3104_; size_t v___x_3105_; lean_object* v___x_3106_; 
v___x_3104_ = ((size_t)0ULL);
v___x_3105_ = lean_usize_of_nat(v___x_3100_);
v___x_3106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3098_, v___x_3104_, v___x_3105_, v___x_3101_);
v___y_3076_ = v_maxWordDiffDistance_3095_;
v___y_3077_ = v_charDiffRaw_3098_;
v___y_3078_ = v___y_3092_;
v___y_3079_ = v___x_3106_;
goto v___jp_3075_;
}
}
else
{
size_t v___x_3107_; size_t v___x_3108_; lean_object* v___x_3109_; 
v___x_3107_ = ((size_t)0ULL);
v___x_3108_ = lean_usize_of_nat(v___x_3100_);
v___x_3109_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3098_, v___x_3107_, v___x_3108_, v___x_3101_);
v___y_3076_ = v_maxWordDiffDistance_3095_;
v___y_3077_ = v_charDiffRaw_3098_;
v___y_3078_ = v___y_3092_;
v___y_3079_ = v___x_3109_;
goto v___jp_3075_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff___boxed(lean_object* v_s_3129_, lean_object* v_s_x27_3130_, lean_object* v_granularity_3131_){
_start:
{
uint8_t v_granularity_boxed_3132_; lean_object* v_res_3133_; 
v_granularity_boxed_3132_ = lean_unbox(v_granularity_3131_);
v_res_3133_ = l_Lean_Meta_Hint_readableDiff(v_s_3129_, v_s_x27_3130_, v_granularity_boxed_3132_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(lean_object* v_as_3134_, size_t v_i_3135_, size_t v_stop_3136_, lean_object* v_b_3137_){
_start:
{
uint8_t v___x_3138_; 
v___x_3138_ = lean_usize_dec_eq(v_i_3135_, v_stop_3136_);
if (v___x_3138_ == 0)
{
lean_object* v___x_3139_; lean_object* v_snd_3140_; lean_object* v___x_3141_; size_t v___x_3142_; size_t v___x_3143_; 
v___x_3139_ = lean_array_uget_borrowed(v_as_3134_, v_i_3135_);
v_snd_3140_ = lean_ctor_get(v___x_3139_, 1);
v___x_3141_ = lean_string_append(v_b_3137_, v_snd_3140_);
v___x_3142_ = ((size_t)1ULL);
v___x_3143_ = lean_usize_add(v_i_3135_, v___x_3142_);
v_i_3135_ = v___x_3143_;
v_b_3137_ = v___x_3141_;
goto _start;
}
else
{
return v_b_3137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0___boxed(lean_object* v_as_3145_, lean_object* v_i_3146_, lean_object* v_stop_3147_, lean_object* v_b_3148_){
_start:
{
size_t v_i_boxed_3149_; size_t v_stop_boxed_3150_; lean_object* v_res_3151_; 
v_i_boxed_3149_ = lean_unbox_usize(v_i_3146_);
lean_dec(v_i_3146_);
v_stop_boxed_3150_ = lean_unbox_usize(v_stop_3147_);
lean_dec(v_stop_3147_);
v_res_3151_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v_as_3145_, v_i_boxed_3149_, v_stop_boxed_3150_, v_b_3148_);
lean_dec_ref(v_as_3145_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(lean_object* v_t_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v___x_3155_; lean_object* v_infoState_3156_; uint8_t v_enabled_3157_; 
v___x_3155_ = lean_st_ref_get(v___y_3153_);
v_infoState_3156_ = lean_ctor_get(v___x_3155_, 7);
lean_inc_ref(v_infoState_3156_);
lean_dec(v___x_3155_);
v_enabled_3157_ = lean_ctor_get_uint8(v_infoState_3156_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3156_);
if (v_enabled_3157_ == 0)
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
lean_dec_ref(v_t_3152_);
v___x_3158_ = lean_box(0);
v___x_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3158_);
return v___x_3159_;
}
else
{
lean_object* v___x_3160_; lean_object* v_infoState_3161_; lean_object* v_env_3162_; lean_object* v_nextMacroScope_3163_; lean_object* v_ngen_3164_; lean_object* v_auxDeclNGen_3165_; lean_object* v_traceState_3166_; lean_object* v_cache_3167_; lean_object* v_messages_3168_; lean_object* v_snapshotTasks_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3191_; 
v___x_3160_ = lean_st_ref_take(v___y_3153_);
v_infoState_3161_ = lean_ctor_get(v___x_3160_, 7);
v_env_3162_ = lean_ctor_get(v___x_3160_, 0);
v_nextMacroScope_3163_ = lean_ctor_get(v___x_3160_, 1);
v_ngen_3164_ = lean_ctor_get(v___x_3160_, 2);
v_auxDeclNGen_3165_ = lean_ctor_get(v___x_3160_, 3);
v_traceState_3166_ = lean_ctor_get(v___x_3160_, 4);
v_cache_3167_ = lean_ctor_get(v___x_3160_, 5);
v_messages_3168_ = lean_ctor_get(v___x_3160_, 6);
v_snapshotTasks_3169_ = lean_ctor_get(v___x_3160_, 8);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3171_ = v___x_3160_;
v_isShared_3172_ = v_isSharedCheck_3191_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_snapshotTasks_3169_);
lean_inc(v_infoState_3161_);
lean_inc(v_messages_3168_);
lean_inc(v_cache_3167_);
lean_inc(v_traceState_3166_);
lean_inc(v_auxDeclNGen_3165_);
lean_inc(v_ngen_3164_);
lean_inc(v_nextMacroScope_3163_);
lean_inc(v_env_3162_);
lean_dec(v___x_3160_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3191_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
uint8_t v_enabled_3173_; lean_object* v_assignment_3174_; lean_object* v_lazyAssignment_3175_; lean_object* v_trees_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3190_; 
v_enabled_3173_ = lean_ctor_get_uint8(v_infoState_3161_, sizeof(void*)*3);
v_assignment_3174_ = lean_ctor_get(v_infoState_3161_, 0);
v_lazyAssignment_3175_ = lean_ctor_get(v_infoState_3161_, 1);
v_trees_3176_ = lean_ctor_get(v_infoState_3161_, 2);
v_isSharedCheck_3190_ = !lean_is_exclusive(v_infoState_3161_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3178_ = v_infoState_3161_;
v_isShared_3179_ = v_isSharedCheck_3190_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_trees_3176_);
lean_inc(v_lazyAssignment_3175_);
lean_inc(v_assignment_3174_);
lean_dec(v_infoState_3161_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3190_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3183_; 
v___x_3180_ = lean_box(0);
v___x_3181_ = l_Lean_PersistentArray_push___redArg(v_trees_3176_, v_t_3152_);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 2, v___x_3181_);
v___x_3183_ = v___x_3178_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3189_; 
v_reuseFailAlloc_3189_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3189_, 0, v_assignment_3174_);
lean_ctor_set(v_reuseFailAlloc_3189_, 1, v_lazyAssignment_3175_);
lean_ctor_set(v_reuseFailAlloc_3189_, 2, v___x_3181_);
lean_ctor_set_uint8(v_reuseFailAlloc_3189_, sizeof(void*)*3, v_enabled_3173_);
v___x_3183_ = v_reuseFailAlloc_3189_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
lean_object* v___x_3185_; 
if (v_isShared_3172_ == 0)
{
lean_ctor_set(v___x_3171_, 7, v___x_3183_);
v___x_3185_ = v___x_3171_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_env_3162_);
lean_ctor_set(v_reuseFailAlloc_3188_, 1, v_nextMacroScope_3163_);
lean_ctor_set(v_reuseFailAlloc_3188_, 2, v_ngen_3164_);
lean_ctor_set(v_reuseFailAlloc_3188_, 3, v_auxDeclNGen_3165_);
lean_ctor_set(v_reuseFailAlloc_3188_, 4, v_traceState_3166_);
lean_ctor_set(v_reuseFailAlloc_3188_, 5, v_cache_3167_);
lean_ctor_set(v_reuseFailAlloc_3188_, 6, v_messages_3168_);
lean_ctor_set(v_reuseFailAlloc_3188_, 7, v___x_3183_);
lean_ctor_set(v_reuseFailAlloc_3188_, 8, v_snapshotTasks_3169_);
v___x_3185_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = lean_st_ref_put(v___y_3153_, v___x_3185_);
v___x_3187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3180_);
return v___x_3187_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg___boxed(lean_object* v_t_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3192_, v___y_3193_);
lean_dec(v___y_3193_);
return v_res_3195_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; 
v___x_3196_ = lean_unsigned_to_nat(32u);
v___x_3197_ = lean_mk_empty_array_with_capacity(v___x_3196_);
v___x_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3197_);
return v___x_3198_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1(void){
_start:
{
size_t v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3199_ = ((size_t)5ULL);
v___x_3200_ = lean_unsigned_to_nat(0u);
v___x_3201_ = lean_unsigned_to_nat(32u);
v___x_3202_ = lean_mk_empty_array_with_capacity(v___x_3201_);
v___x_3203_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0);
v___x_3204_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
lean_ctor_set(v___x_3204_, 1, v___x_3202_);
lean_ctor_set(v___x_3204_, 2, v___x_3200_);
lean_ctor_set(v___x_3204_, 3, v___x_3200_);
lean_ctor_set_usize(v___x_3204_, 4, v___x_3199_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(lean_object* v_t_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_){
_start:
{
lean_object* v___x_3209_; lean_object* v_infoState_3210_; uint8_t v_enabled_3211_; 
v___x_3209_ = lean_st_ref_get(v___y_3207_);
v_infoState_3210_ = lean_ctor_get(v___x_3209_, 7);
lean_inc_ref(v_infoState_3210_);
lean_dec(v___x_3209_);
v_enabled_3211_ = lean_ctor_get_uint8(v_infoState_3210_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3210_);
if (v_enabled_3211_ == 0)
{
lean_object* v___x_3212_; lean_object* v___x_3213_; 
lean_dec_ref(v_t_3205_);
v___x_3212_ = lean_box(0);
v___x_3213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3212_);
return v___x_3213_;
}
else
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3214_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1);
v___x_3215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3215_, 0, v_t_3205_);
lean_ctor_set(v___x_3215_, 1, v___x_3214_);
v___x_3216_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v___x_3215_, v___y_3207_);
return v___x_3216_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___boxed(lean_object* v_t_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v_t_3217_, v___y_3218_, v___y_3219_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
return v_res_3221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0(lean_object* v___x_3222_, lean_object* v___y_3223_){
_start:
{
lean_object* v___x_3224_; 
v___x_3224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3222_);
lean_ctor_set(v___x_3224_, 1, v___y_3223_);
return v___x_3224_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__0));
v___x_3227_ = l_Lean_stringToMessageData(v___x_3226_);
return v___x_3227_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3229_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__2));
v___x_3230_ = l_Lean_stringToMessageData(v___x_3229_);
return v___x_3230_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29(void){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__28));
v___x_3280_ = l_Lean_Json_mkObj(v___x_3279_);
return v___x_3280_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30(void){
_start:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3281_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29);
v___x_3282_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__19));
v___x_3283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3282_);
lean_ctor_set(v___x_3283_, 1, v___x_3281_);
return v___x_3283_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31(void){
_start:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3284_ = lean_box(0);
v___x_3285_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30);
v___x_3286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3285_);
lean_ctor_set(v___x_3286_, 1, v___x_3284_);
return v___x_3286_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33(void){
_start:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__32));
v___x_3290_ = l_Lean_MessageData_ofFormat(v___x_3289_);
return v___x_3290_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35(void){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3292_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__34));
v___x_3293_ = l_Lean_stringToMessageData(v___x_3292_);
return v___x_3293_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(lean_object* v_suggestions_3295_, uint8_t v_forceList_3296_, lean_object* v_codeActionPrefix_x3f_3297_, lean_object* v_ref_3298_, lean_object* v_as_3299_, size_t v_sz_3300_, size_t v_i_3301_, lean_object* v_b_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
lean_object* v_a_3307_; lean_object* v___y_3312_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3323_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3333_; lean_object* v___y_3334_; uint8_t v___x_3351_; 
v___x_3351_ = lean_usize_dec_lt(v_i_3301_, v_sz_3300_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3352_; 
lean_dec(v_ref_3298_);
lean_dec(v_codeActionPrefix_x3f_3297_);
v___x_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3352_, 0, v_b_3302_);
return v___x_3352_;
}
else
{
lean_object* v_a_3353_; lean_object* v_span_x3f_3354_; lean_object* v___x_3355_; lean_object* v___y_3357_; uint8_t v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3390_; uint8_t v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v___y_3396_; lean_object* v___y_3397_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v___y_3442_; uint8_t v___y_3443_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; uint8_t v___y_3450_; uint8_t v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; uint8_t v___y_3460_; uint8_t v___y_3461_; lean_object* v___y_3462_; lean_object* v_postInfo_x3f_3463_; lean_object* v___y_3464_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; uint8_t v___y_3470_; uint8_t v___y_3471_; lean_object* v___y_3472_; lean_object* v_edits_3473_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v_stop_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; uint8_t v___y_3485_; uint8_t v___y_3486_; lean_object* v___y_3487_; lean_object* v_edits_3488_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; uint8_t v___y_3504_; uint8_t v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v_edits_3508_; lean_object* v___y_3509_; lean_object* v___x_3535_; lean_object* v___y_3537_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; uint8_t v___y_3543_; uint8_t v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3546_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3585_; lean_object* v___y_3586_; lean_object* v___y_3587_; uint8_t v___y_3588_; uint8_t v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; lean_object* v___y_3601_; 
v_a_3353_ = lean_array_uget_borrowed(v_as_3299_, v_i_3301_);
v_span_x3f_3354_ = lean_ctor_get(v_a_3353_, 1);
v___x_3355_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_3535_ = l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_;
if (lean_obj_tag(v_span_x3f_3354_) == 0)
{
lean_inc(v_ref_3298_);
v___y_3601_ = v_ref_3298_;
goto v___jp_3600_;
}
else
{
lean_object* v_val_3622_; 
v_val_3622_ = lean_ctor_get(v_span_x3f_3354_, 0);
lean_inc(v_val_3622_);
v___y_3601_ = v_val_3622_;
goto v___jp_3600_;
}
v___jp_3356_:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___f_3377_; 
lean_inc_ref(v___y_3357_);
v___x_3363_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson(v___y_3357_);
v___x_3364_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__9));
v___x_3365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3364_);
lean_ctor_set(v___x_3365_, 1, v___x_3363_);
v___x_3366_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3367_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3367_, 0, v___y_3359_);
v___x_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3366_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
v___x_3369_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3370_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3360_);
v___x_3371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3369_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
v___x_3372_ = lean_box(0);
v___x_3373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3371_);
lean_ctor_set(v___x_3373_, 1, v___x_3372_);
v___x_3374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3368_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
v___x_3375_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3365_);
lean_ctor_set(v___x_3375_, 1, v___x_3374_);
v___x_3376_ = l_Lean_Json_mkObj(v___x_3375_);
lean_dec_ref_known(v___x_3375_, 2);
v___f_3377_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3377_, 0, v___x_3376_);
if (v___y_3358_ == 0)
{
lean_object* v___x_3378_; 
v___x_3378_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString(v___y_3357_);
v___y_3331_ = v___f_3377_;
v___y_3332_ = v___y_3361_;
v___y_3333_ = v___y_3362_;
v___y_3334_ = v___x_3378_;
goto v___jp_3330_;
}
else
{
lean_object* v___x_3379_; lean_object* v___x_3380_; uint8_t v___x_3381_; 
v___x_3379_ = lean_unsigned_to_nat(0u);
v___x_3380_ = lean_array_get_size(v___y_3357_);
v___x_3381_ = lean_nat_dec_lt(v___x_3379_, v___x_3380_);
if (v___x_3381_ == 0)
{
lean_dec_ref(v___y_3357_);
v___y_3331_ = v___f_3377_;
v___y_3332_ = v___y_3361_;
v___y_3333_ = v___y_3362_;
v___y_3334_ = v___x_3355_;
goto v___jp_3330_;
}
else
{
uint8_t v___x_3382_; 
v___x_3382_ = lean_nat_dec_le(v___x_3380_, v___x_3380_);
if (v___x_3382_ == 0)
{
if (v___x_3381_ == 0)
{
lean_dec_ref(v___y_3357_);
v___y_3331_ = v___f_3377_;
v___y_3332_ = v___y_3361_;
v___y_3333_ = v___y_3362_;
v___y_3334_ = v___x_3355_;
goto v___jp_3330_;
}
else
{
size_t v___x_3383_; size_t v___x_3384_; lean_object* v___x_3385_; 
v___x_3383_ = ((size_t)0ULL);
v___x_3384_ = lean_usize_of_nat(v___x_3380_);
v___x_3385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3357_, v___x_3383_, v___x_3384_, v___x_3355_);
lean_dec_ref(v___y_3357_);
v___y_3331_ = v___f_3377_;
v___y_3332_ = v___y_3361_;
v___y_3333_ = v___y_3362_;
v___y_3334_ = v___x_3385_;
goto v___jp_3330_;
}
}
else
{
size_t v___x_3386_; size_t v___x_3387_; lean_object* v___x_3388_; 
v___x_3386_ = ((size_t)0ULL);
v___x_3387_ = lean_usize_of_nat(v___x_3380_);
v___x_3388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3357_, v___x_3386_, v___x_3387_, v___x_3355_);
lean_dec_ref(v___y_3357_);
v___y_3331_ = v___f_3377_;
v___y_3332_ = v___y_3361_;
v___y_3333_ = v___y_3362_;
v___y_3334_ = v___x_3388_;
goto v___jp_3330_;
}
}
}
}
v___jp_3389_:
{
if (lean_obj_tag(v___y_3393_) == 0)
{
lean_object* v___x_3398_; uint64_t v_javascriptHash_3399_; lean_object* v_suggestion_3400_; lean_object* v_messageData_x3f_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___f_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; 
lean_dec_ref(v___y_3390_);
v___x_3398_ = l_Lean_Meta_Hint_textInsertionWidget;
v_javascriptHash_3399_ = lean_ctor_get_uint64(v___x_3398_, sizeof(void*)*1);
v_suggestion_3400_ = lean_ctor_get(v___y_3395_, 0);
lean_inc_ref(v_suggestion_3400_);
v_messageData_x3f_3401_ = lean_ctor_get(v___y_3395_, 4);
lean_inc(v_messageData_x3f_3401_);
lean_dec_ref(v___y_3395_);
v___x_3402_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18));
v___x_3403_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3404_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3394_);
v___x_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3403_);
lean_ctor_set(v___x_3405_, 1, v___x_3404_);
v___x_3406_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3407_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3407_, 0, v___y_3392_);
v___x_3408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3406_);
lean_ctor_set(v___x_3408_, 1, v___x_3407_);
v___x_3409_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31);
v___x_3410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3408_);
lean_ctor_set(v___x_3410_, 1, v___x_3409_);
v___x_3411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3405_);
lean_ctor_set(v___x_3411_, 1, v___x_3410_);
v___x_3412_ = l_Lean_Json_mkObj(v___x_3411_);
lean_dec_ref_known(v___x_3411_, 2);
v___f_3413_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3413_, 0, v___x_3412_);
v___x_3414_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3414_, 0, v___x_3402_);
lean_ctor_set(v___x_3414_, 1, v___f_3413_);
lean_ctor_set_uint64(v___x_3414_, sizeof(void*)*2, v_javascriptHash_3399_);
v___x_3415_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33);
v___x_3416_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3414_);
lean_ctor_set(v___x_3416_, 1, v___x_3415_);
v___x_3417_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3417_);
lean_ctor_set(v___x_3418_, 1, v___x_3416_);
v___x_3419_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35);
v___x_3420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3418_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
v___x_3421_ = l_Lean_stringToMessageData(v___y_3397_);
v___x_3422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3422_, 0, v___x_3420_);
lean_ctor_set(v___x_3422_, 1, v___x_3421_);
if (lean_obj_tag(v_messageData_x3f_3401_) == 0)
{
if (lean_obj_tag(v_suggestion_3400_) == 0)
{
lean_object* v_a_3423_; lean_object* v___x_3424_; 
v_a_3423_ = lean_ctor_get(v_suggestion_3400_, 1);
lean_inc(v_a_3423_);
lean_dec_ref_known(v_suggestion_3400_, 2);
v___x_3424_ = l_Lean_MessageData_ofSyntax(v_a_3423_);
v___y_3316_ = v___x_3422_;
v___y_3317_ = v___y_3396_;
v___y_3318_ = v___x_3424_;
goto v___jp_3315_;
}
else
{
lean_object* v_a_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3433_; 
v_a_3425_ = lean_ctor_get(v_suggestion_3400_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v_suggestion_3400_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3427_ = v_suggestion_3400_;
v_isShared_3428_ = v_isSharedCheck_3433_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_a_3425_);
lean_dec(v_suggestion_3400_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3433_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3430_; 
if (v_isShared_3428_ == 0)
{
lean_ctor_set_tag(v___x_3427_, 3);
v___x_3430_ = v___x_3427_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3425_);
v___x_3430_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
lean_object* v___x_3431_; 
v___x_3431_ = l_Lean_MessageData_ofFormat(v___x_3430_);
v___y_3316_ = v___x_3422_;
v___y_3317_ = v___y_3396_;
v___y_3318_ = v___x_3431_;
goto v___jp_3315_;
}
}
}
}
else
{
lean_object* v_val_3434_; 
lean_dec_ref(v_suggestion_3400_);
v_val_3434_ = lean_ctor_get(v_messageData_x3f_3401_, 0);
lean_inc(v_val_3434_);
lean_dec_ref_known(v_messageData_x3f_3401_, 1);
v___y_3316_ = v___x_3422_;
v___y_3317_ = v___y_3396_;
v___y_3318_ = v_val_3434_;
goto v___jp_3315_;
}
}
else
{
lean_dec_ref_known(v___y_3393_, 1);
lean_dec_ref(v___y_3395_);
v___y_3357_ = v___y_3390_;
v___y_3358_ = v___y_3391_;
v___y_3359_ = v___y_3392_;
v___y_3360_ = v___y_3394_;
v___y_3361_ = v___y_3397_;
v___y_3362_ = v___y_3396_;
goto v___jp_3356_;
}
}
v___jp_3435_:
{
if (v___y_3443_ == 0)
{
lean_object* v_messageData_x3f_3444_; 
v_messageData_x3f_3444_ = lean_ctor_get(v___y_3440_, 4);
if (lean_obj_tag(v_messageData_x3f_3444_) == 0)
{
lean_dec_ref(v___y_3440_);
lean_dec(v___y_3438_);
v___y_3357_ = v___y_3436_;
v___y_3358_ = v___y_3443_;
v___y_3359_ = v___y_3437_;
v___y_3360_ = v___y_3439_;
v___y_3361_ = v___y_3442_;
v___y_3362_ = v___y_3441_;
goto v___jp_3356_;
}
else
{
v___y_3390_ = v___y_3436_;
v___y_3391_ = v___y_3443_;
v___y_3392_ = v___y_3437_;
v___y_3393_ = v___y_3438_;
v___y_3394_ = v___y_3439_;
v___y_3395_ = v___y_3440_;
v___y_3396_ = v___y_3441_;
v___y_3397_ = v___y_3442_;
goto v___jp_3389_;
}
}
else
{
v___y_3390_ = v___y_3436_;
v___y_3391_ = v___y_3443_;
v___y_3392_ = v___y_3437_;
v___y_3393_ = v___y_3438_;
v___y_3394_ = v___y_3439_;
v___y_3395_ = v___y_3440_;
v___y_3396_ = v___y_3441_;
v___y_3397_ = v___y_3442_;
goto v___jp_3389_;
}
}
v___jp_3445_:
{
if (v___y_3451_ == 4)
{
v___y_3436_ = v___y_3446_;
v___y_3437_ = v___y_3447_;
v___y_3438_ = v___y_3448_;
v___y_3439_ = v___y_3449_;
v___y_3440_ = v___y_3452_;
v___y_3441_ = v___y_3454_;
v___y_3442_ = v___y_3453_;
v___y_3443_ = v___x_3351_;
goto v___jp_3435_;
}
else
{
v___y_3436_ = v___y_3446_;
v___y_3437_ = v___y_3447_;
v___y_3438_ = v___y_3448_;
v___y_3439_ = v___y_3449_;
v___y_3440_ = v___y_3452_;
v___y_3441_ = v___y_3454_;
v___y_3442_ = v___y_3453_;
v___y_3443_ = v___y_3450_;
goto v___jp_3435_;
}
}
v___jp_3455_:
{
if (lean_obj_tag(v_postInfo_x3f_3463_) == 0)
{
v___y_3446_ = v___y_3456_;
v___y_3447_ = v___y_3457_;
v___y_3448_ = v___y_3458_;
v___y_3449_ = v___y_3459_;
v___y_3450_ = v___y_3461_;
v___y_3451_ = v___y_3460_;
v___y_3452_ = v___y_3462_;
v___y_3453_ = v___y_3464_;
v___y_3454_ = v___x_3355_;
goto v___jp_3445_;
}
else
{
lean_object* v_val_3465_; 
v_val_3465_ = lean_ctor_get(v_postInfo_x3f_3463_, 0);
lean_inc(v_val_3465_);
lean_dec_ref_known(v_postInfo_x3f_3463_, 1);
v___y_3446_ = v___y_3456_;
v___y_3447_ = v___y_3457_;
v___y_3448_ = v___y_3458_;
v___y_3449_ = v___y_3459_;
v___y_3450_ = v___y_3461_;
v___y_3451_ = v___y_3460_;
v___y_3452_ = v___y_3462_;
v___y_3453_ = v___y_3464_;
v___y_3454_ = v_val_3465_;
goto v___jp_3445_;
}
}
v___jp_3466_:
{
lean_object* v_preInfo_x3f_3474_; 
v_preInfo_x3f_3474_ = lean_ctor_get(v___y_3472_, 1);
if (lean_obj_tag(v_preInfo_x3f_3474_) == 0)
{
lean_object* v_postInfo_x3f_3475_; 
v_postInfo_x3f_3475_ = lean_ctor_get(v___y_3472_, 2);
lean_inc(v_postInfo_x3f_3475_);
v___y_3456_ = v_edits_3473_;
v___y_3457_ = v___y_3467_;
v___y_3458_ = v___y_3468_;
v___y_3459_ = v___y_3469_;
v___y_3460_ = v___y_3471_;
v___y_3461_ = v___y_3470_;
v___y_3462_ = v___y_3472_;
v_postInfo_x3f_3463_ = v_postInfo_x3f_3475_;
v___y_3464_ = v___x_3355_;
goto v___jp_3455_;
}
else
{
lean_object* v_postInfo_x3f_3476_; lean_object* v_val_3477_; 
v_postInfo_x3f_3476_ = lean_ctor_get(v___y_3472_, 2);
lean_inc(v_postInfo_x3f_3476_);
v_val_3477_ = lean_ctor_get(v_preInfo_x3f_3474_, 0);
lean_inc(v_val_3477_);
v___y_3456_ = v_edits_3473_;
v___y_3457_ = v___y_3467_;
v___y_3458_ = v___y_3468_;
v___y_3459_ = v___y_3469_;
v___y_3460_ = v___y_3471_;
v___y_3461_ = v___y_3470_;
v___y_3462_ = v___y_3472_;
v_postInfo_x3f_3463_ = v_postInfo_x3f_3476_;
v___y_3464_ = v_val_3477_;
goto v___jp_3455_;
}
}
v___jp_3478_:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; uint8_t v___x_3491_; 
v___x_3489_ = lean_unsigned_to_nat(1u);
v___x_3490_ = lean_nat_add(v___y_3481_, v___x_3489_);
v___x_3491_ = lean_nat_dec_le(v___x_3490_, v_stop_3482_);
lean_dec(v___x_3490_);
if (v___x_3491_ == 0)
{
lean_dec(v_stop_3482_);
lean_dec(v___y_3481_);
v___y_3467_ = v___y_3479_;
v___y_3468_ = v___y_3483_;
v___y_3469_ = v___y_3484_;
v___y_3470_ = v___y_3486_;
v___y_3471_ = v___y_3485_;
v___y_3472_ = v___y_3487_;
v_edits_3473_ = v_edits_3488_;
goto v___jp_3466_;
}
else
{
lean_object* v_source_3492_; uint8_t v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v_source_3492_ = lean_ctor_get(v___y_3480_, 0);
v___x_3493_ = 2;
v___x_3494_ = lean_string_utf8_extract(v_source_3492_, v___y_3481_, v_stop_3482_);
lean_dec(v_stop_3482_);
lean_dec(v___y_3481_);
v___x_3495_ = lean_box(v___x_3493_);
v___x_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3496_, 0, v___x_3495_);
lean_ctor_set(v___x_3496_, 1, v___x_3494_);
v___x_3497_ = lean_array_push(v_edits_3488_, v___x_3496_);
v___y_3467_ = v___y_3479_;
v___y_3468_ = v___y_3483_;
v___y_3469_ = v___y_3484_;
v___y_3470_ = v___y_3486_;
v___y_3471_ = v___y_3485_;
v___y_3472_ = v___y_3487_;
v_edits_3473_ = v___x_3497_;
goto v___jp_3466_;
}
}
v___jp_3498_:
{
if (lean_obj_tag(v___y_3502_) == 0)
{
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
v___y_3467_ = v___y_3499_;
v___y_3468_ = v___y_3502_;
v___y_3469_ = v___y_3503_;
v___y_3470_ = v___y_3505_;
v___y_3471_ = v___y_3504_;
v___y_3472_ = v___y_3506_;
v_edits_3473_ = v_edits_3508_;
goto v___jp_3466_;
}
else
{
lean_object* v_val_3510_; lean_object* v___x_3511_; 
v_val_3510_ = lean_ctor_get(v___y_3502_, 0);
v___x_3511_ = l_Lean_Syntax_getRange_x3f(v_val_3510_, v___y_3505_);
if (lean_obj_tag(v___x_3511_) == 1)
{
lean_object* v_val_3512_; uint8_t v___x_3513_; 
v_val_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_val_3512_);
lean_dec_ref_known(v___x_3511_, 1);
v___x_3513_ = l_Lean_Syntax_Range_includes(v_val_3512_, v___y_3501_, v___y_3505_, v___y_3505_);
lean_dec_ref(v___y_3501_);
if (v___x_3513_ == 0)
{
lean_dec(v_val_3512_);
lean_dec(v___y_3507_);
lean_dec(v___y_3500_);
v___y_3467_ = v___y_3499_;
v___y_3468_ = v___y_3502_;
v___y_3469_ = v___y_3503_;
v___y_3470_ = v___y_3505_;
v___y_3471_ = v___y_3504_;
v___y_3472_ = v___y_3506_;
v_edits_3473_ = v_edits_3508_;
goto v___jp_3466_;
}
else
{
lean_object* v_toCold_3514_; lean_object* v_fileMap_3515_; lean_object* v_start_3516_; lean_object* v_stop_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3534_; 
v_toCold_3514_ = lean_ctor_get(v___y_3509_, 0);
v_fileMap_3515_ = lean_ctor_get(v_toCold_3514_, 1);
v_start_3516_ = lean_ctor_get(v_val_3512_, 0);
v_stop_3517_ = lean_ctor_get(v_val_3512_, 1);
v_isSharedCheck_3534_ = !lean_is_exclusive(v_val_3512_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3519_ = v_val_3512_;
v_isShared_3520_ = v_isSharedCheck_3534_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_stop_3517_);
lean_inc(v_start_3516_);
lean_dec(v_val_3512_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3534_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; uint8_t v___x_3523_; 
v___x_3521_ = lean_unsigned_to_nat(1u);
v___x_3522_ = lean_nat_add(v_start_3516_, v___x_3521_);
v___x_3523_ = lean_nat_dec_le(v___x_3522_, v___y_3507_);
lean_dec(v___x_3522_);
if (v___x_3523_ == 0)
{
lean_del_object(v___x_3519_);
lean_dec(v_start_3516_);
lean_dec(v___y_3507_);
v___y_3479_ = v___y_3499_;
v___y_3480_ = v_fileMap_3515_;
v___y_3481_ = v___y_3500_;
v_stop_3482_ = v_stop_3517_;
v___y_3483_ = v___y_3502_;
v___y_3484_ = v___y_3503_;
v___y_3485_ = v___y_3504_;
v___y_3486_ = v___y_3505_;
v___y_3487_ = v___y_3506_;
v_edits_3488_ = v_edits_3508_;
goto v___jp_3478_;
}
else
{
lean_object* v_source_3524_; uint8_t v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3529_; 
v_source_3524_ = lean_ctor_get(v_fileMap_3515_, 0);
v___x_3525_ = 2;
v___x_3526_ = lean_string_utf8_extract(v_source_3524_, v_start_3516_, v___y_3507_);
lean_dec(v___y_3507_);
lean_dec(v_start_3516_);
v___x_3527_ = lean_box(v___x_3525_);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 1, v___x_3526_);
lean_ctor_set(v___x_3519_, 0, v___x_3527_);
v___x_3529_ = v___x_3519_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3527_);
lean_ctor_set(v_reuseFailAlloc_3533_, 1, v___x_3526_);
v___x_3529_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; 
v___x_3530_ = lean_mk_empty_array_with_capacity(v___x_3521_);
v___x_3531_ = lean_array_push(v___x_3530_, v___x_3529_);
v___x_3532_ = l_Array_append___redArg(v___x_3531_, v_edits_3508_);
lean_dec_ref(v_edits_3508_);
v___y_3479_ = v___y_3499_;
v___y_3480_ = v_fileMap_3515_;
v___y_3481_ = v___y_3500_;
v_stop_3482_ = v_stop_3517_;
v___y_3483_ = v___y_3502_;
v___y_3484_ = v___y_3503_;
v___y_3485_ = v___y_3504_;
v___y_3486_ = v___y_3505_;
v___y_3487_ = v___y_3506_;
v_edits_3488_ = v___x_3532_;
goto v___jp_3478_;
}
}
}
}
}
else
{
lean_dec(v___x_3511_);
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
v___y_3467_ = v___y_3499_;
v___y_3468_ = v___y_3502_;
v___y_3469_ = v___y_3503_;
v___y_3470_ = v___y_3505_;
v___y_3471_ = v___y_3504_;
v___y_3472_ = v___y_3506_;
v_edits_3473_ = v_edits_3508_;
goto v___jp_3466_;
}
}
}
v___jp_3536_:
{
lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; 
lean_inc_ref(v___y_3545_);
v___x_3547_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3547_, 0, v___y_3542_);
lean_ctor_set(v___x_3547_, 1, v___y_3546_);
lean_ctor_set(v___x_3547_, 2, v___y_3545_);
v___x_3548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3535_);
lean_ctor_set(v___x_3548_, 1, v___x_3547_);
v___x_3549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___y_3537_);
lean_ctor_set(v___x_3549_, 1, v___x_3548_);
v___x_3550_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
v___x_3551_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v___x_3550_, v___y_3303_, v___y_3304_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_messageData_x3f_3552_; 
lean_dec_ref_known(v___x_3551_, 1);
v_messageData_x3f_3552_ = lean_ctor_get(v___y_3545_, 4);
if (lean_obj_tag(v_messageData_x3f_3552_) == 1)
{
lean_object* v_start_3553_; lean_object* v_stop_3554_; lean_object* v_val_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; uint8_t v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
v_start_3553_ = lean_ctor_get(v___y_3539_, 0);
lean_inc(v_start_3553_);
v_stop_3554_ = lean_ctor_get(v___y_3539_, 1);
lean_inc(v_stop_3554_);
v_val_3555_ = lean_ctor_get(v_messageData_x3f_3552_, 0);
v___x_3556_ = lean_box(0);
lean_inc(v_val_3555_);
v___x_3557_ = l_Lean_MessageData_format(v_val_3555_, v___x_3556_);
v___x_3558_ = 0;
v___x_3559_ = l_Std_Format_defWidth;
v___x_3560_ = lean_unsigned_to_nat(0u);
v___x_3561_ = l_Std_Format_pretty(v___x_3557_, v___x_3559_, v___x_3560_, v___x_3560_);
v___x_3562_ = lean_box(v___x_3558_);
v___x_3563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3563_, 0, v___x_3562_);
lean_ctor_set(v___x_3563_, 1, v___x_3561_);
v___x_3564_ = lean_unsigned_to_nat(1u);
v___x_3565_ = lean_mk_empty_array_with_capacity(v___x_3564_);
v___x_3566_ = lean_array_push(v___x_3565_, v___x_3563_);
v___y_3499_ = v___y_3538_;
v___y_3500_ = v_stop_3554_;
v___y_3501_ = v___y_3539_;
v___y_3502_ = v___y_3540_;
v___y_3503_ = v___y_3541_;
v___y_3504_ = v___y_3544_;
v___y_3505_ = v___y_3543_;
v___y_3506_ = v___y_3545_;
v___y_3507_ = v_start_3553_;
v_edits_3508_ = v___x_3566_;
v___y_3509_ = v___y_3303_;
goto v___jp_3498_;
}
else
{
lean_object* v_toCold_3567_; lean_object* v_fileMap_3568_; lean_object* v_start_3569_; lean_object* v_stop_3570_; lean_object* v_source_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v_toCold_3567_ = lean_ctor_get(v___y_3303_, 0);
v_fileMap_3568_ = lean_ctor_get(v_toCold_3567_, 1);
v_start_3569_ = lean_ctor_get(v___y_3539_, 0);
lean_inc(v_start_3569_);
v_stop_3570_ = lean_ctor_get(v___y_3539_, 1);
lean_inc(v_stop_3570_);
v_source_3571_ = lean_ctor_get(v_fileMap_3568_, 0);
v___x_3572_ = lean_string_utf8_extract(v_source_3571_, v_start_3569_, v_stop_3570_);
lean_inc_ref(v___y_3538_);
v___x_3573_ = l_Lean_Meta_Hint_readableDiff(v___x_3572_, v___y_3538_, v___y_3544_);
v___y_3499_ = v___y_3538_;
v___y_3500_ = v_stop_3570_;
v___y_3501_ = v___y_3539_;
v___y_3502_ = v___y_3540_;
v___y_3503_ = v___y_3541_;
v___y_3504_ = v___y_3544_;
v___y_3505_ = v___y_3543_;
v___y_3506_ = v___y_3545_;
v___y_3507_ = v_start_3569_;
v_edits_3508_ = v___x_3573_;
v___y_3509_ = v___y_3303_;
goto v___jp_3498_;
}
}
else
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3581_; 
lean_dec_ref(v___y_3545_);
lean_dec_ref(v___y_3541_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec_ref(v_b_3302_);
lean_dec(v_ref_3298_);
lean_dec(v_codeActionPrefix_x3f_3297_);
v_a_3574_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3576_ = v___x_3551_;
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3551_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3579_; 
if (v_isShared_3577_ == 0)
{
v___x_3579_ = v___x_3576_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_a_3574_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
v___jp_3582_:
{
lean_object* v_toCodeActionTitle_x3f_3592_; lean_object* v___x_3593_; 
v_toCodeActionTitle_x3f_3592_ = lean_ctor_get(v___y_3590_, 5);
v___x_3593_ = l_Lean_Syntax_ofRange(v___y_3591_, v___x_3351_);
if (lean_obj_tag(v_toCodeActionTitle_x3f_3592_) == 0)
{
if (lean_obj_tag(v_codeActionPrefix_x3f_3297_) == 0)
{
lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3594_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__36));
v___x_3595_ = lean_string_append(v___x_3594_, v___y_3583_);
v___y_3537_ = v___x_3593_;
v___y_3538_ = v___y_3583_;
v___y_3539_ = v___y_3584_;
v___y_3540_ = v___y_3585_;
v___y_3541_ = v___y_3587_;
v___y_3542_ = v___y_3586_;
v___y_3543_ = v___y_3589_;
v___y_3544_ = v___y_3588_;
v___y_3545_ = v___y_3590_;
v___y_3546_ = v___x_3595_;
goto v___jp_3536_;
}
else
{
lean_object* v_val_3596_; lean_object* v___x_3597_; 
v_val_3596_ = lean_ctor_get(v_codeActionPrefix_x3f_3297_, 0);
lean_inc(v_val_3596_);
v___x_3597_ = lean_string_append(v_val_3596_, v___y_3583_);
v___y_3537_ = v___x_3593_;
v___y_3538_ = v___y_3583_;
v___y_3539_ = v___y_3584_;
v___y_3540_ = v___y_3585_;
v___y_3541_ = v___y_3587_;
v___y_3542_ = v___y_3586_;
v___y_3543_ = v___y_3589_;
v___y_3544_ = v___y_3588_;
v___y_3545_ = v___y_3590_;
v___y_3546_ = v___x_3597_;
goto v___jp_3536_;
}
}
else
{
lean_object* v_val_3598_; lean_object* v___x_3599_; 
v_val_3598_ = lean_ctor_get(v_toCodeActionTitle_x3f_3592_, 0);
lean_inc(v_val_3598_);
lean_inc_ref(v___y_3583_);
v___x_3599_ = lean_apply_1(v_val_3598_, v___y_3583_);
v___y_3537_ = v___x_3593_;
v___y_3538_ = v___y_3583_;
v___y_3539_ = v___y_3584_;
v___y_3540_ = v___y_3585_;
v___y_3541_ = v___y_3587_;
v___y_3542_ = v___y_3586_;
v___y_3543_ = v___y_3589_;
v___y_3544_ = v___y_3588_;
v___y_3545_ = v___y_3590_;
v___y_3546_ = v___x_3599_;
goto v___jp_3536_;
}
}
v___jp_3600_:
{
uint8_t v___x_3602_; lean_object* v___x_3603_; 
v___x_3602_ = 0;
v___x_3603_ = l_Lean_Syntax_getRange_x3f(v___y_3601_, v___x_3602_);
lean_dec(v___y_3601_);
if (lean_obj_tag(v___x_3603_) == 1)
{
lean_object* v_val_3604_; lean_object* v_toTryThisSuggestion_3605_; lean_object* v_previewSpan_x3f_3606_; uint8_t v_diffGranularity_3607_; lean_object* v___x_3608_; 
v_val_3604_ = lean_ctor_get(v___x_3603_, 0);
lean_inc_n(v_val_3604_, 2);
lean_dec_ref_known(v___x_3603_, 1);
v_toTryThisSuggestion_3605_ = lean_ctor_get(v_a_3353_, 0);
v_previewSpan_x3f_3606_ = lean_ctor_get(v_a_3353_, 2);
v_diffGranularity_3607_ = lean_ctor_get_uint8(v_a_3353_, sizeof(void*)*3);
lean_inc_ref(v_toTryThisSuggestion_3605_);
v___x_3608_ = l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(v_toTryThisSuggestion_3605_, v_val_3604_, v___y_3303_, v___y_3304_);
if (lean_obj_tag(v___x_3608_) == 0)
{
lean_object* v_a_3609_; lean_object* v_range_3610_; lean_object* v_newText_3611_; lean_object* v___x_3612_; 
v_a_3609_ = lean_ctor_get(v___x_3608_, 0);
lean_inc(v_a_3609_);
lean_dec_ref_known(v___x_3608_, 1);
v_range_3610_ = lean_ctor_get(v_a_3609_, 0);
lean_inc_ref(v_range_3610_);
v_newText_3611_ = lean_ctor_get(v_a_3609_, 1);
lean_inc_ref(v_newText_3611_);
v___x_3612_ = l_Lean_Syntax_getRange_x3f(v_ref_3298_, v___x_3602_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_inc_ref(v_toTryThisSuggestion_3605_);
lean_inc(v_previewSpan_x3f_3606_);
lean_inc(v_val_3604_);
v___y_3583_ = v_newText_3611_;
v___y_3584_ = v_val_3604_;
v___y_3585_ = v_previewSpan_x3f_3606_;
v___y_3586_ = v_a_3609_;
v___y_3587_ = v_range_3610_;
v___y_3588_ = v_diffGranularity_3607_;
v___y_3589_ = v___x_3602_;
v___y_3590_ = v_toTryThisSuggestion_3605_;
v___y_3591_ = v_val_3604_;
goto v___jp_3582_;
}
else
{
lean_object* v_val_3613_; 
v_val_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_val_3613_);
lean_dec_ref_known(v___x_3612_, 1);
lean_inc_ref(v_toTryThisSuggestion_3605_);
lean_inc(v_previewSpan_x3f_3606_);
v___y_3583_ = v_newText_3611_;
v___y_3584_ = v_val_3604_;
v___y_3585_ = v_previewSpan_x3f_3606_;
v___y_3586_ = v_a_3609_;
v___y_3587_ = v_range_3610_;
v___y_3588_ = v_diffGranularity_3607_;
v___y_3589_ = v___x_3602_;
v___y_3590_ = v_toTryThisSuggestion_3605_;
v___y_3591_ = v_val_3613_;
goto v___jp_3582_;
}
}
else
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3621_; 
lean_dec(v_val_3604_);
lean_dec_ref(v_b_3302_);
lean_dec(v_ref_3298_);
lean_dec(v_codeActionPrefix_x3f_3297_);
v_a_3614_ = lean_ctor_get(v___x_3608_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3608_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3616_ = v___x_3608_;
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3608_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3614_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
else
{
lean_dec(v___x_3603_);
v_a_3307_ = v_b_3302_;
goto v___jp_3306_;
}
}
}
v___jp_3306_:
{
size_t v___x_3308_; size_t v___x_3309_; 
v___x_3308_ = ((size_t)1ULL);
v___x_3309_ = lean_usize_add(v_i_3301_, v___x_3308_);
v_i_3301_ = v___x_3309_;
v_b_3302_ = v_a_3307_;
goto _start;
}
v___jp_3311_:
{
lean_object* v___x_3313_; lean_object* v___x_3314_; 
v___x_3313_ = l_Lean_MessageData_nestD(v___y_3312_);
v___x_3314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3314_, 0, v_b_3302_);
lean_ctor_set(v___x_3314_, 1, v___x_3313_);
v_a_3307_ = v___x_3314_;
goto v___jp_3306_;
}
v___jp_3315_:
{
lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
v___x_3319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___y_3316_);
lean_ctor_set(v___x_3319_, 1, v___y_3318_);
v___x_3320_ = l_Lean_stringToMessageData(v___y_3317_);
v___x_3321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3319_);
lean_ctor_set(v___x_3321_, 1, v___x_3320_);
v___y_3312_ = v___x_3321_;
goto v___jp_3311_;
}
v___jp_3322_:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3324_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3325_ = lean_unsigned_to_nat(2u);
v___x_3326_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3);
v___x_3327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3326_);
lean_ctor_set(v___x_3327_, 1, v___y_3323_);
v___x_3328_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3325_);
lean_ctor_set(v___x_3328_, 1, v___x_3327_);
v___x_3329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3324_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
v___y_3312_ = v___x_3329_;
goto v___jp_3311_;
}
v___jp_3330_:
{
lean_object* v___x_3335_; uint64_t v_javascriptHash_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; uint8_t v___x_3348_; 
v___x_3335_ = l_Lean_Meta_Hint_tryThisDiffWidget;
v_javascriptHash_3336_ = lean_ctor_get_uint64(v___x_3335_, sizeof(void*)*1);
v___x_3337_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8));
v___x_3338_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3338_, 0, v___x_3337_);
lean_ctor_set(v___x_3338_, 1, v___y_3331_);
lean_ctor_set_uint64(v___x_3338_, sizeof(void*)*2, v_javascriptHash_3336_);
v___x_3339_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3339_, 0, v___y_3334_);
v___x_3340_ = l_Lean_MessageData_ofFormat(v___x_3339_);
v___x_3341_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3338_);
lean_ctor_set(v___x_3341_, 1, v___x_3340_);
v___x_3342_ = l_Lean_stringToMessageData(v___y_3332_);
v___x_3343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3343_, 0, v___x_3342_);
lean_ctor_set(v___x_3343_, 1, v___x_3341_);
v___x_3344_ = l_Lean_stringToMessageData(v___y_3333_);
v___x_3345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3343_);
lean_ctor_set(v___x_3345_, 1, v___x_3344_);
v___x_3346_ = lean_array_get_size(v_suggestions_3295_);
v___x_3347_ = lean_unsigned_to_nat(1u);
v___x_3348_ = lean_nat_dec_eq(v___x_3346_, v___x_3347_);
if (v___x_3348_ == 0)
{
v___y_3323_ = v___x_3345_;
goto v___jp_3322_;
}
else
{
if (v_forceList_3296_ == 0)
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3349_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3349_);
lean_ctor_set(v___x_3350_, 1, v___x_3345_);
v___y_3312_ = v___x_3350_;
goto v___jp_3311_;
}
else
{
v___y_3323_ = v___x_3345_;
goto v___jp_3322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___boxed(lean_object* v_suggestions_3623_, lean_object* v_forceList_3624_, lean_object* v_codeActionPrefix_x3f_3625_, lean_object* v_ref_3626_, lean_object* v_as_3627_, lean_object* v_sz_3628_, lean_object* v_i_3629_, lean_object* v_b_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
uint8_t v_forceList_boxed_3634_; size_t v_sz_boxed_3635_; size_t v_i_boxed_3636_; lean_object* v_res_3637_; 
v_forceList_boxed_3634_ = lean_unbox(v_forceList_3624_);
v_sz_boxed_3635_ = lean_unbox_usize(v_sz_3628_);
lean_dec(v_sz_3628_);
v_i_boxed_3636_ = lean_unbox_usize(v_i_3629_);
lean_dec(v_i_3629_);
v_res_3637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3623_, v_forceList_boxed_3634_, v_codeActionPrefix_x3f_3625_, v_ref_3626_, v_as_3627_, v_sz_boxed_3635_, v_i_boxed_3636_, v_b_3630_, v___y_3631_, v___y_3632_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec_ref(v_as_3627_);
lean_dec_ref(v_suggestions_3623_);
return v_res_3637_;
}
}
static lean_object* _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0(void){
_start:
{
lean_object* v___x_3638_; lean_object* v_msg_3639_; 
v___x_3638_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v_msg_3639_ = l_Lean_stringToMessageData(v___x_3638_);
return v_msg_3639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage(lean_object* v_suggestions_3640_, lean_object* v_ref_3641_, lean_object* v_codeActionPrefix_x3f_3642_, uint8_t v_forceList_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_){
_start:
{
lean_object* v_msg_3647_; size_t v_sz_3648_; size_t v___x_3649_; lean_object* v___x_3650_; 
v_msg_3647_ = lean_obj_once(&l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0, &l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0_once, _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0);
v_sz_3648_ = lean_array_size(v_suggestions_3640_);
v___x_3649_ = ((size_t)0ULL);
v___x_3650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3640_, v_forceList_3643_, v_codeActionPrefix_x3f_3642_, v_ref_3641_, v_suggestions_3640_, v_sz_3648_, v___x_3649_, v_msg_3647_, v_a_3644_, v_a_3645_);
return v___x_3650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage___boxed(lean_object* v_suggestions_3651_, lean_object* v_ref_3652_, lean_object* v_codeActionPrefix_x3f_3653_, lean_object* v_forceList_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_){
_start:
{
uint8_t v_forceList_boxed_3658_; lean_object* v_res_3659_; 
v_forceList_boxed_3658_ = lean_unbox(v_forceList_3654_);
v_res_3659_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3651_, v_ref_3652_, v_codeActionPrefix_x3f_3653_, v_forceList_boxed_3658_, v_a_3655_, v_a_3656_);
lean_dec(v_a_3656_);
lean_dec_ref(v_a_3655_);
lean_dec_ref(v_suggestions_3651_);
return v_res_3659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(lean_object* v_t_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_){
_start:
{
lean_object* v___x_3664_; 
v___x_3664_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3660_, v___y_3662_);
return v___x_3664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___boxed(lean_object* v_t_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(v_t_3665_, v___y_3666_, v___y_3667_);
lean_dec(v___y_3667_);
lean_dec_ref(v___y_3666_);
return v_res_3669_;
}
}
static lean_object* _init_l_Lean_MessageData_hint___closed__3(void){
_start:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3674_ = ((lean_object*)(l_Lean_MessageData_hint___closed__2));
v___x_3675_ = l_Lean_stringToMessageData(v___x_3674_);
return v___x_3675_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint(lean_object* v_hint_3676_, lean_object* v_suggestions_3677_, lean_object* v_ref_x3f_3678_, lean_object* v_codeActionPrefix_x3f_3679_, uint8_t v_forceList_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_){
_start:
{
lean_object* v___y_3685_; 
if (lean_obj_tag(v_ref_x3f_3678_) == 0)
{
lean_object* v_ref_3700_; 
v_ref_3700_ = lean_ctor_get(v_a_3681_, 2);
lean_inc(v_ref_3700_);
v___y_3685_ = v_ref_3700_;
goto v___jp_3684_;
}
else
{
lean_object* v_val_3701_; 
v_val_3701_ = lean_ctor_get(v_ref_x3f_3678_, 0);
lean_inc(v_val_3701_);
lean_dec_ref_known(v_ref_x3f_3678_, 1);
v___y_3685_ = v_val_3701_;
goto v___jp_3684_;
}
v___jp_3684_:
{
lean_object* v___x_3686_; 
v___x_3686_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3677_, v___y_3685_, v_codeActionPrefix_x3f_3679_, v_forceList_3680_, v_a_3681_, v_a_3682_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3699_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3689_ = v___x_3686_;
v_isShared_3690_ = v_isSharedCheck_3699_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3686_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3699_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3697_; 
v___x_3691_ = ((lean_object*)(l_Lean_MessageData_hint___closed__1));
v___x_3692_ = lean_obj_once(&l_Lean_MessageData_hint___closed__3, &l_Lean_MessageData_hint___closed__3_once, _init_l_Lean_MessageData_hint___closed__3);
v___x_3693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3692_);
lean_ctor_set(v___x_3693_, 1, v_hint_3676_);
v___x_3694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3693_);
lean_ctor_set(v___x_3694_, 1, v_a_3687_);
v___x_3695_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3691_);
lean_ctor_set(v___x_3695_, 1, v___x_3694_);
if (v_isShared_3690_ == 0)
{
lean_ctor_set(v___x_3689_, 0, v___x_3695_);
v___x_3697_ = v___x_3689_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v___x_3695_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
else
{
lean_dec_ref(v_hint_3676_);
return v___x_3686_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint___boxed(lean_object* v_hint_3702_, lean_object* v_suggestions_3703_, lean_object* v_ref_x3f_3704_, lean_object* v_codeActionPrefix_x3f_3705_, lean_object* v_forceList_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_){
_start:
{
uint8_t v_forceList_boxed_3710_; lean_object* v_res_3711_; 
v_forceList_boxed_3710_ = lean_unbox(v_forceList_3706_);
v_res_3711_ = l_Lean_MessageData_hint(v_hint_3702_, v_suggestions_3703_, v_ref_x3f_3704_, v_codeActionPrefix_x3f_3705_, v_forceList_boxed_3710_, v_a_3707_, v_a_3708_);
lean_dec(v_a_3708_);
lean_dec_ref(v_a_3707_);
lean_dec_ref(v_suggestions_3703_);
return v_res_3711_;
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
