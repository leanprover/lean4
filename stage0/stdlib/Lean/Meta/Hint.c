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
static const lean_ctor_object l_Lean_Meta_Hint_textInsertionWidget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Hint_textInsertionWidget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 117, 128, 13, 188, 175, 182, 195)}};
static const lean_object* l_Lean_Meta_Hint_textInsertionWidget___closed__1 = (const lean_object*)&l_Lean_Meta_Hint_textInsertionWidget___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Hint_textInsertionWidget = (const lean_object*)&l_Lean_Meta_Hint_textInsertionWidget___closed__1_value;
static const lean_string_object l_Lean_Meta_Hint_tryThisDiffWidget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1142, .m_capacity = 1142, .m_length = 1141, .m_data = "\nimport * as React from 'react';\nimport { EditorContext, EnvPosContext } from '@leanprover/infoview';\n\nconst e = React.createElement;\nexport default function ({ diff, range, suggestion }) {\n  const pos = React.useContext(EnvPosContext)\n  const editorConnection = React.useContext(EditorContext)\n  const insStyle = {\n    style: { color: 'var(--vscode-textLink-foreground)' }\n  }\n  const delStyle = {\n    style: { color: 'var(--vscode-editorError-foreground)', textDecoration: 'line-through' }\n  }\n  const defStyle = {\n    style: { color: 'var(--vscode-editor-foreground)' }\n  }\n  function onClick() {\n    editorConnection.api.applyEdit({\n      changes: { [pos.uri]: [{ range, newText: suggestion }] }\n    })\n  }\n\n  const spans = diff.map (comp =>\n    comp.type === 'deletion' \? e('span', delStyle, comp.text) :\n    comp.type === 'insertion' \? e('span', insStyle, comp.text) :\n      e('span', defStyle, comp.text)\n  )\n  const fullDiff = e('span',\n    { onClick,\n      title: 'Apply suggestion',\n      className: 'link pointer dim font-code',\n      style: { display: 'inline-block', verticalAlign: 'text-top' } },\n    spans)\n  return fullDiff\n}"};
static const lean_object* l_Lean_Meta_Hint_tryThisDiffWidget___closed__0 = (const lean_object*)&l_Lean_Meta_Hint_tryThisDiffWidget___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Hint_tryThisDiffWidget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_Hint_tryThisDiffWidget___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 197, 103, 127, 237, 67, 160, 93)}};
static const lean_object* l_Lean_Meta_Hint_tryThisDiffWidget___closed__1 = (const lean_object*)&l_Lean_Meta_Hint_tryThisDiffWidget___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Hint_tryThisDiffWidget = (const lean_object*)&l_Lean_Meta_Hint_tryThisDiffWidget___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1(size_t v_sz_11_, size_t v_i_12_, lean_object* v_bs_13_){
_start:
{
uint8_t v___x_14_; 
v___x_14_ = lean_usize_dec_lt(v_i_12_, v_sz_11_);
if (v___x_14_ == 0)
{
return v_bs_13_;
}
else
{
lean_object* v_v_15_; lean_object* v___x_16_; lean_object* v_bs_x27_17_; size_t v___x_18_; size_t v___x_19_; lean_object* v___x_20_; 
v_v_15_ = lean_array_uget(v_bs_13_, v_i_12_);
v___x_16_ = lean_unsigned_to_nat(0u);
v_bs_x27_17_ = lean_array_uset(v_bs_13_, v_i_12_, v___x_16_);
v___x_18_ = ((size_t)1ULL);
v___x_19_ = lean_usize_add(v_i_12_, v___x_18_);
v___x_20_ = lean_array_uset(v_bs_x27_17_, v_i_12_, v_v_15_);
v_i_12_ = v___x_19_;
v_bs_13_ = v___x_20_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1___boxed(lean_object* v_sz_22_, lean_object* v_i_23_, lean_object* v_bs_24_){
_start:
{
size_t v_sz_boxed_25_; size_t v_i_boxed_26_; lean_object* v_res_27_; 
v_sz_boxed_25_ = lean_unbox_usize(v_sz_22_);
lean_dec(v_sz_22_);
v_i_boxed_26_ = lean_unbox_usize(v_i_23_);
lean_dec(v_i_23_);
v_res_27_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1(v_sz_boxed_25_, v_i_boxed_26_, v_bs_24_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1(lean_object* v_a_28_){
_start:
{
size_t v_sz_29_; size_t v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v_sz_29_ = lean_array_size(v_a_28_);
v___x_30_ = ((size_t)0ULL);
v___x_31_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1(v_sz_29_, v___x_30_, v_a_28_);
v___x_32_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0(size_t v_sz_53_, size_t v_i_54_, lean_object* v_bs_55_){
_start:
{
uint8_t v___x_56_; 
v___x_56_ = lean_usize_dec_lt(v_i_54_, v_sz_53_);
if (v___x_56_ == 0)
{
return v_bs_55_;
}
else
{
lean_object* v_v_57_; lean_object* v_fst_58_; lean_object* v_snd_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_102_; 
v_v_57_ = lean_array_uget(v_bs_55_, v_i_54_);
v_fst_58_ = lean_ctor_get(v_v_57_, 0);
v_snd_59_ = lean_ctor_get(v_v_57_, 1);
v_isSharedCheck_102_ = !lean_is_exclusive(v_v_57_);
if (v_isSharedCheck_102_ == 0)
{
v___x_61_ = v_v_57_;
v_isShared_62_ = v_isSharedCheck_102_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_snd_59_);
lean_inc(v_fst_58_);
lean_dec(v_v_57_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_102_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_63_; lean_object* v_bs_x27_64_; lean_object* v___y_66_; uint8_t v___x_71_; 
v___x_63_ = lean_unsigned_to_nat(0u);
v_bs_x27_64_ = lean_array_uset(v_bs_55_, v_i_54_, v___x_63_);
v___x_71_ = lean_unbox(v_fst_58_);
lean_dec(v_fst_58_);
switch(v___x_71_)
{
case 0:
{
lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_76_; 
v___x_72_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__3));
v___x_73_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__4));
v___x_74_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_74_, 0, v_snd_59_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 1, v___x_74_);
lean_ctor_set(v___x_61_, 0, v___x_73_);
v___x_76_ = v___x_61_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_73_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v___x_74_);
v___x_76_ = v_reuseFailAlloc_81_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_77_ = lean_box(0);
v___x_78_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_76_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
v___x_79_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_72_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = l_Lean_Json_mkObj(v___x_79_);
lean_dec_ref_known(v___x_79_, 2);
v___y_66_ = v___x_80_;
goto v___jp_65_;
}
}
case 1:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_86_; 
v___x_82_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__7));
v___x_83_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__4));
v___x_84_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_84_, 0, v_snd_59_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 1, v___x_84_);
lean_ctor_set(v___x_61_, 0, v___x_83_);
v___x_86_ = v___x_61_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_83_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v___x_84_);
v___x_86_ = v_reuseFailAlloc_91_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_87_ = lean_box(0);
v___x_88_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_86_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
v___x_89_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_82_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = l_Lean_Json_mkObj(v___x_89_);
lean_dec_ref_known(v___x_89_, 2);
v___y_66_ = v___x_90_;
goto v___jp_65_;
}
}
default: 
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_96_; 
v___x_92_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__10));
v___x_93_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__4));
v___x_94_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_94_, 0, v_snd_59_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 1, v___x_94_);
lean_ctor_set(v___x_61_, 0, v___x_93_);
v___x_96_ = v___x_61_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v___x_93_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v___x_94_);
v___x_96_ = v_reuseFailAlloc_101_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_97_ = lean_box(0);
v___x_98_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_96_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_92_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v___x_100_ = l_Lean_Json_mkObj(v___x_99_);
lean_dec_ref_known(v___x_99_, 2);
v___y_66_ = v___x_100_;
goto v___jp_65_;
}
}
}
v___jp_65_:
{
size_t v___x_67_; size_t v___x_68_; lean_object* v___x_69_; 
v___x_67_ = ((size_t)1ULL);
v___x_68_ = lean_usize_add(v_i_54_, v___x_67_);
v___x_69_ = lean_array_uset(v_bs_x27_64_, v_i_54_, v___y_66_);
v_i_54_ = v___x_68_;
v_bs_55_ = v___x_69_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___boxed(lean_object* v_sz_103_, lean_object* v_i_104_, lean_object* v_bs_105_){
_start:
{
size_t v_sz_boxed_106_; size_t v_i_boxed_107_; lean_object* v_res_108_; 
v_sz_boxed_106_ = lean_unbox_usize(v_sz_103_);
lean_dec(v_sz_103_);
v_i_boxed_107_ = lean_unbox_usize(v_i_104_);
lean_dec(v_i_104_);
v_res_108_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0(v_sz_boxed_106_, v_i_boxed_107_, v_bs_105_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson(lean_object* v_ds_109_){
_start:
{
size_t v_sz_110_; size_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v_sz_110_ = lean_array_size(v_ds_109_);
v___x_111_ = ((size_t)0ULL);
v___x_112_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0(v_sz_110_, v___x_111_, v_ds_109_);
v___x_113_ = l_Lean_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1(v___x_112_);
return v___x_113_;
}
}
static lean_object* _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_114_; lean_object* v___x_115_; 
v___x_114_ = 821;
v___x_115_ = lean_box_uint32(v___x_114_);
return v___x_115_;
}
}
static lean_object* _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0(void){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_116_ = lean_box(0);
v___x_117_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0___boxed__const__1;
v___x_118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v___x_116_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1(lean_object* v_a_119_, lean_object* v_a_120_){
_start:
{
if (lean_obj_tag(v_a_119_) == 0)
{
lean_object* v___x_121_; 
v___x_121_ = lean_array_to_list(v_a_120_);
return v___x_121_;
}
else
{
lean_object* v_head_122_; lean_object* v_tail_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_133_; 
v_head_122_ = lean_ctor_get(v_a_119_, 0);
v_tail_123_ = lean_ctor_get(v_a_119_, 1);
v_isSharedCheck_133_ = !lean_is_exclusive(v_a_119_);
if (v_isSharedCheck_133_ == 0)
{
v___x_125_ = v_a_119_;
v_isShared_126_ = v_isSharedCheck_133_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_tail_123_);
lean_inc(v_head_122_);
lean_dec(v_a_119_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_133_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_129_; 
v___x_127_ = lean_obj_once(&l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0, &l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0_once, _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v___x_127_);
v___x_129_ = v___x_125_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_132_; 
v_reuseFailAlloc_132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_132_, 0, v_head_122_);
lean_ctor_set(v_reuseFailAlloc_132_, 1, v___x_127_);
v___x_129_ = v_reuseFailAlloc_132_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_130_; 
v___x_130_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_120_, v___x_129_);
v_a_119_ = v_tail_123_;
v_a_120_ = v___x_130_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_134_; lean_object* v___x_135_; 
v___x_134_ = 818;
v___x_135_ = lean_box_uint32(v___x_134_);
return v___x_135_;
}
}
static lean_object* _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_136_ = lean_box(0);
v___x_137_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0___boxed__const__1;
v___x_138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v___x_136_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0(lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
if (lean_obj_tag(v_a_139_) == 0)
{
lean_object* v___x_141_; 
v___x_141_ = lean_array_to_list(v_a_140_);
return v___x_141_;
}
else
{
lean_object* v_head_142_; lean_object* v_tail_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_153_; 
v_head_142_ = lean_ctor_get(v_a_139_, 0);
v_tail_143_ = lean_ctor_get(v_a_139_, 1);
v_isSharedCheck_153_ = !lean_is_exclusive(v_a_139_);
if (v_isSharedCheck_153_ == 0)
{
v___x_145_ = v_a_139_;
v_isShared_146_ = v_isSharedCheck_153_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_tail_143_);
lean_inc(v_head_142_);
lean_dec(v_a_139_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_153_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_147_ = lean_obj_once(&l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0, &l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0_once, _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0);
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 1, v___x_147_);
v___x_149_ = v___x_145_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_head_142_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v___x_147_);
v___x_149_ = v_reuseFailAlloc_152_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_150_; 
v___x_150_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_140_, v___x_149_);
v_a_139_ = v_tail_143_;
v_a_140_ = v___x_150_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2(size_t v_sz_156_, size_t v_i_157_, lean_object* v_bs_158_){
_start:
{
uint8_t v___x_159_; 
v___x_159_ = lean_usize_dec_lt(v_i_157_, v_sz_156_);
if (v___x_159_ == 0)
{
return v_bs_158_;
}
else
{
lean_object* v_v_160_; lean_object* v_fst_161_; lean_object* v_snd_162_; lean_object* v___x_163_; lean_object* v_bs_x27_164_; lean_object* v___y_166_; uint8_t v___x_171_; 
v_v_160_ = lean_array_uget_borrowed(v_bs_158_, v_i_157_);
v_fst_161_ = lean_ctor_get(v_v_160_, 0);
lean_inc(v_fst_161_);
v_snd_162_ = lean_ctor_get(v_v_160_, 1);
lean_inc(v_snd_162_);
v___x_163_ = lean_unsigned_to_nat(0u);
v_bs_x27_164_ = lean_array_uset(v_bs_158_, v_i_157_, v___x_163_);
v___x_171_ = lean_unbox(v_fst_161_);
lean_dec(v_fst_161_);
switch(v___x_171_)
{
case 0:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_172_ = lean_string_data(v_snd_162_);
v___x_173_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_174_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0(v___x_172_, v___x_173_);
v___x_175_ = lean_string_mk(v___x_174_);
v___y_166_ = v___x_175_;
goto v___jp_165_;
}
case 1:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_176_ = lean_string_data(v_snd_162_);
v___x_177_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_178_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1(v___x_176_, v___x_177_);
v___x_179_ = lean_string_mk(v___x_178_);
v___y_166_ = v___x_179_;
goto v___jp_165_;
}
default: 
{
v___y_166_ = v_snd_162_;
goto v___jp_165_;
}
}
v___jp_165_:
{
size_t v___x_167_; size_t v___x_168_; lean_object* v___x_169_; 
v___x_167_ = ((size_t)1ULL);
v___x_168_ = lean_usize_add(v_i_157_, v___x_167_);
v___x_169_ = lean_array_uset(v_bs_x27_164_, v_i_157_, v___y_166_);
v_i_157_ = v___x_168_;
v_bs_158_ = v___x_169_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___boxed(lean_object* v_sz_180_, lean_object* v_i_181_, lean_object* v_bs_182_){
_start:
{
size_t v_sz_boxed_183_; size_t v_i_boxed_184_; lean_object* v_res_185_; 
v_sz_boxed_183_ = lean_unbox_usize(v_sz_180_);
lean_dec(v_sz_180_);
v_i_boxed_184_ = lean_unbox_usize(v_i_181_);
lean_dec(v_i_181_);
v_res_185_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2(v_sz_boxed_183_, v_i_boxed_184_, v_bs_182_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(lean_object* v_as_186_, size_t v_i_187_, size_t v_stop_188_, lean_object* v_b_189_){
_start:
{
uint8_t v___x_190_; 
v___x_190_ = lean_usize_dec_eq(v_i_187_, v_stop_188_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; lean_object* v___x_192_; size_t v___x_193_; size_t v___x_194_; 
v___x_191_ = lean_array_uget_borrowed(v_as_186_, v_i_187_);
v___x_192_ = lean_string_append(v_b_189_, v___x_191_);
v___x_193_ = ((size_t)1ULL);
v___x_194_ = lean_usize_add(v_i_187_, v___x_193_);
v_i_187_ = v___x_194_;
v_b_189_ = v___x_192_;
goto _start;
}
else
{
return v_b_189_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3___boxed(lean_object* v_as_196_, lean_object* v_i_197_, lean_object* v_stop_198_, lean_object* v_b_199_){
_start:
{
size_t v_i_boxed_200_; size_t v_stop_boxed_201_; lean_object* v_res_202_; 
v_i_boxed_200_ = lean_unbox_usize(v_i_197_);
lean_dec(v_i_197_);
v_stop_boxed_201_ = lean_unbox_usize(v_stop_198_);
lean_dec(v_stop_198_);
v_res_202_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_as_196_, v_i_boxed_200_, v_stop_boxed_201_, v_b_199_);
lean_dec_ref(v_as_196_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString(lean_object* v_ds_204_){
_start:
{
size_t v_sz_205_; size_t v___x_206_; lean_object* v_rangeStrs_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; uint8_t v___x_211_; 
v_sz_205_ = lean_array_size(v_ds_204_);
v___x_206_ = ((size_t)0ULL);
v_rangeStrs_207_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2(v_sz_205_, v___x_206_, v_ds_204_);
v___x_208_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_210_ = lean_array_get_size(v_rangeStrs_207_);
v___x_211_ = lean_nat_dec_lt(v___x_209_, v___x_210_);
if (v___x_211_ == 0)
{
lean_dec_ref(v_rangeStrs_207_);
return v___x_208_;
}
else
{
uint8_t v___x_212_; 
v___x_212_ = lean_nat_dec_le(v___x_210_, v___x_210_);
if (v___x_212_ == 0)
{
if (v___x_211_ == 0)
{
lean_dec_ref(v_rangeStrs_207_);
return v___x_208_;
}
else
{
size_t v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_usize_of_nat(v___x_210_);
v___x_214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_rangeStrs_207_, v___x_206_, v___x_213_, v___x_208_);
lean_dec_ref(v_rangeStrs_207_);
return v___x_214_;
}
}
else
{
size_t v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_usize_of_nat(v___x_210_);
v___x_216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_rangeStrs_207_, v___x_206_, v___x_215_, v___x_208_);
lean_dec_ref(v_rangeStrs_207_);
return v___x_216_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorIdx(uint8_t v_x_217_){
_start:
{
switch(v_x_217_)
{
case 0:
{
lean_object* v___x_218_; 
v___x_218_ = lean_unsigned_to_nat(0u);
return v___x_218_;
}
case 1:
{
lean_object* v___x_219_; 
v___x_219_ = lean_unsigned_to_nat(1u);
return v___x_219_;
}
case 2:
{
lean_object* v___x_220_; 
v___x_220_ = lean_unsigned_to_nat(2u);
return v___x_220_;
}
case 3:
{
lean_object* v___x_221_; 
v___x_221_ = lean_unsigned_to_nat(3u);
return v___x_221_;
}
default: 
{
lean_object* v___x_222_; 
v___x_222_ = lean_unsigned_to_nat(4u);
return v___x_222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorIdx___boxed(lean_object* v_x_223_){
_start:
{
uint8_t v_x_boxed_224_; lean_object* v_res_225_; 
v_x_boxed_224_ = lean_unbox(v_x_223_);
v_res_225_ = l_Lean_Meta_Hint_DiffGranularity_ctorIdx(v_x_boxed_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim___redArg(lean_object* v_k_226_){
_start:
{
lean_inc(v_k_226_);
return v_k_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim___redArg___boxed(lean_object* v_k_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_Meta_Hint_DiffGranularity_ctorElim___redArg(v_k_227_);
lean_dec(v_k_227_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim(lean_object* v_motive_229_, lean_object* v_ctorIdx_230_, uint8_t v_t_231_, lean_object* v_h_232_, lean_object* v_k_233_){
_start:
{
lean_inc(v_k_233_);
return v_k_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim___boxed(lean_object* v_motive_234_, lean_object* v_ctorIdx_235_, lean_object* v_t_236_, lean_object* v_h_237_, lean_object* v_k_238_){
_start:
{
uint8_t v_t_boxed_239_; lean_object* v_res_240_; 
v_t_boxed_239_ = lean_unbox(v_t_236_);
v_res_240_ = l_Lean_Meta_Hint_DiffGranularity_ctorElim(v_motive_234_, v_ctorIdx_235_, v_t_boxed_239_, v_h_237_, v_k_238_);
lean_dec(v_k_238_);
lean_dec(v_ctorIdx_235_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim___redArg(lean_object* v_auto_241_){
_start:
{
lean_inc(v_auto_241_);
return v_auto_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim___redArg___boxed(lean_object* v_auto_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = l_Lean_Meta_Hint_DiffGranularity_auto_elim___redArg(v_auto_242_);
lean_dec(v_auto_242_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim(lean_object* v_motive_244_, uint8_t v_t_245_, lean_object* v_h_246_, lean_object* v_auto_247_){
_start:
{
lean_inc(v_auto_247_);
return v_auto_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim___boxed(lean_object* v_motive_248_, lean_object* v_t_249_, lean_object* v_h_250_, lean_object* v_auto_251_){
_start:
{
uint8_t v_t_boxed_252_; lean_object* v_res_253_; 
v_t_boxed_252_ = lean_unbox(v_t_249_);
v_res_253_ = l_Lean_Meta_Hint_DiffGranularity_auto_elim(v_motive_248_, v_t_boxed_252_, v_h_250_, v_auto_251_);
lean_dec(v_auto_251_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim___redArg(lean_object* v_char_254_){
_start:
{
lean_inc(v_char_254_);
return v_char_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim___redArg___boxed(lean_object* v_char_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_Meta_Hint_DiffGranularity_char_elim___redArg(v_char_255_);
lean_dec(v_char_255_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim(lean_object* v_motive_257_, uint8_t v_t_258_, lean_object* v_h_259_, lean_object* v_char_260_){
_start:
{
lean_inc(v_char_260_);
return v_char_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim___boxed(lean_object* v_motive_261_, lean_object* v_t_262_, lean_object* v_h_263_, lean_object* v_char_264_){
_start:
{
uint8_t v_t_boxed_265_; lean_object* v_res_266_; 
v_t_boxed_265_ = lean_unbox(v_t_262_);
v_res_266_ = l_Lean_Meta_Hint_DiffGranularity_char_elim(v_motive_261_, v_t_boxed_265_, v_h_263_, v_char_264_);
lean_dec(v_char_264_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim___redArg(lean_object* v_word_267_){
_start:
{
lean_inc(v_word_267_);
return v_word_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim___redArg___boxed(lean_object* v_word_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_Meta_Hint_DiffGranularity_word_elim___redArg(v_word_268_);
lean_dec(v_word_268_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim(lean_object* v_motive_270_, uint8_t v_t_271_, lean_object* v_h_272_, lean_object* v_word_273_){
_start:
{
lean_inc(v_word_273_);
return v_word_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim___boxed(lean_object* v_motive_274_, lean_object* v_t_275_, lean_object* v_h_276_, lean_object* v_word_277_){
_start:
{
uint8_t v_t_boxed_278_; lean_object* v_res_279_; 
v_t_boxed_278_ = lean_unbox(v_t_275_);
v_res_279_ = l_Lean_Meta_Hint_DiffGranularity_word_elim(v_motive_274_, v_t_boxed_278_, v_h_276_, v_word_277_);
lean_dec(v_word_277_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim___redArg(lean_object* v_all_280_){
_start:
{
lean_inc(v_all_280_);
return v_all_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim___redArg___boxed(lean_object* v_all_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Meta_Hint_DiffGranularity_all_elim___redArg(v_all_281_);
lean_dec(v_all_281_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim(lean_object* v_motive_283_, uint8_t v_t_284_, lean_object* v_h_285_, lean_object* v_all_286_){
_start:
{
lean_inc(v_all_286_);
return v_all_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim___boxed(lean_object* v_motive_287_, lean_object* v_t_288_, lean_object* v_h_289_, lean_object* v_all_290_){
_start:
{
uint8_t v_t_boxed_291_; lean_object* v_res_292_; 
v_t_boxed_291_ = lean_unbox(v_t_288_);
v_res_292_ = l_Lean_Meta_Hint_DiffGranularity_all_elim(v_motive_287_, v_t_boxed_291_, v_h_289_, v_all_290_);
lean_dec(v_all_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim___redArg(lean_object* v_none_293_){
_start:
{
lean_inc(v_none_293_);
return v_none_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim___redArg___boxed(lean_object* v_none_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Lean_Meta_Hint_DiffGranularity_none_elim___redArg(v_none_294_);
lean_dec(v_none_294_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim(lean_object* v_motive_296_, uint8_t v_t_297_, lean_object* v_h_298_, lean_object* v_none_299_){
_start:
{
lean_inc(v_none_299_);
return v_none_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim___boxed(lean_object* v_motive_300_, lean_object* v_t_301_, lean_object* v_h_302_, lean_object* v_none_303_){
_start:
{
uint8_t v_t_boxed_304_; lean_object* v_res_305_; 
v_t_boxed_304_ = lean_unbox(v_t_301_);
v_res_305_ = l_Lean_Meta_Hint_DiffGranularity_none_elim(v_motive_300_, v_t_boxed_304_, v_h_302_, v_none_303_);
lean_dec(v_none_303_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_instCoeSuggestionTextSuggestion___lam__0(lean_object* v_t_306_){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; lean_object* v___x_310_; 
v___x_307_ = lean_box(0);
v___x_308_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_308_, 0, v_t_306_);
lean_ctor_set(v___x_308_, 1, v___x_307_);
lean_ctor_set(v___x_308_, 2, v___x_307_);
lean_ctor_set(v___x_308_, 3, v___x_307_);
lean_ctor_set(v___x_308_, 4, v___x_307_);
lean_ctor_set(v___x_308_, 5, v___x_307_);
v___x_309_ = 0;
v___x_310_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_310_, 0, v___x_308_);
lean_ctor_set(v___x_310_, 1, v___x_307_);
lean_ctor_set(v___x_310_, 2, v___x_307_);
lean_ctor_set_uint8(v___x_310_, sizeof(void*)*3, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_instToMessageDataSuggestion___lam__0(lean_object* v_s_313_){
_start:
{
lean_object* v_toTryThisSuggestion_314_; lean_object* v_messageData_x3f_315_; 
v_toTryThisSuggestion_314_ = lean_ctor_get(v_s_313_, 0);
lean_inc_ref(v_toTryThisSuggestion_314_);
lean_dec_ref(v_s_313_);
v_messageData_x3f_315_ = lean_ctor_get(v_toTryThisSuggestion_314_, 4);
if (lean_obj_tag(v_messageData_x3f_315_) == 0)
{
lean_object* v_suggestion_316_; 
v_suggestion_316_ = lean_ctor_get(v_toTryThisSuggestion_314_, 0);
lean_inc_ref(v_suggestion_316_);
lean_dec_ref(v_toTryThisSuggestion_314_);
if (lean_obj_tag(v_suggestion_316_) == 0)
{
lean_object* v_a_317_; lean_object* v___x_318_; 
v_a_317_ = lean_ctor_get(v_suggestion_316_, 1);
lean_inc(v_a_317_);
lean_dec_ref_known(v_suggestion_316_, 2);
v___x_318_ = l_Lean_MessageData_ofSyntax(v_a_317_);
return v___x_318_;
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_327_; 
v_a_319_ = lean_ctor_get(v_suggestion_316_, 0);
v_isSharedCheck_327_ = !lean_is_exclusive(v_suggestion_316_);
if (v_isSharedCheck_327_ == 0)
{
v___x_321_ = v_suggestion_316_;
v_isShared_322_ = v_isSharedCheck_327_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v_suggestion_316_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_327_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
lean_ctor_set_tag(v___x_321_, 3);
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_326_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; 
v___x_325_ = l_Lean_MessageData_ofFormat(v___x_324_);
return v___x_325_;
}
}
}
}
else
{
lean_object* v_val_328_; 
lean_inc_ref(v_messageData_x3f_315_);
lean_dec_ref(v_toTryThisSuggestion_314_);
v_val_328_ = lean_ctor_get(v_messageData_x3f_315_, 0);
lean_inc(v_val_328_);
lean_dec_ref_known(v_messageData_x3f_315_, 1);
return v_val_328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(lean_object* v_as_331_, size_t v_i_332_, size_t v_stop_333_, lean_object* v_b_334_){
_start:
{
lean_object* v___y_336_; uint8_t v___x_340_; 
v___x_340_ = lean_usize_dec_eq(v_i_332_, v_stop_333_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; lean_object* v_fst_342_; lean_object* v_snd_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_380_; 
v___x_341_ = lean_array_uget(v_as_331_, v_i_332_);
v_fst_342_ = lean_ctor_get(v___x_341_, 0);
v_snd_343_ = lean_ctor_get(v___x_341_, 1);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_341_);
if (v_isSharedCheck_380_ == 0)
{
v___x_345_ = v___x_341_;
v_isShared_346_ = v_isSharedCheck_380_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_snd_343_);
lean_inc(v_fst_342_);
lean_dec(v___x_341_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_380_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_347_ = lean_array_get_size(v_b_334_);
v___x_348_ = lean_unsigned_to_nat(0u);
v___x_349_ = lean_nat_dec_eq(v___x_347_, v___x_348_);
if (v___x_349_ == 0)
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v_fst_353_; lean_object* v_snd_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_372_; 
lean_del_object(v___x_345_);
v___x_350_ = lean_unsigned_to_nat(1u);
v___x_351_ = lean_nat_sub(v___x_347_, v___x_350_);
v___x_352_ = lean_array_fget(v_b_334_, v___x_351_);
v_fst_353_ = lean_ctor_get(v___x_352_, 0);
v_snd_354_ = lean_ctor_get(v___x_352_, 1);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_372_ == 0)
{
v___x_356_ = v___x_352_;
v_isShared_357_ = v_isSharedCheck_372_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_snd_354_);
lean_inc(v_fst_353_);
lean_dec(v___x_352_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_372_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
uint8_t v___x_358_; uint8_t v___x_359_; uint8_t v___x_360_; 
v___x_358_ = lean_unbox(v_fst_342_);
v___x_359_ = lean_unbox(v_fst_353_);
lean_dec(v_fst_353_);
v___x_360_ = l_Lean_Diff_instBEqAction_beq(v___x_358_, v___x_359_);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_364_; 
lean_dec(v_snd_354_);
lean_dec(v___x_351_);
v___x_361_ = lean_mk_empty_array_with_capacity(v___x_350_);
v___x_362_ = lean_array_push(v___x_361_, v_snd_343_);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 1, v___x_362_);
lean_ctor_set(v___x_356_, 0, v_fst_342_);
v___x_364_ = v___x_356_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_fst_342_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v___x_362_);
v___x_364_ = v_reuseFailAlloc_366_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; 
v___x_365_ = lean_array_push(v_b_334_, v___x_364_);
v___y_336_ = v___x_365_;
goto v___jp_335_;
}
}
else
{
lean_object* v___x_367_; lean_object* v___x_369_; 
v___x_367_ = lean_array_push(v_snd_354_, v_snd_343_);
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 1, v___x_367_);
lean_ctor_set(v___x_356_, 0, v_fst_342_);
v___x_369_ = v___x_356_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_fst_342_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v___x_367_);
v___x_369_ = v_reuseFailAlloc_371_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
lean_object* v___x_370_; 
v___x_370_ = lean_array_fset(v_b_334_, v___x_351_, v___x_369_);
lean_dec(v___x_351_);
v___y_336_ = v___x_370_;
goto v___jp_335_;
}
}
}
}
else
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_377_; 
lean_dec_ref(v_b_334_);
v___x_373_ = lean_unsigned_to_nat(1u);
v___x_374_ = lean_mk_empty_array_with_capacity(v___x_373_);
lean_inc_ref(v___x_374_);
v___x_375_ = lean_array_push(v___x_374_, v_snd_343_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 1, v___x_375_);
v___x_377_ = v___x_345_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_fst_342_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v___x_375_);
v___x_377_ = v_reuseFailAlloc_379_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; 
v___x_378_ = lean_array_push(v___x_374_, v___x_377_);
v___y_336_ = v___x_378_;
goto v___jp_335_;
}
}
}
}
else
{
return v_b_334_;
}
v___jp_335_:
{
size_t v___x_337_; size_t v___x_338_; 
v___x_337_ = ((size_t)1ULL);
v___x_338_ = lean_usize_add(v_i_332_, v___x_337_);
v_i_332_ = v___x_338_;
v_b_334_ = v___y_336_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg___boxed(lean_object* v_as_381_, lean_object* v_i_382_, lean_object* v_stop_383_, lean_object* v_b_384_){
_start:
{
size_t v_i_boxed_385_; size_t v_stop_boxed_386_; lean_object* v_res_387_; 
v_i_boxed_385_ = lean_unbox_usize(v_i_382_);
lean_dec(v_i_382_);
v_stop_boxed_386_ = lean_unbox_usize(v_stop_383_);
lean_dec(v_stop_383_);
v_res_387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_as_381_, v_i_boxed_385_, v_stop_boxed_386_, v_b_384_);
lean_dec_ref(v_as_381_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(lean_object* v_ds_390_){
_start:
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; uint8_t v___x_394_; 
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg___closed__0));
v___x_393_ = lean_array_get_size(v_ds_390_);
v___x_394_ = lean_nat_dec_lt(v___x_391_, v___x_393_);
if (v___x_394_ == 0)
{
return v___x_392_;
}
else
{
uint8_t v___x_395_; 
v___x_395_ = lean_nat_dec_le(v___x_393_, v___x_393_);
if (v___x_395_ == 0)
{
if (v___x_394_ == 0)
{
return v___x_392_;
}
else
{
size_t v___x_396_; size_t v___x_397_; lean_object* v___x_398_; 
v___x_396_ = ((size_t)0ULL);
v___x_397_ = lean_usize_of_nat(v___x_393_);
v___x_398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_ds_390_, v___x_396_, v___x_397_, v___x_392_);
return v___x_398_;
}
}
else
{
size_t v___x_399_; size_t v___x_400_; lean_object* v___x_401_; 
v___x_399_ = ((size_t)0ULL);
v___x_400_ = lean_usize_of_nat(v___x_393_);
v___x_401_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_ds_390_, v___x_399_, v___x_400_, v___x_392_);
return v___x_401_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg___boxed(lean_object* v_ds_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_ds_402_);
lean_dec_ref(v_ds_402_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits(lean_object* v_00_u03b1_404_, lean_object* v_ds_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_ds_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___boxed(lean_object* v_00_u03b1_407_, lean_object* v_ds_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits(v_00_u03b1_407_, v_ds_408_);
lean_dec_ref(v_ds_408_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0(lean_object* v_00_u03b1_410_, lean_object* v_as_411_, size_t v_i_412_, size_t v_stop_413_, lean_object* v_b_414_){
_start:
{
lean_object* v___x_415_; 
v___x_415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_as_411_, v_i_412_, v_stop_413_, v_b_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___boxed(lean_object* v_00_u03b1_416_, lean_object* v_as_417_, lean_object* v_i_418_, lean_object* v_stop_419_, lean_object* v_b_420_){
_start:
{
size_t v_i_boxed_421_; size_t v_stop_boxed_422_; lean_object* v_res_423_; 
v_i_boxed_421_ = lean_unbox_usize(v_i_418_);
lean_dec(v_i_418_);
v_stop_boxed_422_ = lean_unbox_usize(v_stop_419_);
lean_dec(v_stop_419_);
v_res_423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0(v_00_u03b1_416_, v_as_417_, v_i_boxed_421_, v_stop_boxed_422_, v_b_420_);
lean_dec_ref(v_as_417_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(size_t v_sz_424_, size_t v_i_425_, lean_object* v_bs_426_){
_start:
{
uint8_t v___x_427_; 
v___x_427_ = lean_usize_dec_lt(v_i_425_, v_sz_424_);
if (v___x_427_ == 0)
{
return v_bs_426_;
}
else
{
lean_object* v_v_428_; lean_object* v_fst_429_; lean_object* v_snd_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_445_; 
v_v_428_ = lean_array_uget(v_bs_426_, v_i_425_);
v_fst_429_ = lean_ctor_get(v_v_428_, 0);
v_snd_430_ = lean_ctor_get(v_v_428_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v_v_428_);
if (v_isSharedCheck_445_ == 0)
{
v___x_432_ = v_v_428_;
v_isShared_433_ = v_isSharedCheck_445_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_snd_430_);
lean_inc(v_fst_429_);
lean_dec(v_v_428_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_445_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v_bs_x27_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_434_ = lean_unsigned_to_nat(0u);
v_bs_x27_435_ = lean_array_uset(v_bs_426_, v_i_425_, v___x_434_);
v___x_436_ = lean_array_to_list(v_snd_430_);
v___x_437_ = lean_string_mk(v___x_436_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 1, v___x_437_);
v___x_439_ = v___x_432_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_fst_429_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v___x_437_);
v___x_439_ = v_reuseFailAlloc_444_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
size_t v___x_440_; size_t v___x_441_; lean_object* v___x_442_; 
v___x_440_ = ((size_t)1ULL);
v___x_441_ = lean_usize_add(v_i_425_, v___x_440_);
v___x_442_ = lean_array_uset(v_bs_x27_435_, v_i_425_, v___x_439_);
v_i_425_ = v___x_441_;
v_bs_426_ = v___x_442_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0___boxed(lean_object* v_sz_446_, lean_object* v_i_447_, lean_object* v_bs_448_){
_start:
{
size_t v_sz_boxed_449_; size_t v_i_boxed_450_; lean_object* v_res_451_; 
v_sz_boxed_449_ = lean_unbox_usize(v_sz_446_);
lean_dec(v_sz_446_);
v_i_boxed_450_ = lean_unbox_usize(v_i_447_);
lean_dec(v_i_447_);
v_res_451_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_boxed_449_, v_i_boxed_450_, v_bs_448_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(lean_object* v_d_452_){
_start:
{
lean_object* v___x_453_; size_t v_sz_454_; size_t v___x_455_; lean_object* v___x_456_; 
v___x_453_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_d_452_);
v_sz_454_ = lean_array_size(v___x_453_);
v___x_455_ = ((size_t)0ULL);
v___x_456_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_454_, v___x_455_, v___x_453_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff___boxed(lean_object* v_d_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v_d_457_);
lean_dec_ref(v_d_457_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(size_t v_sz_459_, size_t v_i_460_, lean_object* v_bs_461_){
_start:
{
uint8_t v___x_462_; 
v___x_462_ = lean_usize_dec_lt(v_i_460_, v_sz_459_);
if (v___x_462_ == 0)
{
return v_bs_461_;
}
else
{
lean_object* v_v_463_; lean_object* v___x_464_; lean_object* v_bs_x27_465_; uint8_t v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; size_t v___x_469_; size_t v___x_470_; lean_object* v___x_471_; 
v_v_463_ = lean_array_uget(v_bs_461_, v_i_460_);
v___x_464_ = lean_unsigned_to_nat(0u);
v_bs_x27_465_ = lean_array_uset(v_bs_461_, v_i_460_, v___x_464_);
v___x_466_ = 0;
v___x_467_ = lean_box(v___x_466_);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v_v_463_);
v___x_469_ = ((size_t)1ULL);
v___x_470_ = lean_usize_add(v_i_460_, v___x_469_);
v___x_471_ = lean_array_uset(v_bs_x27_465_, v_i_460_, v___x_468_);
v_i_460_ = v___x_470_;
v_bs_461_ = v___x_471_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9___boxed(lean_object* v_sz_473_, lean_object* v_i_474_, lean_object* v_bs_475_){
_start:
{
size_t v_sz_boxed_476_; size_t v_i_boxed_477_; lean_object* v_res_478_; 
v_sz_boxed_476_ = lean_unbox_usize(v_sz_473_);
lean_dec(v_sz_473_);
v_i_boxed_477_ = lean_unbox_usize(v_i_474_);
lean_dec(v_i_474_);
v_res_478_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(v_sz_boxed_476_, v_i_boxed_477_, v_bs_475_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(lean_object* v___x_479_, lean_object* v_original_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_fst_482_; lean_object* v_snd_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_502_; 
v_fst_482_ = lean_ctor_get(v_a_481_, 0);
v_snd_483_ = lean_ctor_get(v_a_481_, 1);
v_isSharedCheck_502_ = !lean_is_exclusive(v_a_481_);
if (v_isSharedCheck_502_ == 0)
{
v___x_485_ = v_a_481_;
v_isShared_486_ = v_isSharedCheck_502_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_snd_483_);
lean_inc(v_fst_482_);
lean_dec(v_a_481_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_502_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
uint8_t v___x_487_; 
v___x_487_ = lean_nat_dec_lt(v_snd_483_, v___x_479_);
if (v___x_487_ == 0)
{
lean_object* v___x_489_; 
if (v_isShared_486_ == 0)
{
v___x_489_ = v___x_485_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_fst_482_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_snd_483_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
else
{
uint8_t v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_491_ = 1;
v___x_492_ = lean_array_fget_borrowed(v_original_480_, v_snd_483_);
v___x_493_ = lean_box(v___x_491_);
lean_inc(v___x_492_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 1, v___x_492_);
lean_ctor_set(v___x_485_, 0, v___x_493_);
v___x_495_ = v___x_485_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_493_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v___x_492_);
v___x_495_ = v_reuseFailAlloc_501_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_496_ = lean_array_push(v_fst_482_, v___x_495_);
v___x_497_ = lean_unsigned_to_nat(1u);
v___x_498_ = lean_nat_add(v_snd_483_, v___x_497_);
lean_dec(v_snd_483_);
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_496_);
lean_ctor_set(v___x_499_, 1, v___x_498_);
v_a_481_ = v___x_499_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg___boxed(lean_object* v___x_503_, lean_object* v_original_504_, lean_object* v_a_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_503_, v_original_504_, v_a_505_);
lean_dec_ref(v_original_504_);
lean_dec(v___x_503_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg(uint32_t v_a_507_, lean_object* v_x_508_){
_start:
{
if (lean_obj_tag(v_x_508_) == 0)
{
lean_object* v___x_509_; 
v___x_509_ = lean_box(0);
return v___x_509_;
}
else
{
lean_object* v_key_510_; lean_object* v_value_511_; lean_object* v_tail_512_; uint32_t v___x_513_; uint8_t v___x_514_; 
v_key_510_ = lean_ctor_get(v_x_508_, 0);
v_value_511_ = lean_ctor_get(v_x_508_, 1);
v_tail_512_ = lean_ctor_get(v_x_508_, 2);
v___x_513_ = lean_unbox_uint32(v_key_510_);
v___x_514_ = lean_uint32_dec_eq(v___x_513_, v_a_507_);
if (v___x_514_ == 0)
{
v_x_508_ = v_tail_512_;
goto _start;
}
else
{
lean_object* v___x_516_; 
lean_inc(v_value_511_);
v___x_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_516_, 0, v_value_511_);
return v___x_516_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg___boxed(lean_object* v_a_517_, lean_object* v_x_518_){
_start:
{
uint32_t v_a_boxed_519_; lean_object* v_res_520_; 
v_a_boxed_519_ = lean_unbox_uint32(v_a_517_);
lean_dec(v_a_517_);
v_res_520_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg(v_a_boxed_519_, v_x_518_);
lean_dec(v_x_518_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(lean_object* v_m_521_, uint32_t v_a_522_){
_start:
{
lean_object* v_buckets_523_; lean_object* v___x_524_; uint64_t v___x_525_; uint64_t v___x_526_; uint64_t v___x_527_; uint64_t v_fold_528_; uint64_t v___x_529_; uint64_t v___x_530_; uint64_t v___x_531_; size_t v___x_532_; size_t v___x_533_; size_t v___x_534_; size_t v___x_535_; size_t v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v_buckets_523_ = lean_ctor_get(v_m_521_, 1);
v___x_524_ = lean_array_get_size(v_buckets_523_);
v___x_525_ = lean_uint32_to_uint64(v_a_522_);
v___x_526_ = 32ULL;
v___x_527_ = lean_uint64_shift_right(v___x_525_, v___x_526_);
v_fold_528_ = lean_uint64_xor(v___x_525_, v___x_527_);
v___x_529_ = 16ULL;
v___x_530_ = lean_uint64_shift_right(v_fold_528_, v___x_529_);
v___x_531_ = lean_uint64_xor(v_fold_528_, v___x_530_);
v___x_532_ = lean_uint64_to_usize(v___x_531_);
v___x_533_ = lean_usize_of_nat(v___x_524_);
v___x_534_ = ((size_t)1ULL);
v___x_535_ = lean_usize_sub(v___x_533_, v___x_534_);
v___x_536_ = lean_usize_land(v___x_532_, v___x_535_);
v___x_537_ = lean_array_uget_borrowed(v_buckets_523_, v___x_536_);
v___x_538_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg(v_a_522_, v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg___boxed(lean_object* v_m_539_, lean_object* v_a_540_){
_start:
{
uint32_t v_a_boxed_541_; lean_object* v_res_542_; 
v_a_boxed_541_ = lean_unbox_uint32(v_a_540_);
lean_dec(v_a_540_);
v_res_542_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_m_539_, v_a_boxed_541_);
lean_dec_ref(v_m_539_);
return v_res_542_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(uint32_t v_a_543_, lean_object* v_x_544_){
_start:
{
if (lean_obj_tag(v_x_544_) == 0)
{
uint8_t v___x_545_; 
v___x_545_ = 0;
return v___x_545_;
}
else
{
lean_object* v_key_546_; lean_object* v_tail_547_; uint32_t v___x_548_; uint8_t v___x_549_; 
v_key_546_ = lean_ctor_get(v_x_544_, 0);
v_tail_547_ = lean_ctor_get(v_x_544_, 2);
v___x_548_ = lean_unbox_uint32(v_key_546_);
v___x_549_ = lean_uint32_dec_eq(v___x_548_, v_a_543_);
if (v___x_549_ == 0)
{
v_x_544_ = v_tail_547_;
goto _start;
}
else
{
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg___boxed(lean_object* v_a_551_, lean_object* v_x_552_){
_start:
{
uint32_t v_a_boxed_553_; uint8_t v_res_554_; lean_object* v_r_555_; 
v_a_boxed_553_ = lean_unbox_uint32(v_a_551_);
lean_dec(v_a_551_);
v_res_554_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(v_a_boxed_553_, v_x_552_);
lean_dec(v_x_552_);
v_r_555_ = lean_box(v_res_554_);
return v_r_555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(uint32_t v_a_556_, lean_object* v_b_557_, lean_object* v_x_558_){
_start:
{
if (lean_obj_tag(v_x_558_) == 0)
{
lean_dec(v_b_557_);
return v_x_558_;
}
else
{
lean_object* v_key_559_; lean_object* v_value_560_; lean_object* v_tail_561_; lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_575_; 
v_key_559_ = lean_ctor_get(v_x_558_, 0);
v_value_560_ = lean_ctor_get(v_x_558_, 1);
v_tail_561_ = lean_ctor_get(v_x_558_, 2);
v_isSharedCheck_575_ = !lean_is_exclusive(v_x_558_);
if (v_isSharedCheck_575_ == 0)
{
v___x_563_ = v_x_558_;
v_isShared_564_ = v_isSharedCheck_575_;
goto v_resetjp_562_;
}
else
{
lean_inc(v_tail_561_);
lean_inc(v_value_560_);
lean_inc(v_key_559_);
lean_dec(v_x_558_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_575_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
uint32_t v___x_565_; uint8_t v___x_566_; 
v___x_565_ = lean_unbox_uint32(v_key_559_);
v___x_566_ = lean_uint32_dec_eq(v___x_565_, v_a_556_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_567_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(v_a_556_, v_b_557_, v_tail_561_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 2, v___x_567_);
v___x_569_ = v___x_563_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v_key_559_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_value_560_);
lean_ctor_set(v_reuseFailAlloc_570_, 2, v___x_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
else
{
lean_object* v___x_571_; lean_object* v___x_573_; 
lean_dec(v_value_560_);
lean_dec(v_key_559_);
v___x_571_ = lean_box_uint32(v_a_556_);
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 1, v_b_557_);
lean_ctor_set(v___x_563_, 0, v___x_571_);
v___x_573_ = v___x_563_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_b_557_);
lean_ctor_set(v_reuseFailAlloc_574_, 2, v_tail_561_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg___boxed(lean_object* v_a_576_, lean_object* v_b_577_, lean_object* v_x_578_){
_start:
{
uint32_t v_a_boxed_579_; lean_object* v_res_580_; 
v_a_boxed_579_ = lean_unbox_uint32(v_a_576_);
lean_dec(v_a_576_);
v_res_580_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(v_a_boxed_579_, v_b_577_, v_x_578_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29___redArg(lean_object* v_x_581_, lean_object* v_x_582_){
_start:
{
if (lean_obj_tag(v_x_582_) == 0)
{
return v_x_581_;
}
else
{
lean_object* v_key_583_; lean_object* v_value_584_; lean_object* v_tail_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_609_; 
v_key_583_ = lean_ctor_get(v_x_582_, 0);
v_value_584_ = lean_ctor_get(v_x_582_, 1);
v_tail_585_ = lean_ctor_get(v_x_582_, 2);
v_isSharedCheck_609_ = !lean_is_exclusive(v_x_582_);
if (v_isSharedCheck_609_ == 0)
{
v___x_587_ = v_x_582_;
v_isShared_588_ = v_isSharedCheck_609_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_tail_585_);
lean_inc(v_value_584_);
lean_inc(v_key_583_);
lean_dec(v_x_582_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_609_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; uint32_t v___x_590_; uint64_t v___x_591_; uint64_t v___x_592_; uint64_t v___x_593_; uint64_t v_fold_594_; uint64_t v___x_595_; uint64_t v___x_596_; uint64_t v___x_597_; size_t v___x_598_; size_t v___x_599_; size_t v___x_600_; size_t v___x_601_; size_t v___x_602_; lean_object* v___x_603_; lean_object* v___x_605_; 
v___x_589_ = lean_array_get_size(v_x_581_);
v___x_590_ = lean_unbox_uint32(v_key_583_);
v___x_591_ = lean_uint32_to_uint64(v___x_590_);
v___x_592_ = 32ULL;
v___x_593_ = lean_uint64_shift_right(v___x_591_, v___x_592_);
v_fold_594_ = lean_uint64_xor(v___x_591_, v___x_593_);
v___x_595_ = 16ULL;
v___x_596_ = lean_uint64_shift_right(v_fold_594_, v___x_595_);
v___x_597_ = lean_uint64_xor(v_fold_594_, v___x_596_);
v___x_598_ = lean_uint64_to_usize(v___x_597_);
v___x_599_ = lean_usize_of_nat(v___x_589_);
v___x_600_ = ((size_t)1ULL);
v___x_601_ = lean_usize_sub(v___x_599_, v___x_600_);
v___x_602_ = lean_usize_land(v___x_598_, v___x_601_);
v___x_603_ = lean_array_uget_borrowed(v_x_581_, v___x_602_);
lean_inc(v___x_603_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 2, v___x_603_);
v___x_605_ = v___x_587_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_key_583_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_value_584_);
lean_ctor_set(v_reuseFailAlloc_608_, 2, v___x_603_);
v___x_605_ = v_reuseFailAlloc_608_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
lean_object* v___x_606_; 
v___x_606_ = lean_array_uset(v_x_581_, v___x_602_, v___x_605_);
v_x_581_ = v___x_606_;
v_x_582_ = v_tail_585_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28___redArg(lean_object* v_i_610_, lean_object* v_source_611_, lean_object* v_target_612_){
_start:
{
lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_613_ = lean_array_get_size(v_source_611_);
v___x_614_ = lean_nat_dec_lt(v_i_610_, v___x_613_);
if (v___x_614_ == 0)
{
lean_dec_ref(v_source_611_);
lean_dec(v_i_610_);
return v_target_612_;
}
else
{
lean_object* v_es_615_; lean_object* v___x_616_; lean_object* v_source_617_; lean_object* v_target_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v_es_615_ = lean_array_fget(v_source_611_, v_i_610_);
v___x_616_ = lean_box(0);
v_source_617_ = lean_array_fset(v_source_611_, v_i_610_, v___x_616_);
v_target_618_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29___redArg(v_target_612_, v_es_615_);
v___x_619_ = lean_unsigned_to_nat(1u);
v___x_620_ = lean_nat_add(v_i_610_, v___x_619_);
lean_dec(v_i_610_);
v_i_610_ = v___x_620_;
v_source_611_ = v_source_617_;
v_target_612_ = v_target_618_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23___redArg(lean_object* v_data_622_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v_nbuckets_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_623_ = lean_array_get_size(v_data_622_);
v___x_624_ = lean_unsigned_to_nat(2u);
v_nbuckets_625_ = lean_nat_mul(v___x_623_, v___x_624_);
v___x_626_ = lean_unsigned_to_nat(0u);
v___x_627_ = lean_box(0);
v___x_628_ = lean_mk_array(v_nbuckets_625_, v___x_627_);
v___x_629_ = lean_array_propagate_mark(v_data_622_, v___x_628_);
v___x_630_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28___redArg(v___x_626_, v_data_622_, v___x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(lean_object* v_m_631_, uint32_t v_a_632_, lean_object* v_b_633_){
_start:
{
lean_object* v_size_634_; lean_object* v_buckets_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_679_; 
v_size_634_ = lean_ctor_get(v_m_631_, 0);
v_buckets_635_ = lean_ctor_get(v_m_631_, 1);
v_isSharedCheck_679_ = !lean_is_exclusive(v_m_631_);
if (v_isSharedCheck_679_ == 0)
{
v___x_637_ = v_m_631_;
v_isShared_638_ = v_isSharedCheck_679_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_buckets_635_);
lean_inc(v_size_634_);
lean_dec(v_m_631_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_679_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; uint64_t v___x_640_; uint64_t v___x_641_; uint64_t v___x_642_; uint64_t v_fold_643_; uint64_t v___x_644_; uint64_t v___x_645_; uint64_t v___x_646_; size_t v___x_647_; size_t v___x_648_; size_t v___x_649_; size_t v___x_650_; size_t v___x_651_; lean_object* v_bkt_652_; uint8_t v___x_653_; 
v___x_639_ = lean_array_get_size(v_buckets_635_);
v___x_640_ = lean_uint32_to_uint64(v_a_632_);
v___x_641_ = 32ULL;
v___x_642_ = lean_uint64_shift_right(v___x_640_, v___x_641_);
v_fold_643_ = lean_uint64_xor(v___x_640_, v___x_642_);
v___x_644_ = 16ULL;
v___x_645_ = lean_uint64_shift_right(v_fold_643_, v___x_644_);
v___x_646_ = lean_uint64_xor(v_fold_643_, v___x_645_);
v___x_647_ = lean_uint64_to_usize(v___x_646_);
v___x_648_ = lean_usize_of_nat(v___x_639_);
v___x_649_ = ((size_t)1ULL);
v___x_650_ = lean_usize_sub(v___x_648_, v___x_649_);
v___x_651_ = lean_usize_land(v___x_647_, v___x_650_);
v_bkt_652_ = lean_array_uget_borrowed(v_buckets_635_, v___x_651_);
v___x_653_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(v_a_632_, v_bkt_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v_size_x27_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v_buckets_x27_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_654_ = lean_unsigned_to_nat(1u);
v_size_x27_655_ = lean_nat_add(v_size_634_, v___x_654_);
lean_dec(v_size_634_);
v___x_656_ = lean_box_uint32(v_a_632_);
lean_inc(v_bkt_652_);
v___x_657_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v_b_633_);
lean_ctor_set(v___x_657_, 2, v_bkt_652_);
v_buckets_x27_658_ = lean_array_uset(v_buckets_635_, v___x_651_, v___x_657_);
v___x_659_ = lean_unsigned_to_nat(4u);
v___x_660_ = lean_nat_mul(v_size_x27_655_, v___x_659_);
v___x_661_ = lean_unsigned_to_nat(3u);
v___x_662_ = lean_nat_div(v___x_660_, v___x_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_array_get_size(v_buckets_x27_658_);
v___x_664_ = lean_nat_dec_le(v___x_662_, v___x_663_);
lean_dec(v___x_662_);
if (v___x_664_ == 0)
{
lean_object* v_val_665_; lean_object* v___x_667_; 
v_val_665_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23___redArg(v_buckets_x27_658_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v_val_665_);
lean_ctor_set(v___x_637_, 0, v_size_x27_655_);
v___x_667_ = v___x_637_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_size_x27_655_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_val_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
else
{
lean_object* v___x_670_; 
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v_buckets_x27_658_);
lean_ctor_set(v___x_637_, 0, v_size_x27_655_);
v___x_670_ = v___x_637_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_size_x27_655_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_buckets_x27_658_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
else
{
lean_object* v___x_672_; lean_object* v_buckets_x27_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_677_; 
lean_inc(v_bkt_652_);
v___x_672_ = lean_box(0);
v_buckets_x27_673_ = lean_array_uset(v_buckets_635_, v___x_651_, v___x_672_);
v___x_674_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(v_a_632_, v_b_633_, v_bkt_652_);
v___x_675_ = lean_array_uset(v_buckets_x27_673_, v___x_651_, v___x_674_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v___x_675_);
v___x_677_ = v___x_637_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_size_634_);
lean_ctor_set(v_reuseFailAlloc_678_, 1, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg___boxed(lean_object* v_m_680_, lean_object* v_a_681_, lean_object* v_b_682_){
_start:
{
uint32_t v_a_boxed_683_; lean_object* v_res_684_; 
v_a_boxed_683_ = lean_unbox_uint32(v_a_681_);
lean_dec(v_a_681_);
v_res_684_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_m_680_, v_a_boxed_683_, v_b_682_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(lean_object* v_histogram_685_, lean_object* v_index_686_, uint32_t v_val_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_histogram_685_, v_val_687_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_689_ = lean_unsigned_to_nat(0u);
v___x_690_ = lean_box(0);
v___x_691_ = lean_unsigned_to_nat(1u);
v___x_692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_692_, 0, v_index_686_);
v___x_693_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_693_, 0, v___x_689_);
lean_ctor_set(v___x_693_, 1, v___x_690_);
lean_ctor_set(v___x_693_, 2, v___x_691_);
lean_ctor_set(v___x_693_, 3, v___x_692_);
v___x_694_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_685_, v_val_687_, v___x_693_);
return v___x_694_;
}
else
{
lean_object* v_val_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_716_; 
v_val_695_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_716_ == 0)
{
v___x_697_ = v___x_688_;
v_isShared_698_ = v_isSharedCheck_716_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_val_695_);
lean_dec(v___x_688_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_716_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v_leftCount_699_; lean_object* v_leftIndex_700_; lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_713_; 
v_leftCount_699_ = lean_ctor_get(v_val_695_, 0);
v_leftIndex_700_ = lean_ctor_get(v_val_695_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v_val_695_);
if (v_isSharedCheck_713_ == 0)
{
lean_object* v_unused_714_; lean_object* v_unused_715_; 
v_unused_714_ = lean_ctor_get(v_val_695_, 3);
lean_dec(v_unused_714_);
v_unused_715_ = lean_ctor_get(v_val_695_, 2);
lean_dec(v_unused_715_);
v___x_702_ = v_val_695_;
v_isShared_703_ = v_isSharedCheck_713_;
goto v_resetjp_701_;
}
else
{
lean_inc(v_leftIndex_700_);
lean_inc(v_leftCount_699_);
lean_dec(v_val_695_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_713_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_707_; 
v___x_704_ = lean_unsigned_to_nat(1u);
v___x_705_ = lean_nat_add(v_leftCount_699_, v___x_704_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v_index_686_);
v___x_707_ = v___x_697_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_index_686_);
v___x_707_ = v_reuseFailAlloc_712_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_709_; 
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 3, v___x_707_);
lean_ctor_set(v___x_702_, 2, v___x_705_);
v___x_709_ = v___x_702_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_leftCount_699_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_leftIndex_700_);
lean_ctor_set(v_reuseFailAlloc_711_, 2, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_711_, 3, v___x_707_);
v___x_709_ = v_reuseFailAlloc_711_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_710_; 
v___x_710_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_685_, v_val_687_, v___x_709_);
return v___x_710_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_histogram_717_, lean_object* v_index_718_, lean_object* v_val_719_){
_start:
{
uint32_t v_val_boxed_720_; lean_object* v_res_721_; 
v_val_boxed_720_ = lean_unbox_uint32(v_val_719_);
lean_dec(v_val_719_);
v_res_721_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(v_histogram_717_, v_index_718_, v_val_boxed_720_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(lean_object* v_upperBound_722_, lean_object* v___x_723_, lean_object* v_fst_724_, lean_object* v___x_725_, lean_object* v_a_726_, lean_object* v_b_727_){
_start:
{
uint8_t v___x_728_; 
v___x_728_ = lean_nat_dec_lt(v_a_726_, v_upperBound_722_);
if (v___x_728_ == 0)
{
lean_dec(v_a_726_);
return v_b_727_;
}
else
{
lean_object* v___x_729_; uint32_t v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_729_ = l_Subarray_get___redArg(v_fst_724_, v_a_726_);
v___x_730_ = lean_unbox_uint32(v___x_729_);
lean_dec(v___x_729_);
lean_inc(v_a_726_);
v___x_731_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(v_b_727_, v_a_726_, v___x_730_);
v___x_732_ = lean_unsigned_to_nat(1u);
v___x_733_ = lean_nat_add(v_a_726_, v___x_732_);
lean_dec(v_a_726_);
v_a_726_ = v___x_733_;
v_b_727_ = v___x_731_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg___boxed(lean_object* v_upperBound_735_, lean_object* v___x_736_, lean_object* v_fst_737_, lean_object* v___x_738_, lean_object* v_a_739_, lean_object* v_b_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(v_upperBound_735_, v___x_736_, v_fst_737_, v___x_738_, v_a_739_, v_b_740_);
lean_dec(v___x_738_);
lean_dec_ref(v_fst_737_);
lean_dec(v___x_736_);
lean_dec(v_upperBound_735_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(lean_object* v_as_x27_742_, lean_object* v_b_743_){
_start:
{
if (lean_obj_tag(v_as_x27_742_) == 0)
{
return v_b_743_;
}
else
{
lean_object* v_head_744_; lean_object* v_snd_745_; lean_object* v_leftIndex_746_; 
v_head_744_ = lean_ctor_get(v_as_x27_742_, 0);
v_snd_745_ = lean_ctor_get(v_head_744_, 1);
v_leftIndex_746_ = lean_ctor_get(v_snd_745_, 1);
if (lean_obj_tag(v_leftIndex_746_) == 1)
{
lean_object* v_rightIndex_747_; 
v_rightIndex_747_ = lean_ctor_get(v_snd_745_, 3);
if (lean_obj_tag(v_rightIndex_747_) == 1)
{
if (lean_obj_tag(v_b_743_) == 0)
{
lean_object* v_tail_748_; lean_object* v_fst_749_; lean_object* v_leftCount_750_; lean_object* v_rightCount_751_; lean_object* v_val_752_; lean_object* v_val_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v_tail_748_ = lean_ctor_get(v_as_x27_742_, 1);
v_fst_749_ = lean_ctor_get(v_head_744_, 0);
v_leftCount_750_ = lean_ctor_get(v_snd_745_, 0);
v_rightCount_751_ = lean_ctor_get(v_snd_745_, 2);
v_val_752_ = lean_ctor_get(v_leftIndex_746_, 0);
v_val_753_ = lean_ctor_get(v_rightIndex_747_, 0);
v___x_754_ = lean_nat_add(v_leftCount_750_, v_rightCount_751_);
lean_inc(v_val_753_);
lean_inc(v_val_752_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v_val_752_);
lean_ctor_set(v___x_755_, 1, v_val_753_);
lean_inc(v_fst_749_);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v_fst_749_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v___x_754_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_758_, 0, v___x_757_);
v_as_x27_742_ = v_tail_748_;
v_b_743_ = v___x_758_;
goto _start;
}
else
{
lean_object* v_val_760_; lean_object* v_tail_761_; lean_object* v_fst_762_; lean_object* v_leftCount_763_; lean_object* v_rightCount_764_; lean_object* v_val_765_; lean_object* v_val_766_; lean_object* v_fst_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_788_; 
v_val_760_ = lean_ctor_get(v_b_743_, 0);
lean_inc(v_val_760_);
v_tail_761_ = lean_ctor_get(v_as_x27_742_, 1);
v_fst_762_ = lean_ctor_get(v_head_744_, 0);
v_leftCount_763_ = lean_ctor_get(v_snd_745_, 0);
v_rightCount_764_ = lean_ctor_get(v_snd_745_, 2);
v_val_765_ = lean_ctor_get(v_leftIndex_746_, 0);
v_val_766_ = lean_ctor_get(v_rightIndex_747_, 0);
v_fst_767_ = lean_ctor_get(v_val_760_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v_val_760_);
if (v_isSharedCheck_788_ == 0)
{
lean_object* v_unused_789_; 
v_unused_789_ = lean_ctor_get(v_val_760_, 1);
lean_dec(v_unused_789_);
v___x_769_ = v_val_760_;
v_isShared_770_ = v_isSharedCheck_788_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_fst_767_);
lean_dec(v_val_760_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_788_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v___x_771_; uint8_t v___x_772_; 
v___x_771_ = lean_nat_add(v_leftCount_763_, v_rightCount_764_);
v___x_772_ = lean_nat_dec_lt(v___x_771_, v_fst_767_);
lean_dec(v_fst_767_);
if (v___x_772_ == 0)
{
lean_dec(v___x_771_);
lean_del_object(v___x_769_);
v_as_x27_742_ = v_tail_761_;
goto _start;
}
else
{
lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_786_; 
v_isSharedCheck_786_ = !lean_is_exclusive(v_b_743_);
if (v_isSharedCheck_786_ == 0)
{
lean_object* v_unused_787_; 
v_unused_787_ = lean_ctor_get(v_b_743_, 0);
lean_dec(v_unused_787_);
v___x_775_ = v_b_743_;
v_isShared_776_ = v_isSharedCheck_786_;
goto v_resetjp_774_;
}
else
{
lean_dec(v_b_743_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_786_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
lean_inc(v_val_766_);
lean_inc(v_val_765_);
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 1, v_val_766_);
lean_ctor_set(v___x_769_, 0, v_val_765_);
v___x_778_ = v___x_769_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_val_765_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_val_766_);
v___x_778_ = v_reuseFailAlloc_785_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_782_; 
lean_inc(v_fst_762_);
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v_fst_762_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_771_);
lean_ctor_set(v___x_780_, 1, v___x_779_);
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v___x_780_);
v___x_782_ = v___x_775_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_784_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
v_as_x27_742_ = v_tail_761_;
v_b_743_ = v___x_782_;
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
lean_object* v_tail_790_; 
v_tail_790_ = lean_ctor_get(v_as_x27_742_, 1);
v_as_x27_742_ = v_tail_790_;
goto _start;
}
}
else
{
lean_object* v_tail_792_; 
v_tail_792_ = lean_ctor_get(v_as_x27_742_, 1);
v_as_x27_742_ = v_tail_792_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_as_x27_794_, lean_object* v_b_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(v_as_x27_794_, v_b_795_);
lean_dec(v_as_x27_794_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(lean_object* v_a_797_, lean_object* v_b_798_){
_start:
{
lean_object* v_array_799_; lean_object* v_start_800_; lean_object* v_stop_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_814_; 
v_array_799_ = lean_ctor_get(v_a_797_, 0);
v_start_800_ = lean_ctor_get(v_a_797_, 1);
v_stop_801_ = lean_ctor_get(v_a_797_, 2);
v_isSharedCheck_814_ = !lean_is_exclusive(v_a_797_);
if (v_isSharedCheck_814_ == 0)
{
v___x_803_ = v_a_797_;
v_isShared_804_ = v_isSharedCheck_814_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_stop_801_);
lean_inc(v_start_800_);
lean_inc(v_array_799_);
lean_dec(v_a_797_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_814_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
uint8_t v___x_805_; 
v___x_805_ = lean_nat_dec_lt(v_start_800_, v_stop_801_);
if (v___x_805_ == 0)
{
lean_del_object(v___x_803_);
lean_dec(v_stop_801_);
lean_dec(v_start_800_);
lean_dec_ref(v_array_799_);
return v_b_798_;
}
else
{
lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_809_; 
v___x_806_ = lean_unsigned_to_nat(1u);
v___x_807_ = lean_nat_add(v_start_800_, v___x_806_);
lean_inc_ref(v_array_799_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 1, v___x_807_);
v___x_809_ = v___x_803_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_array_799_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v_stop_801_);
v___x_809_ = v_reuseFailAlloc_813_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_array_fget(v_array_799_, v_start_800_);
lean_dec(v_start_800_);
lean_dec_ref(v_array_799_);
v___x_811_ = lean_array_push(v_b_798_, v___x_810_);
v_a_797_ = v___x_809_;
v_b_798_ = v___x_811_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8(lean_object* v_left_815_, lean_object* v_right_816_, lean_object* v_i_817_){
_start:
{
lean_object* v_start_818_; lean_object* v_stop_819_; lean_object* v_start_820_; lean_object* v_stop_821_; lean_object* v___x_822_; uint8_t v___x_823_; lean_object* v___x_824_; uint8_t v___y_826_; 
v_start_818_ = lean_ctor_get(v_left_815_, 1);
v_stop_819_ = lean_ctor_get(v_left_815_, 2);
v_start_820_ = lean_ctor_get(v_right_816_, 1);
v_stop_821_ = lean_ctor_get(v_right_816_, 2);
v___x_822_ = lean_nat_sub(v_stop_819_, v_start_818_);
v___x_823_ = lean_nat_dec_lt(v_i_817_, v___x_822_);
v___x_824_ = lean_nat_sub(v_stop_821_, v_start_820_);
if (v___x_823_ == 0)
{
v___y_826_ = v___x_823_;
goto v___jp_825_;
}
else
{
uint8_t v___x_855_; 
v___x_855_ = lean_nat_dec_lt(v_i_817_, v___x_824_);
v___y_826_ = v___x_855_;
goto v___jp_825_;
}
v___jp_825_:
{
if (v___y_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_827_ = lean_nat_sub(v___x_822_, v_i_817_);
lean_dec(v___x_822_);
lean_inc_ref(v_left_815_);
v___x_828_ = l_Subarray_take___redArg(v_left_815_, v___x_827_);
v___x_829_ = lean_nat_sub(v___x_824_, v_i_817_);
lean_dec(v_i_817_);
lean_dec(v___x_824_);
v___x_830_ = l_Subarray_take___redArg(v_right_816_, v___x_829_);
lean_dec(v___x_829_);
v___x_831_ = l_Subarray_drop___redArg(v_left_815_, v___x_827_);
lean_dec(v___x_827_);
v___x_832_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_833_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(v___x_831_, v___x_832_);
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_830_);
lean_ctor_set(v___x_834_, 1, v___x_833_);
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_828_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
return v___x_835_;
}
else
{
lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; uint32_t v___x_843_; uint32_t v___x_844_; uint8_t v___x_845_; 
v___x_836_ = lean_nat_sub(v___x_822_, v_i_817_);
lean_dec(v___x_822_);
v___x_837_ = lean_unsigned_to_nat(1u);
v___x_838_ = lean_nat_sub(v___x_836_, v___x_837_);
v___x_839_ = l_Subarray_get___redArg(v_left_815_, v___x_838_);
lean_dec(v___x_838_);
v___x_840_ = lean_nat_sub(v___x_824_, v_i_817_);
lean_dec(v___x_824_);
v___x_841_ = lean_nat_sub(v___x_840_, v___x_837_);
v___x_842_ = l_Subarray_get___redArg(v_right_816_, v___x_841_);
lean_dec(v___x_841_);
v___x_843_ = lean_unbox_uint32(v___x_839_);
lean_dec(v___x_839_);
v___x_844_ = lean_unbox_uint32(v___x_842_);
lean_dec(v___x_842_);
v___x_845_ = lean_uint32_dec_eq(v___x_843_, v___x_844_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec(v_i_817_);
lean_inc_ref(v_left_815_);
v___x_846_ = l_Subarray_take___redArg(v_left_815_, v___x_836_);
v___x_847_ = l_Subarray_take___redArg(v_right_816_, v___x_840_);
lean_dec(v___x_840_);
v___x_848_ = l_Subarray_drop___redArg(v_left_815_, v___x_836_);
lean_dec(v___x_836_);
v___x_849_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_850_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(v___x_848_, v___x_849_);
v___x_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_847_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
v___x_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_846_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
return v___x_852_;
}
else
{
lean_object* v___x_853_; 
lean_dec(v___x_840_);
lean_dec(v___x_836_);
v___x_853_ = lean_nat_add(v_i_817_, v___x_837_);
lean_dec(v_i_817_);
v_i_817_ = v___x_853_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6(lean_object* v_left_856_, lean_object* v_right_857_){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_unsigned_to_nat(0u);
v___x_859_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8(v_left_856_, v_right_857_, v___x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(lean_object* v_x_860_, lean_object* v_x_861_){
_start:
{
if (lean_obj_tag(v_x_861_) == 0)
{
lean_inc(v_x_860_);
return v_x_860_;
}
else
{
lean_object* v_key_862_; lean_object* v_value_863_; lean_object* v_tail_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v_key_862_ = lean_ctor_get(v_x_861_, 0);
v_value_863_ = lean_ctor_get(v_x_861_, 1);
v_tail_864_ = lean_ctor_get(v_x_861_, 2);
v___x_865_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(v_x_860_, v_tail_864_);
lean_inc(v_value_863_);
lean_inc(v_key_862_);
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v_key_862_);
lean_ctor_set(v___x_866_, 1, v_value_863_);
v___x_867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_866_);
lean_ctor_set(v___x_867_, 1, v___x_865_);
return v___x_867_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8___boxed(lean_object* v_x_868_, lean_object* v_x_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(v_x_868_, v_x_869_);
lean_dec(v_x_869_);
lean_dec(v_x_868_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9(lean_object* v_as_871_, size_t v_i_872_, size_t v_stop_873_, lean_object* v_b_874_){
_start:
{
uint8_t v___x_875_; 
v___x_875_ = lean_usize_dec_eq(v_i_872_, v_stop_873_);
if (v___x_875_ == 0)
{
size_t v___x_876_; size_t v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_876_ = ((size_t)1ULL);
v___x_877_ = lean_usize_sub(v_i_872_, v___x_876_);
v___x_878_ = lean_array_uget_borrowed(v_as_871_, v___x_877_);
v___x_879_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(v_b_874_, v___x_878_);
lean_dec(v_b_874_);
v_i_872_ = v___x_877_;
v_b_874_ = v___x_879_;
goto _start;
}
else
{
return v_b_874_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9___boxed(lean_object* v_as_881_, lean_object* v_i_882_, lean_object* v_stop_883_, lean_object* v_b_884_){
_start:
{
size_t v_i_boxed_885_; size_t v_stop_boxed_886_; lean_object* v_res_887_; 
v_i_boxed_885_ = lean_unbox_usize(v_i_882_);
lean_dec(v_i_882_);
v_stop_boxed_886_ = lean_unbox_usize(v_stop_883_);
lean_dec(v_stop_883_);
v_res_887_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9(v_as_881_, v_i_boxed_885_, v_stop_boxed_886_, v_b_884_);
lean_dec_ref(v_as_881_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5_spec__6(lean_object* v_left_888_, lean_object* v_right_889_, lean_object* v_pref_890_){
_start:
{
lean_object* v_start_891_; lean_object* v_stop_892_; lean_object* v_start_893_; lean_object* v_stop_894_; lean_object* v_i_895_; uint8_t v___y_897_; lean_object* v___x_913_; uint8_t v___x_914_; 
v_start_891_ = lean_ctor_get(v_left_888_, 1);
v_stop_892_ = lean_ctor_get(v_left_888_, 2);
v_start_893_ = lean_ctor_get(v_right_889_, 1);
v_stop_894_ = lean_ctor_get(v_right_889_, 2);
v_i_895_ = lean_array_get_size(v_pref_890_);
v___x_913_ = lean_nat_sub(v_stop_892_, v_start_891_);
v___x_914_ = lean_nat_dec_lt(v_i_895_, v___x_913_);
lean_dec(v___x_913_);
if (v___x_914_ == 0)
{
v___y_897_ = v___x_914_;
goto v___jp_896_;
}
else
{
lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_915_ = lean_nat_sub(v_stop_894_, v_start_893_);
v___x_916_ = lean_nat_dec_lt(v_i_895_, v___x_915_);
lean_dec(v___x_915_);
v___y_897_ = v___x_916_;
goto v___jp_896_;
}
v___jp_896_:
{
if (v___y_897_ == 0)
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_898_ = l_Subarray_drop___redArg(v_left_888_, v_i_895_);
v___x_899_ = l_Subarray_drop___redArg(v_right_889_, v_i_895_);
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_898_);
lean_ctor_set(v___x_900_, 1, v___x_899_);
v___x_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_901_, 0, v_pref_890_);
lean_ctor_set(v___x_901_, 1, v___x_900_);
return v___x_901_;
}
else
{
lean_object* v___x_902_; lean_object* v___x_903_; uint32_t v___x_904_; uint32_t v___x_905_; uint8_t v___x_906_; 
v___x_902_ = l_Subarray_get___redArg(v_left_888_, v_i_895_);
v___x_903_ = l_Subarray_get___redArg(v_right_889_, v_i_895_);
v___x_904_ = lean_unbox_uint32(v___x_902_);
v___x_905_ = lean_unbox_uint32(v___x_903_);
lean_dec(v___x_903_);
v___x_906_ = lean_uint32_dec_eq(v___x_904_, v___x_905_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
lean_dec(v___x_902_);
v___x_907_ = l_Subarray_drop___redArg(v_left_888_, v_i_895_);
v___x_908_ = l_Subarray_drop___redArg(v_right_889_, v_i_895_);
v___x_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v_pref_890_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
return v___x_910_;
}
else
{
lean_object* v___x_911_; 
v___x_911_ = lean_array_push(v_pref_890_, v___x_902_);
v_pref_890_ = v___x_911_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5(lean_object* v_left_917_, lean_object* v_right_918_){
_start:
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_920_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5_spec__6(v_left_917_, v_right_918_, v___x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(lean_object* v_histogram_921_, lean_object* v_index_922_, uint32_t v_val_923_){
_start:
{
lean_object* v___x_924_; 
v___x_924_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_histogram_921_, v_val_923_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_925_ = lean_unsigned_to_nat(1u);
v___x_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_926_, 0, v_index_922_);
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = lean_box(0);
v___x_929_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_929_, 0, v___x_925_);
lean_ctor_set(v___x_929_, 1, v___x_926_);
lean_ctor_set(v___x_929_, 2, v___x_927_);
lean_ctor_set(v___x_929_, 3, v___x_928_);
v___x_930_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_921_, v_val_923_, v___x_929_);
return v___x_930_;
}
else
{
lean_object* v_val_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_952_; 
v_val_931_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_952_ == 0)
{
v___x_933_ = v___x_924_;
v_isShared_934_ = v_isSharedCheck_952_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_val_931_);
lean_dec(v___x_924_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_952_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v_leftCount_935_; lean_object* v_rightCount_936_; lean_object* v_rightIndex_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_950_; 
v_leftCount_935_ = lean_ctor_get(v_val_931_, 0);
v_rightCount_936_ = lean_ctor_get(v_val_931_, 2);
v_rightIndex_937_ = lean_ctor_get(v_val_931_, 3);
v_isSharedCheck_950_ = !lean_is_exclusive(v_val_931_);
if (v_isSharedCheck_950_ == 0)
{
lean_object* v_unused_951_; 
v_unused_951_ = lean_ctor_get(v_val_931_, 1);
lean_dec(v_unused_951_);
v___x_939_ = v_val_931_;
v_isShared_940_ = v_isSharedCheck_950_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_rightIndex_937_);
lean_inc(v_rightCount_936_);
lean_inc(v_leftCount_935_);
lean_dec(v_val_931_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_950_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_944_; 
v___x_941_ = lean_unsigned_to_nat(1u);
v___x_942_ = lean_nat_add(v_leftCount_935_, v___x_941_);
lean_dec(v_leftCount_935_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v_index_922_);
v___x_944_ = v___x_933_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_index_922_);
v___x_944_ = v_reuseFailAlloc_949_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
lean_object* v___x_946_; 
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_944_);
lean_ctor_set(v___x_939_, 0, v___x_942_);
v___x_946_ = v___x_939_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_948_, 2, v_rightCount_936_);
lean_ctor_set(v_reuseFailAlloc_948_, 3, v_rightIndex_937_);
v___x_946_ = v_reuseFailAlloc_948_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
lean_object* v___x_947_; 
v___x_947_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_921_, v_val_923_, v___x_946_);
return v___x_947_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg___boxed(lean_object* v_histogram_953_, lean_object* v_index_954_, lean_object* v_val_955_){
_start:
{
uint32_t v_val_boxed_956_; lean_object* v_res_957_; 
v_val_boxed_956_ = lean_unbox_uint32(v_val_955_);
lean_dec(v_val_955_);
v_res_957_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(v_histogram_953_, v_index_954_, v_val_boxed_956_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(lean_object* v_upperBound_958_, lean_object* v_fst_959_, lean_object* v___x_960_, lean_object* v_fst_961_, lean_object* v_a_962_, lean_object* v_b_963_){
_start:
{
uint8_t v___x_964_; 
v___x_964_ = lean_nat_dec_lt(v_a_962_, v_upperBound_958_);
if (v___x_964_ == 0)
{
lean_dec(v_a_962_);
return v_b_963_;
}
else
{
lean_object* v___x_965_; uint32_t v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_965_ = l_Subarray_get___redArg(v_fst_961_, v_a_962_);
v___x_966_ = lean_unbox_uint32(v___x_965_);
lean_dec(v___x_965_);
lean_inc(v_a_962_);
v___x_967_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(v_b_963_, v_a_962_, v___x_966_);
v___x_968_ = lean_unsigned_to_nat(1u);
v___x_969_ = lean_nat_add(v_a_962_, v___x_968_);
lean_dec(v_a_962_);
v_a_962_ = v___x_969_;
v_b_963_ = v___x_967_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg___boxed(lean_object* v_upperBound_971_, lean_object* v_fst_972_, lean_object* v___x_973_, lean_object* v_fst_974_, lean_object* v_a_975_, lean_object* v_b_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(v_upperBound_971_, v_fst_972_, v___x_973_, v_fst_974_, v_a_975_, v_b_976_);
lean_dec_ref(v_fst_974_);
lean_dec(v___x_973_);
lean_dec_ref(v_fst_972_);
lean_dec(v_upperBound_971_);
return v_res_977_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_978_ = lean_box(0);
v___x_979_ = lean_unsigned_to_nat(16u);
v___x_980_ = lean_mk_array(v___x_979_, v___x_978_);
return v___x_980_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v_hist_983_; 
v___x_981_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0);
v___x_982_ = lean_unsigned_to_nat(0u);
v_hist_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_983_, 0, v___x_982_);
lean_ctor_set(v_hist_983_, 1, v___x_981_);
return v_hist_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(lean_object* v_left_984_, lean_object* v_right_985_){
_start:
{
lean_object* v___x_986_; lean_object* v_snd_987_; lean_object* v_fst_988_; lean_object* v_fst_989_; lean_object* v_snd_990_; lean_object* v___x_991_; lean_object* v_snd_992_; lean_object* v_fst_993_; lean_object* v_fst_994_; lean_object* v_snd_995_; lean_object* v_start_996_; lean_object* v_stop_997_; lean_object* v___x_998_; lean_object* v_hist_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v_start_1002_; lean_object* v_stop_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v_buckets_1006_; lean_object* v___x_1007_; lean_object* v___y_1009_; lean_object* v___x_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v___x_986_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5(v_left_984_, v_right_985_);
v_snd_987_ = lean_ctor_get(v___x_986_, 1);
lean_inc(v_snd_987_);
v_fst_988_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_fst_988_);
lean_dec_ref(v___x_986_);
v_fst_989_ = lean_ctor_get(v_snd_987_, 0);
lean_inc(v_fst_989_);
v_snd_990_ = lean_ctor_get(v_snd_987_, 1);
lean_inc(v_snd_990_);
lean_dec(v_snd_987_);
v___x_991_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6(v_fst_989_, v_snd_990_);
v_snd_992_ = lean_ctor_get(v___x_991_, 1);
lean_inc(v_snd_992_);
v_fst_993_ = lean_ctor_get(v___x_991_, 0);
lean_inc(v_fst_993_);
lean_dec_ref(v___x_991_);
v_fst_994_ = lean_ctor_get(v_snd_992_, 0);
lean_inc(v_fst_994_);
v_snd_995_ = lean_ctor_get(v_snd_992_, 1);
lean_inc(v_snd_995_);
lean_dec(v_snd_992_);
v_start_996_ = lean_ctor_get(v_fst_993_, 1);
v_stop_997_ = lean_ctor_get(v_fst_993_, 2);
v___x_998_ = lean_unsigned_to_nat(0u);
v_hist_999_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1);
v___x_1000_ = lean_nat_sub(v_stop_997_, v_start_996_);
v___x_1001_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(v___x_1000_, v_fst_994_, v___x_1000_, v_fst_993_, v___x_998_, v_hist_999_);
v_start_1002_ = lean_ctor_get(v_fst_994_, 1);
v_stop_1003_ = lean_ctor_get(v_fst_994_, 2);
v___x_1004_ = lean_nat_sub(v_stop_1003_, v_start_1002_);
v___x_1005_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(v___x_1004_, v___x_1004_, v_fst_994_, v___x_1000_, v___x_998_, v___x_1001_);
lean_dec(v___x_1000_);
lean_dec(v___x_1004_);
v_buckets_1006_ = lean_ctor_get(v___x_1005_, 1);
lean_inc_ref(v_buckets_1006_);
lean_dec_ref(v___x_1005_);
v___x_1007_ = lean_box(0);
v___x_1035_ = lean_box(0);
v___x_1036_ = lean_array_get_size(v_buckets_1006_);
v___x_1037_ = lean_nat_dec_lt(v___x_998_, v___x_1036_);
if (v___x_1037_ == 0)
{
lean_dec_ref(v_buckets_1006_);
v___y_1009_ = v___x_1035_;
goto v___jp_1008_;
}
else
{
size_t v___x_1038_; size_t v___x_1039_; lean_object* v___x_1040_; 
v___x_1038_ = lean_usize_of_nat(v___x_1036_);
v___x_1039_ = ((size_t)0ULL);
v___x_1040_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9(v_buckets_1006_, v___x_1038_, v___x_1039_, v___x_1035_);
lean_dec_ref(v_buckets_1006_);
v___y_1009_ = v___x_1040_;
goto v___jp_1008_;
}
v___jp_1008_:
{
lean_object* v___x_1010_; 
v___x_1010_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(v___y_1009_, v___x_1007_);
lean_dec(v___y_1009_);
if (lean_obj_tag(v___x_1010_) == 1)
{
lean_object* v_val_1011_; lean_object* v_snd_1012_; lean_object* v_snd_1013_; lean_object* v_fst_1014_; lean_object* v_fst_1015_; lean_object* v_snd_1016_; lean_object* v___x_1017_; lean_object* v_fst_1018_; lean_object* v_snd_1019_; lean_object* v___x_1020_; lean_object* v_fst_1021_; lean_object* v_snd_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v_val_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_val_1011_);
lean_dec_ref_known(v___x_1010_, 1);
v_snd_1012_ = lean_ctor_get(v_val_1011_, 1);
lean_inc(v_snd_1012_);
lean_dec(v_val_1011_);
v_snd_1013_ = lean_ctor_get(v_snd_1012_, 1);
lean_inc(v_snd_1013_);
v_fst_1014_ = lean_ctor_get(v_snd_1012_, 0);
lean_inc(v_fst_1014_);
lean_dec(v_snd_1012_);
v_fst_1015_ = lean_ctor_get(v_snd_1013_, 0);
lean_inc(v_fst_1015_);
v_snd_1016_ = lean_ctor_get(v_snd_1013_, 1);
lean_inc(v_snd_1016_);
lean_dec(v_snd_1013_);
v___x_1017_ = l_Subarray_split___redArg(v_fst_993_, v_fst_1015_);
lean_dec(v_fst_1015_);
v_fst_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_fst_1018_);
v_snd_1019_ = lean_ctor_get(v___x_1017_, 1);
lean_inc(v_snd_1019_);
lean_dec_ref(v___x_1017_);
v___x_1020_ = l_Subarray_split___redArg(v_fst_994_, v_snd_1016_);
lean_dec(v_snd_1016_);
v_fst_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_fst_1021_);
v_snd_1022_ = lean_ctor_get(v___x_1020_, 1);
lean_inc(v_snd_1022_);
lean_dec_ref(v___x_1020_);
v___x_1023_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v_fst_1018_, v_fst_1021_);
v___x_1024_ = l_Array_append___redArg(v_fst_988_, v___x_1023_);
lean_dec_ref(v___x_1023_);
v___x_1025_ = lean_unsigned_to_nat(1u);
v___x_1026_ = lean_mk_empty_array_with_capacity(v___x_1025_);
v___x_1027_ = lean_array_push(v___x_1026_, v_fst_1014_);
v___x_1028_ = l_Array_append___redArg(v___x_1024_, v___x_1027_);
lean_dec_ref(v___x_1027_);
v___x_1029_ = l_Subarray_drop___redArg(v_snd_1019_, v___x_1025_);
v___x_1030_ = l_Subarray_drop___redArg(v_snd_1022_, v___x_1025_);
v___x_1031_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v___x_1029_, v___x_1030_);
v___x_1032_ = l_Array_append___redArg(v___x_1028_, v___x_1031_);
lean_dec_ref(v___x_1031_);
v___x_1033_ = l_Array_append___redArg(v___x_1032_, v_snd_995_);
lean_dec(v_snd_995_);
return v___x_1033_;
}
else
{
lean_object* v___x_1034_; 
lean_dec(v___x_1010_);
lean_dec(v_fst_994_);
lean_dec(v_fst_993_);
v___x_1034_ = l_Array_append___redArg(v_fst_988_, v_snd_995_);
lean_dec(v_snd_995_);
return v___x_1034_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(lean_object* v___x_1041_, lean_object* v_edited_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_fst_1044_; lean_object* v_snd_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1064_; 
v_fst_1044_ = lean_ctor_get(v_a_1043_, 0);
v_snd_1045_ = lean_ctor_get(v_a_1043_, 1);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_a_1043_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1047_ = v_a_1043_;
v_isShared_1048_ = v_isSharedCheck_1064_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_snd_1045_);
lean_inc(v_fst_1044_);
lean_dec(v_a_1043_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1064_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
uint8_t v___x_1049_; 
v___x_1049_ = lean_nat_dec_lt(v_snd_1045_, v___x_1041_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1051_; 
if (v_isShared_1048_ == 0)
{
v___x_1051_ = v___x_1047_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_fst_1044_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_snd_1045_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
else
{
uint8_t v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1053_ = 0;
v___x_1054_ = lean_array_fget_borrowed(v_edited_1042_, v_snd_1045_);
v___x_1055_ = lean_box(v___x_1053_);
lean_inc(v___x_1054_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 1, v___x_1054_);
lean_ctor_set(v___x_1047_, 0, v___x_1055_);
v___x_1057_ = v___x_1047_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1063_, 1, v___x_1054_);
v___x_1057_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1058_ = lean_array_push(v_fst_1044_, v___x_1057_);
v___x_1059_ = lean_unsigned_to_nat(1u);
v___x_1060_ = lean_nat_add(v_snd_1045_, v___x_1059_);
lean_dec(v_snd_1045_);
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1058_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v_a_1043_ = v___x_1061_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg___boxed(lean_object* v___x_1065_, lean_object* v_edited_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1065_, v_edited_1066_, v_a_1067_);
lean_dec_ref(v_edited_1066_);
lean_dec(v___x_1065_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(size_t v_sz_1069_, size_t v_i_1070_, lean_object* v_bs_1071_){
_start:
{
uint8_t v___x_1072_; 
v___x_1072_ = lean_usize_dec_lt(v_i_1070_, v_sz_1069_);
if (v___x_1072_ == 0)
{
return v_bs_1071_;
}
else
{
lean_object* v_v_1073_; lean_object* v___x_1074_; lean_object* v_bs_x27_1075_; uint8_t v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; size_t v___x_1079_; size_t v___x_1080_; lean_object* v___x_1081_; 
v_v_1073_ = lean_array_uget(v_bs_1071_, v_i_1070_);
v___x_1074_ = lean_unsigned_to_nat(0u);
v_bs_x27_1075_ = lean_array_uset(v_bs_1071_, v_i_1070_, v___x_1074_);
v___x_1076_ = 1;
v___x_1077_ = lean_box(v___x_1076_);
v___x_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v_v_1073_);
v___x_1079_ = ((size_t)1ULL);
v___x_1080_ = lean_usize_add(v_i_1070_, v___x_1079_);
v___x_1081_ = lean_array_uset(v_bs_x27_1075_, v_i_1070_, v___x_1078_);
v_i_1070_ = v___x_1080_;
v_bs_1071_ = v___x_1081_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8___boxed(lean_object* v_sz_1083_, lean_object* v_i_1084_, lean_object* v_bs_1085_){
_start:
{
size_t v_sz_boxed_1086_; size_t v_i_boxed_1087_; lean_object* v_res_1088_; 
v_sz_boxed_1086_ = lean_unbox_usize(v_sz_1083_);
lean_dec(v_sz_1083_);
v_i_boxed_1087_ = lean_unbox_usize(v_i_1084_);
lean_dec(v_i_1084_);
v_res_1088_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(v_sz_boxed_1086_, v_i_boxed_1087_, v_bs_1085_);
return v_res_1088_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_1089_; lean_object* v___x_1090_; 
v___x_1089_ = 65;
v___x_1090_ = lean_box_uint32(v___x_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(lean_object* v___x_1091_, lean_object* v_original_1092_, uint32_t v_a_1093_, lean_object* v_a_1094_){
_start:
{
lean_object* v_fst_1095_; lean_object* v_snd_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1121_; 
v_fst_1095_ = lean_ctor_get(v_a_1094_, 0);
v_snd_1096_ = lean_ctor_get(v_a_1094_, 1);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_a_1094_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1098_ = v_a_1094_;
v_isShared_1099_ = v_isSharedCheck_1121_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_snd_1096_);
lean_inc(v_fst_1095_);
lean_dec(v_a_1094_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1121_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
uint8_t v___x_1100_; 
v___x_1100_ = lean_nat_dec_lt(v_snd_1096_, v___x_1091_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1102_; 
if (v_isShared_1099_ == 0)
{
v___x_1102_ = v___x_1098_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_fst_1095_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v_snd_1096_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
else
{
lean_object* v___x_1104_; lean_object* v___x_1105_; uint32_t v___x_1106_; uint8_t v___x_1107_; 
v___x_1104_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed__const__1;
v___x_1105_ = lean_array_get_borrowed(v___x_1104_, v_original_1092_, v_snd_1096_);
v___x_1106_ = lean_unbox_uint32(v___x_1105_);
v___x_1107_ = lean_uint32_dec_eq(v___x_1106_, v_a_1093_);
if (v___x_1107_ == 0)
{
uint8_t v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1108_ = 1;
v___x_1109_ = lean_box(v___x_1108_);
lean_inc(v___x_1105_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 1, v___x_1105_);
lean_ctor_set(v___x_1098_, 0, v___x_1109_);
v___x_1111_ = v___x_1098_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v___x_1105_);
v___x_1111_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1112_ = lean_array_push(v_fst_1095_, v___x_1111_);
v___x_1113_ = lean_unsigned_to_nat(1u);
v___x_1114_ = lean_nat_add(v_snd_1096_, v___x_1113_);
lean_dec(v_snd_1096_);
v___x_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1112_);
lean_ctor_set(v___x_1115_, 1, v___x_1114_);
v_a_1094_ = v___x_1115_;
goto _start;
}
}
else
{
lean_object* v___x_1119_; 
if (v_isShared_1099_ == 0)
{
v___x_1119_ = v___x_1098_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_fst_1095_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_snd_1096_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed(lean_object* v___x_1122_, lean_object* v_original_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
uint32_t v_a_boxed_1126_; lean_object* v_res_1127_; 
v_a_boxed_1126_ = lean_unbox_uint32(v_a_1124_);
lean_dec(v_a_1124_);
v_res_1127_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1122_, v_original_1123_, v_a_boxed_1126_, v_a_1125_);
lean_dec_ref(v_original_1123_);
lean_dec(v___x_1122_);
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(lean_object* v___x_1128_, lean_object* v_edited_1129_, uint32_t v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v_fst_1132_; lean_object* v_snd_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1158_; 
v_fst_1132_ = lean_ctor_get(v_a_1131_, 0);
v_snd_1133_ = lean_ctor_get(v_a_1131_, 1);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_a_1131_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1135_ = v_a_1131_;
v_isShared_1136_ = v_isSharedCheck_1158_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_snd_1133_);
lean_inc(v_fst_1132_);
lean_dec(v_a_1131_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1158_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
uint8_t v___x_1137_; 
v___x_1137_ = lean_nat_dec_lt(v_snd_1133_, v___x_1128_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1139_; 
if (v_isShared_1136_ == 0)
{
v___x_1139_ = v___x_1135_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_fst_1132_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_snd_1133_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1142_; uint32_t v___x_1143_; uint8_t v___x_1144_; 
v___x_1141_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed__const__1;
v___x_1142_ = lean_array_get_borrowed(v___x_1141_, v_edited_1129_, v_snd_1133_);
v___x_1143_ = lean_unbox_uint32(v___x_1142_);
v___x_1144_ = lean_uint32_dec_eq(v___x_1143_, v_a_1130_);
if (v___x_1144_ == 0)
{
uint8_t v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1148_; 
v___x_1145_ = 0;
v___x_1146_ = lean_box(v___x_1145_);
lean_inc(v___x_1142_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 1, v___x_1142_);
lean_ctor_set(v___x_1135_, 0, v___x_1146_);
v___x_1148_ = v___x_1135_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1146_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v___x_1142_);
v___x_1148_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1149_ = lean_array_push(v_fst_1132_, v___x_1148_);
v___x_1150_ = lean_unsigned_to_nat(1u);
v___x_1151_ = lean_nat_add(v_snd_1133_, v___x_1150_);
lean_dec(v_snd_1133_);
v___x_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1149_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v_a_1131_ = v___x_1152_;
goto _start;
}
}
else
{
lean_object* v___x_1156_; 
if (v_isShared_1136_ == 0)
{
v___x_1156_ = v___x_1135_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_fst_1132_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_snd_1133_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg___boxed(lean_object* v___x_1159_, lean_object* v_edited_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
uint32_t v_a_boxed_1163_; lean_object* v_res_1164_; 
v_a_boxed_1163_ = lean_unbox_uint32(v_a_1161_);
lean_dec(v_a_1161_);
v_res_1164_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1159_, v_edited_1160_, v_a_boxed_1163_, v_a_1162_);
lean_dec_ref(v_edited_1160_);
lean_dec(v___x_1159_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(lean_object* v___x_1165_, lean_object* v_original_1166_, lean_object* v___x_1167_, lean_object* v_edited_1168_, lean_object* v_as_1169_, size_t v_sz_1170_, size_t v_i_1171_, lean_object* v_b_1172_){
_start:
{
uint8_t v___x_1173_; 
v___x_1173_ = lean_usize_dec_lt(v_i_1171_, v_sz_1170_);
if (v___x_1173_ == 0)
{
return v_b_1172_;
}
else
{
lean_object* v_snd_1174_; lean_object* v_fst_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1224_; 
v_snd_1174_ = lean_ctor_get(v_b_1172_, 1);
v_fst_1175_ = lean_ctor_get(v_b_1172_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_b_1172_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1177_ = v_b_1172_;
v_isShared_1178_ = v_isSharedCheck_1224_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_snd_1174_);
lean_inc(v_fst_1175_);
lean_dec(v_b_1172_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1224_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v_fst_1179_; lean_object* v_snd_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1223_; 
v_fst_1179_ = lean_ctor_get(v_snd_1174_, 0);
v_snd_1180_ = lean_ctor_get(v_snd_1174_, 1);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_snd_1174_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1182_ = v_snd_1174_;
v_isShared_1183_ = v_isSharedCheck_1223_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_snd_1180_);
lean_inc(v_fst_1179_);
lean_dec(v_snd_1174_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1223_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v_a_1184_; lean_object* v___x_1186_; 
v_a_1184_ = lean_array_uget_borrowed(v_as_1169_, v_i_1171_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 1, v_fst_1179_);
lean_ctor_set(v___x_1182_, 0, v_fst_1175_);
v___x_1186_ = v___x_1182_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_fst_1175_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_fst_1179_);
v___x_1186_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
uint32_t v___x_1187_; lean_object* v___x_1188_; lean_object* v_fst_1189_; lean_object* v_snd_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1221_; 
v___x_1187_ = lean_unbox_uint32(v_a_1184_);
v___x_1188_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1165_, v_original_1166_, v___x_1187_, v___x_1186_);
v_fst_1189_ = lean_ctor_get(v___x_1188_, 0);
v_snd_1190_ = lean_ctor_get(v___x_1188_, 1);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1192_ = v___x_1188_;
v_isShared_1193_ = v_isSharedCheck_1221_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_snd_1190_);
lean_inc(v_fst_1189_);
lean_dec(v___x_1188_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1221_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1195_; 
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 1, v_snd_1180_);
v___x_1195_ = v___x_1192_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_fst_1189_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v_snd_1180_);
v___x_1195_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
uint32_t v___x_1196_; lean_object* v___x_1197_; lean_object* v_fst_1198_; lean_object* v_snd_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1219_; 
v___x_1196_ = lean_unbox_uint32(v_a_1184_);
v___x_1197_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1167_, v_edited_1168_, v___x_1196_, v___x_1195_);
v_fst_1198_ = lean_ctor_get(v___x_1197_, 0);
v_snd_1199_ = lean_ctor_get(v___x_1197_, 1);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1201_ = v___x_1197_;
v_isShared_1202_ = v_isSharedCheck_1219_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_snd_1199_);
lean_inc(v_fst_1198_);
lean_dec(v___x_1197_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1219_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
uint8_t v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1203_ = 2;
v___x_1204_ = lean_box(v___x_1203_);
lean_inc(v_a_1184_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 1, v_a_1184_);
lean_ctor_set(v___x_1201_, 0, v___x_1204_);
v___x_1206_ = v___x_1201_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_a_1184_);
v___x_1206_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1207_ = lean_array_push(v_fst_1198_, v___x_1206_);
v___x_1208_ = lean_unsigned_to_nat(1u);
v___x_1209_ = lean_nat_add(v_snd_1190_, v___x_1208_);
lean_dec(v_snd_1190_);
v___x_1210_ = lean_nat_add(v_snd_1199_, v___x_1208_);
lean_dec(v_snd_1199_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v___x_1210_);
lean_ctor_set(v___x_1177_, 0, v___x_1209_);
v___x_1212_ = v___x_1177_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1213_; size_t v___x_1214_; size_t v___x_1215_; 
v___x_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1207_);
lean_ctor_set(v___x_1213_, 1, v___x_1212_);
v___x_1214_ = ((size_t)1ULL);
v___x_1215_ = lean_usize_add(v_i_1171_, v___x_1214_);
v_i_1171_ = v___x_1215_;
v_b_1172_ = v___x_1213_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15___boxed(lean_object* v___x_1225_, lean_object* v_original_1226_, lean_object* v___x_1227_, lean_object* v_edited_1228_, lean_object* v_as_1229_, lean_object* v_sz_1230_, lean_object* v_i_1231_, lean_object* v_b_1232_){
_start:
{
size_t v_sz_boxed_1233_; size_t v_i_boxed_1234_; lean_object* v_res_1235_; 
v_sz_boxed_1233_ = lean_unbox_usize(v_sz_1230_);
lean_dec(v_sz_1230_);
v_i_boxed_1234_ = lean_unbox_usize(v_i_1231_);
lean_dec(v_i_1231_);
v_res_1235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(v___x_1225_, v_original_1226_, v___x_1227_, v_edited_1228_, v_as_1229_, v_sz_boxed_1233_, v_i_boxed_1234_, v_b_1232_);
lean_dec_ref(v_as_1229_);
lean_dec_ref(v_edited_1228_);
lean_dec(v___x_1227_);
lean_dec_ref(v_original_1226_);
lean_dec(v___x_1225_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(lean_object* v___x_1236_, lean_object* v_edited_1237_, lean_object* v___x_1238_, lean_object* v_original_1239_, lean_object* v_as_1240_, size_t v_sz_1241_, size_t v_i_1242_, lean_object* v_b_1243_){
_start:
{
uint8_t v___x_1244_; 
v___x_1244_ = lean_usize_dec_lt(v_i_1242_, v_sz_1241_);
if (v___x_1244_ == 0)
{
return v_b_1243_;
}
else
{
lean_object* v_snd_1245_; lean_object* v_fst_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1295_; 
v_snd_1245_ = lean_ctor_get(v_b_1243_, 1);
v_fst_1246_ = lean_ctor_get(v_b_1243_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_b_1243_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1248_ = v_b_1243_;
v_isShared_1249_ = v_isSharedCheck_1295_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_snd_1245_);
lean_inc(v_fst_1246_);
lean_dec(v_b_1243_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1295_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v_fst_1250_; lean_object* v_snd_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1294_; 
v_fst_1250_ = lean_ctor_get(v_snd_1245_, 0);
v_snd_1251_ = lean_ctor_get(v_snd_1245_, 1);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_snd_1245_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1253_ = v_snd_1245_;
v_isShared_1254_ = v_isSharedCheck_1294_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_snd_1251_);
lean_inc(v_fst_1250_);
lean_dec(v_snd_1245_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1294_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v_a_1255_; lean_object* v___x_1257_; 
v_a_1255_ = lean_array_uget_borrowed(v_as_1240_, v_i_1242_);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 1, v_fst_1250_);
lean_ctor_set(v___x_1253_, 0, v_fst_1246_);
v___x_1257_ = v___x_1253_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_fst_1246_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v_fst_1250_);
v___x_1257_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
uint32_t v___x_1258_; lean_object* v___x_1259_; lean_object* v_fst_1260_; lean_object* v_snd_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1292_; 
v___x_1258_ = lean_unbox_uint32(v_a_1255_);
v___x_1259_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1238_, v_original_1239_, v___x_1258_, v___x_1257_);
v_fst_1260_ = lean_ctor_get(v___x_1259_, 0);
v_snd_1261_ = lean_ctor_get(v___x_1259_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1263_ = v___x_1259_;
v_isShared_1264_ = v_isSharedCheck_1292_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_snd_1261_);
lean_inc(v_fst_1260_);
lean_dec(v___x_1259_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1292_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 1, v_snd_1251_);
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_fst_1260_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_snd_1251_);
v___x_1266_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
uint32_t v___x_1267_; lean_object* v___x_1268_; lean_object* v_fst_1269_; lean_object* v_snd_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1290_; 
v___x_1267_ = lean_unbox_uint32(v_a_1255_);
v___x_1268_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1236_, v_edited_1237_, v___x_1267_, v___x_1266_);
v_fst_1269_ = lean_ctor_get(v___x_1268_, 0);
v_snd_1270_ = lean_ctor_get(v___x_1268_, 1);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1272_ = v___x_1268_;
v_isShared_1273_ = v_isSharedCheck_1290_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_snd_1270_);
lean_inc(v_fst_1269_);
lean_dec(v___x_1268_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1290_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
uint8_t v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1277_; 
v___x_1274_ = 2;
v___x_1275_ = lean_box(v___x_1274_);
lean_inc(v_a_1255_);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 1, v_a_1255_);
lean_ctor_set(v___x_1272_, 0, v___x_1275_);
v___x_1277_ = v___x_1272_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v___x_1275_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_a_1255_);
v___x_1277_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1278_ = lean_array_push(v_fst_1269_, v___x_1277_);
v___x_1279_ = lean_unsigned_to_nat(1u);
v___x_1280_ = lean_nat_add(v_snd_1261_, v___x_1279_);
lean_dec(v_snd_1261_);
v___x_1281_ = lean_nat_add(v_snd_1270_, v___x_1279_);
lean_dec(v_snd_1270_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 1, v___x_1281_);
lean_ctor_set(v___x_1248_, 0, v___x_1280_);
v___x_1283_ = v___x_1248_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1280_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1284_; size_t v___x_1285_; size_t v___x_1286_; lean_object* v___x_1287_; 
v___x_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1278_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = ((size_t)1ULL);
v___x_1286_ = lean_usize_add(v_i_1242_, v___x_1285_);
v___x_1287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(v___x_1238_, v_original_1239_, v___x_1236_, v_edited_1237_, v_as_1240_, v_sz_1241_, v___x_1286_, v___x_1284_);
return v___x_1287_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5___boxed(lean_object* v___x_1296_, lean_object* v_edited_1297_, lean_object* v___x_1298_, lean_object* v_original_1299_, lean_object* v_as_1300_, lean_object* v_sz_1301_, lean_object* v_i_1302_, lean_object* v_b_1303_){
_start:
{
size_t v_sz_boxed_1304_; size_t v_i_boxed_1305_; lean_object* v_res_1306_; 
v_sz_boxed_1304_ = lean_unbox_usize(v_sz_1301_);
lean_dec(v_sz_1301_);
v_i_boxed_1305_ = lean_unbox_usize(v_i_1302_);
lean_dec(v_i_1302_);
v_res_1306_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v___x_1296_, v_edited_1297_, v___x_1298_, v_original_1299_, v_as_1300_, v_sz_boxed_1304_, v_i_boxed_1305_, v_b_1303_);
lean_dec_ref(v_as_1300_);
lean_dec_ref(v_original_1299_);
lean_dec(v___x_1298_);
lean_dec_ref(v_edited_1297_);
lean_dec(v___x_1296_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(lean_object* v_original_1314_, lean_object* v_edited_1315_){
_start:
{
lean_object* v_i_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v_i_1316_ = lean_unsigned_to_nat(0u);
v___x_1317_ = lean_array_get_size(v_original_1314_);
v___x_1318_ = lean_nat_dec_lt(v_i_1316_, v___x_1317_);
if (v___x_1318_ == 0)
{
size_t v_sz_1319_; size_t v___x_1320_; lean_object* v___x_1321_; 
lean_dec_ref(v_original_1314_);
v_sz_1319_ = lean_array_size(v_edited_1315_);
v___x_1320_ = ((size_t)0ULL);
v___x_1321_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(v_sz_1319_, v___x_1320_, v_edited_1315_);
return v___x_1321_;
}
else
{
lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1322_ = lean_array_get_size(v_edited_1315_);
v___x_1323_ = lean_nat_dec_lt(v_i_1316_, v___x_1322_);
if (v___x_1323_ == 0)
{
size_t v_sz_1324_; size_t v___x_1325_; lean_object* v___x_1326_; 
lean_dec_ref(v_edited_1315_);
v_sz_1324_ = lean_array_size(v_original_1314_);
v___x_1325_ = ((size_t)0ULL);
v___x_1326_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(v_sz_1324_, v___x_1325_, v_original_1314_);
return v___x_1326_;
}
else
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v_ds_1329_; lean_object* v___x_1330_; size_t v_sz_1331_; size_t v___x_1332_; lean_object* v___x_1333_; lean_object* v_snd_1334_; lean_object* v_fst_1335_; lean_object* v_fst_1336_; lean_object* v_snd_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1356_; 
lean_inc_ref(v_original_1314_);
v___x_1327_ = l_Array_toSubarray___redArg(v_original_1314_, v_i_1316_, v___x_1317_);
lean_inc_ref(v_edited_1315_);
v___x_1328_ = l_Array_toSubarray___redArg(v_edited_1315_, v_i_1316_, v___x_1322_);
v_ds_1329_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v___x_1327_, v___x_1328_);
v___x_1330_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__2));
v_sz_1331_ = lean_array_size(v_ds_1329_);
v___x_1332_ = ((size_t)0ULL);
v___x_1333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v___x_1322_, v_edited_1315_, v___x_1317_, v_original_1314_, v_ds_1329_, v_sz_1331_, v___x_1332_, v___x_1330_);
lean_dec_ref(v_ds_1329_);
v_snd_1334_ = lean_ctor_get(v___x_1333_, 1);
lean_inc(v_snd_1334_);
v_fst_1335_ = lean_ctor_get(v___x_1333_, 0);
lean_inc(v_fst_1335_);
lean_dec_ref(v___x_1333_);
v_fst_1336_ = lean_ctor_get(v_snd_1334_, 0);
v_snd_1337_ = lean_ctor_get(v_snd_1334_, 1);
v_isSharedCheck_1356_ = !lean_is_exclusive(v_snd_1334_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1339_ = v_snd_1334_;
v_isShared_1340_ = v_isSharedCheck_1356_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_snd_1337_);
lean_inc(v_fst_1336_);
lean_dec(v_snd_1334_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1356_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
lean_ctor_set(v___x_1339_, 1, v_fst_1336_);
lean_ctor_set(v___x_1339_, 0, v_fst_1335_);
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_fst_1335_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_fst_1336_);
v___x_1342_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
lean_object* v___x_1343_; lean_object* v_fst_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1353_; 
v___x_1343_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_1317_, v_original_1314_, v___x_1342_);
lean_dec_ref(v_original_1314_);
v_fst_1344_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1353_ == 0)
{
lean_object* v_unused_1354_; 
v_unused_1354_ = lean_ctor_get(v___x_1343_, 1);
lean_dec(v_unused_1354_);
v___x_1346_ = v___x_1343_;
v_isShared_1347_ = v_isSharedCheck_1353_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_fst_1344_);
lean_dec(v___x_1343_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1353_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 1, v_snd_1337_);
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_fst_1344_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_snd_1337_);
v___x_1349_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
lean_object* v___x_1350_; lean_object* v_fst_1351_; 
v___x_1350_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1322_, v_edited_1315_, v___x_1349_);
lean_dec_ref(v_edited_1315_);
v_fst_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_fst_1351_);
lean_dec_ref(v___x_1350_);
return v_fst_1351_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(lean_object* v_s_1357_, lean_object* v_a_1358_, uint8_t v_b_1359_){
_start:
{
lean_object* v_str_1360_; lean_object* v_startInclusive_1361_; lean_object* v_endExclusive_1362_; lean_object* v___x_1363_; uint8_t v_decide_1364_; 
v_str_1360_ = lean_ctor_get(v_s_1357_, 0);
v_startInclusive_1361_ = lean_ctor_get(v_s_1357_, 1);
v_endExclusive_1362_ = lean_ctor_get(v_s_1357_, 2);
v___x_1363_ = lean_nat_sub(v_endExclusive_1362_, v_startInclusive_1361_);
v_decide_1364_ = lean_nat_dec_eq(v_a_1358_, v___x_1363_);
lean_dec(v___x_1363_);
if (v_decide_1364_ == 0)
{
lean_object* v___x_1365_; uint32_t v___x_1366_; uint32_t v___x_1367_; uint8_t v___x_1368_; 
v___x_1365_ = lean_nat_add(v_startInclusive_1361_, v_a_1358_);
lean_dec(v_a_1358_);
v___x_1366_ = lean_string_utf8_get_fast(v_str_1360_, v___x_1365_);
v___x_1367_ = 10;
v___x_1368_ = lean_uint32_dec_eq(v___x_1366_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = lean_string_utf8_next_fast(v_str_1360_, v___x_1365_);
lean_dec(v___x_1365_);
v___x_1370_ = lean_nat_sub(v___x_1369_, v_startInclusive_1361_);
v_a_1358_ = v___x_1370_;
v_b_1359_ = v___x_1368_;
goto _start;
}
else
{
lean_dec(v___x_1365_);
return v___x_1368_;
}
}
else
{
lean_dec(v_a_1358_);
return v_b_1359_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg___boxed(lean_object* v_s_1372_, lean_object* v_a_1373_, lean_object* v_b_1374_){
_start:
{
uint8_t v_b_boxed_1375_; uint8_t v_res_1376_; lean_object* v_r_1377_; 
v_b_boxed_1375_ = lean_unbox(v_b_1374_);
v_res_1376_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1372_, v_a_1373_, v_b_boxed_1375_);
lean_dec_ref(v_s_1372_);
v_r_1377_ = lean_box(v_res_1376_);
return v_r_1377_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(lean_object* v_s_1378_){
_start:
{
lean_object* v_searcher_1379_; uint8_t v___x_1380_; uint8_t v___x_1381_; 
v_searcher_1379_ = lean_unsigned_to_nat(0u);
v___x_1380_ = 0;
v___x_1381_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1378_, v_searcher_1379_, v___x_1380_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0___boxed(lean_object* v_s_1382_){
_start:
{
uint8_t v_res_1383_; lean_object* v_r_1384_; 
v_res_1383_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v_s_1382_);
lean_dec_ref(v_s_1382_);
v_r_1384_ = lean_box(v_res_1383_);
return v_r_1384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(lean_object* v_oldWs_1385_, lean_object* v_newWs_1386_){
_start:
{
lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; uint8_t v___x_1390_; 
v___x_1387_ = lean_unsigned_to_nat(0u);
v___x_1388_ = lean_string_utf8_byte_size(v_oldWs_1385_);
lean_inc_ref(v_oldWs_1385_);
v___x_1389_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1389_, 0, v_oldWs_1385_);
lean_ctor_set(v___x_1389_, 1, v___x_1387_);
lean_ctor_set(v___x_1389_, 2, v___x_1388_);
v___x_1390_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_1389_);
lean_dec_ref_known(v___x_1389_, 3);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1391_ = lean_string_data(v_oldWs_1385_);
v___x_1392_ = lean_array_mk(v___x_1391_);
v___x_1393_ = lean_string_data(v_newWs_1386_);
v___x_1394_ = lean_array_mk(v___x_1393_);
v___x_1395_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_1392_, v___x_1394_);
v___x_1396_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_1395_);
lean_dec_ref(v___x_1395_);
return v___x_1396_;
}
else
{
uint8_t v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
lean_dec_ref(v_oldWs_1385_);
v___x_1397_ = 2;
v___x_1398_ = lean_box(v___x_1397_);
v___x_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1398_);
lean_ctor_set(v___x_1399_, 1, v_newWs_1386_);
v___x_1400_ = lean_unsigned_to_nat(1u);
v___x_1401_ = lean_mk_empty_array_with_capacity(v___x_1400_);
v___x_1402_ = lean_array_push(v___x_1401_, v___x_1399_);
return v___x_1402_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(lean_object* v_s_1403_, lean_object* v_inst_1404_, lean_object* v_R_1405_, lean_object* v_a_1406_, uint8_t v_b_1407_, lean_object* v_c_1408_){
_start:
{
uint8_t v___x_1409_; 
v___x_1409_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1403_, v_a_1406_, v_b_1407_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___boxed(lean_object* v_s_1410_, lean_object* v_inst_1411_, lean_object* v_R_1412_, lean_object* v_a_1413_, lean_object* v_b_1414_, lean_object* v_c_1415_){
_start:
{
uint8_t v_b_boxed_1416_; uint8_t v_res_1417_; lean_object* v_r_1418_; 
v_b_boxed_1416_ = lean_unbox(v_b_1414_);
v_res_1417_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(v_s_1410_, v_inst_1411_, v_R_1412_, v_a_1413_, v_b_boxed_1416_, v_c_1415_);
lean_dec_ref(v_s_1410_);
v_r_1418_ = lean_box(v_res_1417_);
return v_r_1418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(lean_object* v___x_1419_, lean_object* v_original_1420_, uint32_t v_a_1421_, lean_object* v_inst_1422_, lean_object* v_a_1423_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1419_, v_original_1420_, v_a_1421_, v_a_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___boxed(lean_object* v___x_1425_, lean_object* v_original_1426_, lean_object* v_a_1427_, lean_object* v_inst_1428_, lean_object* v_a_1429_){
_start:
{
uint32_t v_a_boxed_1430_; lean_object* v_res_1431_; 
v_a_boxed_1430_ = lean_unbox_uint32(v_a_1427_);
lean_dec(v_a_1427_);
v_res_1431_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v___x_1425_, v_original_1426_, v_a_boxed_1430_, v_inst_1428_, v_a_1429_);
lean_dec_ref(v_original_1426_);
lean_dec(v___x_1425_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(lean_object* v___x_1432_, lean_object* v_edited_1433_, uint32_t v_a_1434_, lean_object* v_inst_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1432_, v_edited_1433_, v_a_1434_, v_a_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___boxed(lean_object* v___x_1438_, lean_object* v_edited_1439_, lean_object* v_a_1440_, lean_object* v_inst_1441_, lean_object* v_a_1442_){
_start:
{
uint32_t v_a_boxed_1443_; lean_object* v_res_1444_; 
v_a_boxed_1443_ = lean_unbox_uint32(v_a_1440_);
lean_dec(v_a_1440_);
v_res_1444_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(v___x_1438_, v_edited_1439_, v_a_boxed_1443_, v_inst_1441_, v_a_1442_);
lean_dec_ref(v_edited_1439_);
lean_dec(v___x_1438_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(lean_object* v___x_1445_, lean_object* v_original_1446_, lean_object* v_inst_1447_, lean_object* v_a_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_1445_, v_original_1446_, v_a_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___boxed(lean_object* v___x_1450_, lean_object* v_original_1451_, lean_object* v_inst_1452_, lean_object* v_a_1453_){
_start:
{
lean_object* v_res_1454_; 
v_res_1454_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(v___x_1450_, v_original_1451_, v_inst_1452_, v_a_1453_);
lean_dec_ref(v_original_1451_);
lean_dec(v___x_1450_);
return v_res_1454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(lean_object* v___x_1455_, lean_object* v_edited_1456_, lean_object* v_inst_1457_, lean_object* v_a_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1455_, v_edited_1456_, v_a_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___boxed(lean_object* v___x_1460_, lean_object* v_edited_1461_, lean_object* v_inst_1462_, lean_object* v_a_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(v___x_1460_, v_edited_1461_, v_inst_1462_, v_a_1463_);
lean_dec_ref(v_edited_1461_);
lean_dec(v___x_1460_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7(lean_object* v_as_1465_, lean_object* v_as_x27_1466_, lean_object* v_b_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(v_as_x27_1466_, v_b_1467_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___boxed(lean_object* v_as_1470_, lean_object* v_as_x27_1471_, lean_object* v_b_1472_, lean_object* v_a_1473_){
_start:
{
lean_object* v_res_1474_; 
v_res_1474_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7(v_as_1470_, v_as_x27_1471_, v_b_1472_, v_a_1473_);
lean_dec(v_as_x27_1471_);
lean_dec(v_as_1470_);
return v_res_1474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10(lean_object* v_lsize_1475_, lean_object* v_rsize_1476_, lean_object* v_histogram_1477_, lean_object* v_index_1478_, uint32_t v_val_1479_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(v_histogram_1477_, v_index_1478_, v_val_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___boxed(lean_object* v_lsize_1481_, lean_object* v_rsize_1482_, lean_object* v_histogram_1483_, lean_object* v_index_1484_, lean_object* v_val_1485_){
_start:
{
uint32_t v_val_boxed_1486_; lean_object* v_res_1487_; 
v_val_boxed_1486_ = lean_unbox_uint32(v_val_1485_);
lean_dec(v_val_1485_);
v_res_1487_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10(v_lsize_1481_, v_rsize_1482_, v_histogram_1483_, v_index_1484_, v_val_boxed_1486_);
lean_dec(v_rsize_1482_);
lean_dec(v_lsize_1481_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11(lean_object* v_upperBound_1488_, lean_object* v___x_1489_, lean_object* v_fst_1490_, lean_object* v___x_1491_, lean_object* v_inst_1492_, lean_object* v_R_1493_, lean_object* v_a_1494_, lean_object* v_b_1495_, lean_object* v_c_1496_){
_start:
{
lean_object* v___x_1497_; 
v___x_1497_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(v_upperBound_1488_, v___x_1489_, v_fst_1490_, v___x_1491_, v_a_1494_, v_b_1495_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___boxed(lean_object* v_upperBound_1498_, lean_object* v___x_1499_, lean_object* v_fst_1500_, lean_object* v___x_1501_, lean_object* v_inst_1502_, lean_object* v_R_1503_, lean_object* v_a_1504_, lean_object* v_b_1505_, lean_object* v_c_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11(v_upperBound_1498_, v___x_1499_, v_fst_1500_, v___x_1501_, v_inst_1502_, v_R_1503_, v_a_1504_, v_b_1505_, v_c_1506_);
lean_dec(v___x_1501_);
lean_dec_ref(v_fst_1500_);
lean_dec(v___x_1499_);
lean_dec(v_upperBound_1498_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12(lean_object* v_lsize_1508_, lean_object* v_rsize_1509_, lean_object* v_histogram_1510_, lean_object* v_index_1511_, uint32_t v_val_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(v_histogram_1510_, v_index_1511_, v_val_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___boxed(lean_object* v_lsize_1514_, lean_object* v_rsize_1515_, lean_object* v_histogram_1516_, lean_object* v_index_1517_, lean_object* v_val_1518_){
_start:
{
uint32_t v_val_boxed_1519_; lean_object* v_res_1520_; 
v_val_boxed_1519_ = lean_unbox_uint32(v_val_1518_);
lean_dec(v_val_1518_);
v_res_1520_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12(v_lsize_1514_, v_rsize_1515_, v_histogram_1516_, v_index_1517_, v_val_boxed_1519_);
lean_dec(v_rsize_1515_);
lean_dec(v_lsize_1514_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13(lean_object* v_upperBound_1521_, lean_object* v_fst_1522_, lean_object* v___x_1523_, lean_object* v_fst_1524_, lean_object* v_inst_1525_, lean_object* v_R_1526_, lean_object* v_a_1527_, lean_object* v_b_1528_, lean_object* v_c_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(v_upperBound_1521_, v_fst_1522_, v___x_1523_, v_fst_1524_, v_a_1527_, v_b_1528_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___boxed(lean_object* v_upperBound_1531_, lean_object* v_fst_1532_, lean_object* v___x_1533_, lean_object* v_fst_1534_, lean_object* v_inst_1535_, lean_object* v_R_1536_, lean_object* v_a_1537_, lean_object* v_b_1538_, lean_object* v_c_1539_){
_start:
{
lean_object* v_res_1540_; 
v_res_1540_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13(v_upperBound_1531_, v_fst_1532_, v___x_1533_, v_fst_1534_, v_inst_1535_, v_R_1536_, v_a_1537_, v_b_1538_, v_c_1539_);
lean_dec_ref(v_fst_1534_);
lean_dec(v___x_1533_);
lean_dec_ref(v_fst_1532_);
lean_dec(v_upperBound_1531_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13(lean_object* v_00_u03b2_1541_, lean_object* v_m_1542_, uint32_t v_a_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_m_1542_, v_a_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___boxed(lean_object* v_00_u03b2_1545_, lean_object* v_m_1546_, lean_object* v_a_1547_){
_start:
{
uint32_t v_a_boxed_1548_; lean_object* v_res_1549_; 
v_a_boxed_1548_ = lean_unbox_uint32(v_a_1547_);
lean_dec(v_a_1547_);
v_res_1549_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13(v_00_u03b2_1545_, v_m_1546_, v_a_boxed_1548_);
lean_dec_ref(v_m_1546_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14(lean_object* v_00_u03b2_1550_, lean_object* v_m_1551_, uint32_t v_a_1552_, lean_object* v_b_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_m_1551_, v_a_1552_, v_b_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___boxed(lean_object* v_00_u03b2_1555_, lean_object* v_m_1556_, lean_object* v_a_1557_, lean_object* v_b_1558_){
_start:
{
uint32_t v_a_boxed_1559_; lean_object* v_res_1560_; 
v_a_boxed_1559_ = lean_unbox_uint32(v_a_1557_);
lean_dec(v_a_1557_);
v_res_1560_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14(v_00_u03b2_1555_, v_m_1556_, v_a_boxed_1559_, v_b_1558_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14(lean_object* v_inst_1561_, lean_object* v_R_1562_, lean_object* v_a_1563_, lean_object* v_b_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(v_a_1563_, v_b_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20(lean_object* v_00_u03b2_1566_, uint32_t v_a_1567_, lean_object* v_x_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg(v_a_1567_, v_x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___boxed(lean_object* v_00_u03b2_1570_, lean_object* v_a_1571_, lean_object* v_x_1572_){
_start:
{
uint32_t v_a_boxed_1573_; lean_object* v_res_1574_; 
v_a_boxed_1573_ = lean_unbox_uint32(v_a_1571_);
lean_dec(v_a_1571_);
v_res_1574_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20(v_00_u03b2_1570_, v_a_boxed_1573_, v_x_1572_);
lean_dec(v_x_1572_);
return v_res_1574_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22(lean_object* v_00_u03b2_1575_, uint32_t v_a_1576_, lean_object* v_x_1577_){
_start:
{
uint8_t v___x_1578_; 
v___x_1578_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(v_a_1576_, v_x_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___boxed(lean_object* v_00_u03b2_1579_, lean_object* v_a_1580_, lean_object* v_x_1581_){
_start:
{
uint32_t v_a_boxed_1582_; uint8_t v_res_1583_; lean_object* v_r_1584_; 
v_a_boxed_1582_ = lean_unbox_uint32(v_a_1580_);
lean_dec(v_a_1580_);
v_res_1583_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22(v_00_u03b2_1579_, v_a_boxed_1582_, v_x_1581_);
lean_dec(v_x_1581_);
v_r_1584_ = lean_box(v_res_1583_);
return v_r_1584_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23(lean_object* v_00_u03b2_1585_, lean_object* v_data_1586_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23___redArg(v_data_1586_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24(lean_object* v_00_u03b2_1588_, uint32_t v_a_1589_, lean_object* v_b_1590_, lean_object* v_x_1591_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(v_a_1589_, v_b_1590_, v_x_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___boxed(lean_object* v_00_u03b2_1593_, lean_object* v_a_1594_, lean_object* v_b_1595_, lean_object* v_x_1596_){
_start:
{
uint32_t v_a_boxed_1597_; lean_object* v_res_1598_; 
v_a_boxed_1597_ = lean_unbox_uint32(v_a_1594_);
lean_dec(v_a_1594_);
v_res_1598_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24(v_00_u03b2_1593_, v_a_boxed_1597_, v_b_1595_, v_x_1596_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28(lean_object* v_00_u03b2_1599_, lean_object* v_i_1600_, lean_object* v_source_1601_, lean_object* v_target_1602_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28___redArg(v_i_1600_, v_source_1601_, v_target_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_1604_, lean_object* v_x_1605_, lean_object* v_x_1606_){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29___redArg(v_x_1605_, v_x_1606_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(lean_object* v_s_1608_, lean_object* v_stopPos_1609_, lean_object* v_i_1610_){
_start:
{
uint8_t v___y_1612_; lean_object* v___x_1615_; lean_object* v___x_1616_; uint8_t v___x_1617_; 
v___x_1615_ = lean_unsigned_to_nat(1u);
v___x_1616_ = lean_nat_add(v_i_1610_, v___x_1615_);
v___x_1617_ = lean_nat_dec_le(v___x_1616_, v_stopPos_1609_);
lean_dec(v___x_1616_);
if (v___x_1617_ == 0)
{
return v_i_1610_;
}
else
{
if (v___x_1617_ == 0)
{
v___y_1612_ = v___x_1617_;
goto v___jp_1611_;
}
else
{
uint32_t v___x_1618_; uint32_t v___x_1619_; uint8_t v___x_1620_; 
v___x_1618_ = lean_string_utf8_get(v_s_1608_, v_i_1610_);
v___x_1619_ = 32;
v___x_1620_ = lean_uint32_dec_eq(v___x_1618_, v___x_1619_);
if (v___x_1620_ == 0)
{
uint32_t v___x_1621_; uint8_t v___x_1622_; 
v___x_1621_ = 9;
v___x_1622_ = lean_uint32_dec_eq(v___x_1618_, v___x_1621_);
if (v___x_1622_ == 0)
{
uint32_t v___x_1623_; uint8_t v___x_1624_; 
v___x_1623_ = 13;
v___x_1624_ = lean_uint32_dec_eq(v___x_1618_, v___x_1623_);
if (v___x_1624_ == 0)
{
uint32_t v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = 10;
v___x_1626_ = lean_uint32_dec_eq(v___x_1618_, v___x_1625_);
v___y_1612_ = v___x_1626_;
goto v___jp_1611_;
}
else
{
v___y_1612_ = v___x_1624_;
goto v___jp_1611_;
}
}
else
{
v___y_1612_ = v___x_1622_;
goto v___jp_1611_;
}
}
else
{
v___y_1612_ = v___x_1620_;
goto v___jp_1611_;
}
}
}
v___jp_1611_:
{
if (v___y_1612_ == 0)
{
return v_i_1610_;
}
else
{
lean_object* v___x_1613_; 
v___x_1613_ = lean_string_utf8_next(v_s_1608_, v_i_1610_);
lean_dec(v_i_1610_);
v_i_1610_ = v___x_1613_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0___boxed(lean_object* v_s_1627_, lean_object* v_stopPos_1628_, lean_object* v_i_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1627_, v_stopPos_1628_, v_i_1629_);
lean_dec(v_stopPos_1628_);
lean_dec_ref(v_s_1627_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(lean_object* v_s_1631_, lean_object* v_b_1632_, lean_object* v_i_1633_, lean_object* v_r_1634_, lean_object* v_ws_1635_){
_start:
{
uint8_t v___x_1644_; 
v___x_1644_ = lean_string_utf8_at_end(v_s_1631_, v_i_1633_);
if (v___x_1644_ == 0)
{
uint32_t v___x_1645_; uint32_t v___x_1646_; uint8_t v___x_1647_; 
v___x_1645_ = lean_string_utf8_get(v_s_1631_, v_i_1633_);
v___x_1646_ = 32;
v___x_1647_ = lean_uint32_dec_eq(v___x_1645_, v___x_1646_);
if (v___x_1647_ == 0)
{
uint32_t v___x_1648_; uint8_t v___x_1649_; 
v___x_1648_ = 9;
v___x_1649_ = lean_uint32_dec_eq(v___x_1645_, v___x_1648_);
if (v___x_1649_ == 0)
{
uint32_t v___x_1650_; uint8_t v___x_1651_; 
v___x_1650_ = 13;
v___x_1651_ = lean_uint32_dec_eq(v___x_1645_, v___x_1650_);
if (v___x_1651_ == 0)
{
uint32_t v___x_1652_; uint8_t v___x_1653_; 
v___x_1652_ = 10;
v___x_1653_ = lean_uint32_dec_eq(v___x_1645_, v___x_1652_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; 
v___x_1654_ = lean_string_utf8_next(v_s_1631_, v_i_1633_);
lean_dec(v_i_1633_);
v_i_1633_ = v___x_1654_;
goto _start;
}
else
{
goto v___jp_1636_;
}
}
else
{
goto v___jp_1636_;
}
}
else
{
goto v___jp_1636_;
}
}
else
{
goto v___jp_1636_;
}
}
else
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1656_ = lean_string_utf8_extract(v_s_1631_, v_b_1632_, v_i_1633_);
lean_dec(v_i_1633_);
lean_dec(v_b_1632_);
v___x_1657_ = lean_array_push(v_r_1634_, v___x_1656_);
v___x_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
lean_ctor_set(v___x_1658_, 1, v_ws_1635_);
return v___x_1658_;
}
v___jp_1636_:
{
lean_object* v___x_1637_; lean_object* v_e_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1637_ = lean_string_utf8_byte_size(v_s_1631_);
lean_inc(v_i_1633_);
v_e_1638_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1631_, v___x_1637_, v_i_1633_);
v___x_1639_ = lean_string_utf8_extract(v_s_1631_, v_b_1632_, v_i_1633_);
lean_dec(v_b_1632_);
v___x_1640_ = lean_array_push(v_r_1634_, v___x_1639_);
v___x_1641_ = lean_string_utf8_extract(v_s_1631_, v_i_1633_, v_e_1638_);
lean_dec(v_i_1633_);
v___x_1642_ = lean_array_push(v_ws_1635_, v___x_1641_);
lean_inc(v_e_1638_);
v_b_1632_ = v_e_1638_;
v_i_1633_ = v_e_1638_;
v_r_1634_ = v___x_1640_;
v_ws_1635_ = v___x_1642_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux___boxed(lean_object* v_s_1659_, lean_object* v_b_1660_, lean_object* v_i_1661_, lean_object* v_r_1662_, lean_object* v_ws_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1659_, v_b_1660_, v_i_1661_, v_r_1662_, v_ws_1663_);
lean_dec_ref(v_s_1659_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(lean_object* v_s_1667_){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1668_ = lean_unsigned_to_nat(0u);
v___x_1669_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_1670_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1667_, v___x_1668_, v___x_1668_, v___x_1669_, v___x_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___boxed(lean_object* v_s_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_1671_);
lean_dec_ref(v_s_1671_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(size_t v_sz_1673_, size_t v_i_1674_, lean_object* v_bs_1675_){
_start:
{
uint8_t v___x_1676_; 
v___x_1676_ = lean_usize_dec_lt(v_i_1674_, v_sz_1673_);
if (v___x_1676_ == 0)
{
return v_bs_1675_;
}
else
{
lean_object* v_v_1677_; lean_object* v_fst_1678_; lean_object* v_snd_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1713_; 
v_v_1677_ = lean_array_uget(v_bs_1675_, v_i_1674_);
v_fst_1678_ = lean_ctor_get(v_v_1677_, 0);
v_snd_1679_ = lean_ctor_get(v_v_1677_, 1);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_v_1677_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1681_ = v_v_1677_;
v_isShared_1682_ = v_isSharedCheck_1713_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_snd_1679_);
lean_inc(v_fst_1678_);
lean_dec(v_v_1677_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1713_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1683_; lean_object* v_bs_x27_1684_; lean_object* v___y_1686_; lean_object* v___x_1691_; lean_object* v___x_1692_; uint8_t v___x_1693_; 
v___x_1683_ = lean_unsigned_to_nat(0u);
v_bs_x27_1684_ = lean_array_uset(v_bs_1675_, v_i_1674_, v___x_1683_);
v___x_1691_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_1692_ = lean_array_get_size(v_snd_1679_);
v___x_1693_ = lean_nat_dec_lt(v___x_1683_, v___x_1692_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1695_; 
lean_dec(v_snd_1679_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 1, v___x_1691_);
v___x_1695_ = v___x_1681_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_fst_1678_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v___x_1691_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
v___y_1686_ = v___x_1695_;
goto v___jp_1685_;
}
}
else
{
uint8_t v___x_1697_; 
v___x_1697_ = lean_nat_dec_le(v___x_1692_, v___x_1692_);
if (v___x_1697_ == 0)
{
if (v___x_1693_ == 0)
{
lean_object* v___x_1699_; 
lean_dec(v_snd_1679_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 1, v___x_1691_);
v___x_1699_ = v___x_1681_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_fst_1678_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v___x_1691_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
v___y_1686_ = v___x_1699_;
goto v___jp_1685_;
}
}
else
{
size_t v___x_1701_; size_t v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1705_; 
v___x_1701_ = ((size_t)0ULL);
v___x_1702_ = lean_usize_of_nat(v___x_1692_);
v___x_1703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_1679_, v___x_1701_, v___x_1702_, v___x_1691_);
lean_dec(v_snd_1679_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 1, v___x_1703_);
v___x_1705_ = v___x_1681_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_fst_1678_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v___x_1703_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
v___y_1686_ = v___x_1705_;
goto v___jp_1685_;
}
}
}
else
{
size_t v___x_1707_; size_t v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1711_; 
v___x_1707_ = ((size_t)0ULL);
v___x_1708_ = lean_usize_of_nat(v___x_1692_);
v___x_1709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_1679_, v___x_1707_, v___x_1708_, v___x_1691_);
lean_dec(v_snd_1679_);
if (v_isShared_1682_ == 0)
{
lean_ctor_set(v___x_1681_, 1, v___x_1709_);
v___x_1711_ = v___x_1681_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_fst_1678_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v___x_1709_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
v___y_1686_ = v___x_1711_;
goto v___jp_1685_;
}
}
}
v___jp_1685_:
{
size_t v___x_1687_; size_t v___x_1688_; lean_object* v___x_1689_; 
v___x_1687_ = ((size_t)1ULL);
v___x_1688_ = lean_usize_add(v_i_1674_, v___x_1687_);
v___x_1689_ = lean_array_uset(v_bs_x27_1684_, v_i_1674_, v___y_1686_);
v_i_1674_ = v___x_1688_;
v_bs_1675_ = v___x_1689_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0___boxed(lean_object* v_sz_1714_, lean_object* v_i_1715_, lean_object* v_bs_1716_){
_start:
{
size_t v_sz_boxed_1717_; size_t v_i_boxed_1718_; lean_object* v_res_1719_; 
v_sz_boxed_1717_ = lean_unbox_usize(v_sz_1714_);
lean_dec(v_sz_1714_);
v_i_boxed_1718_ = lean_unbox_usize(v_i_1715_);
lean_dec(v_i_1715_);
v_res_1719_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_boxed_1717_, v_i_boxed_1718_, v_bs_1716_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(size_t v_sz_1720_, size_t v_i_1721_, lean_object* v_bs_1722_){
_start:
{
uint8_t v___x_1723_; 
v___x_1723_ = lean_usize_dec_lt(v_i_1721_, v_sz_1720_);
if (v___x_1723_ == 0)
{
return v_bs_1722_;
}
else
{
lean_object* v_v_1724_; lean_object* v___x_1725_; lean_object* v_bs_x27_1726_; uint8_t v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; size_t v___x_1730_; size_t v___x_1731_; lean_object* v___x_1732_; 
v_v_1724_ = lean_array_uget(v_bs_1722_, v_i_1721_);
v___x_1725_ = lean_unsigned_to_nat(0u);
v_bs_x27_1726_ = lean_array_uset(v_bs_1722_, v_i_1721_, v___x_1725_);
v___x_1727_ = 0;
v___x_1728_ = lean_box(v___x_1727_);
v___x_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1729_, 0, v___x_1728_);
lean_ctor_set(v___x_1729_, 1, v_v_1724_);
v___x_1730_ = ((size_t)1ULL);
v___x_1731_ = lean_usize_add(v_i_1721_, v___x_1730_);
v___x_1732_ = lean_array_uset(v_bs_x27_1726_, v_i_1721_, v___x_1729_);
v_i_1721_ = v___x_1731_;
v_bs_1722_ = v___x_1732_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8___boxed(lean_object* v_sz_1734_, lean_object* v_i_1735_, lean_object* v_bs_1736_){
_start:
{
size_t v_sz_boxed_1737_; size_t v_i_boxed_1738_; lean_object* v_res_1739_; 
v_sz_boxed_1737_ = lean_unbox_usize(v_sz_1734_);
lean_dec(v_sz_1734_);
v_i_boxed_1738_ = lean_unbox_usize(v_i_1735_);
lean_dec(v_i_1735_);
v_res_1739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_boxed_1737_, v_i_boxed_1738_, v_bs_1736_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(lean_object* v_x_1740_, lean_object* v_x_1741_){
_start:
{
if (lean_obj_tag(v_x_1741_) == 0)
{
lean_inc(v_x_1740_);
return v_x_1740_;
}
else
{
lean_object* v_key_1742_; lean_object* v_value_1743_; lean_object* v_tail_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; 
v_key_1742_ = lean_ctor_get(v_x_1741_, 0);
v_value_1743_ = lean_ctor_get(v_x_1741_, 1);
v_tail_1744_ = lean_ctor_get(v_x_1741_, 2);
v___x_1745_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(v_x_1740_, v_tail_1744_);
lean_inc(v_value_1743_);
lean_inc(v_key_1742_);
v___x_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1746_, 0, v_key_1742_);
lean_ctor_set(v___x_1746_, 1, v_value_1743_);
v___x_1747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1747_, 0, v___x_1746_);
lean_ctor_set(v___x_1747_, 1, v___x_1745_);
return v___x_1747_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7___boxed(lean_object* v_x_1748_, lean_object* v_x_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(v_x_1748_, v_x_1749_);
lean_dec(v_x_1749_);
lean_dec(v_x_1748_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8(lean_object* v_as_1751_, size_t v_i_1752_, size_t v_stop_1753_, lean_object* v_b_1754_){
_start:
{
uint8_t v___x_1755_; 
v___x_1755_ = lean_usize_dec_eq(v_i_1752_, v_stop_1753_);
if (v___x_1755_ == 0)
{
size_t v___x_1756_; size_t v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1756_ = ((size_t)1ULL);
v___x_1757_ = lean_usize_sub(v_i_1752_, v___x_1756_);
v___x_1758_ = lean_array_uget_borrowed(v_as_1751_, v___x_1757_);
v___x_1759_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(v_b_1754_, v___x_1758_);
lean_dec(v_b_1754_);
v_i_1752_ = v___x_1757_;
v_b_1754_ = v___x_1759_;
goto _start;
}
else
{
return v_b_1754_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8___boxed(lean_object* v_as_1761_, lean_object* v_i_1762_, lean_object* v_stop_1763_, lean_object* v_b_1764_){
_start:
{
size_t v_i_boxed_1765_; size_t v_stop_boxed_1766_; lean_object* v_res_1767_; 
v_i_boxed_1765_ = lean_unbox_usize(v_i_1762_);
lean_dec(v_i_1762_);
v_stop_boxed_1766_ = lean_unbox_usize(v_stop_1763_);
lean_dec(v_stop_1763_);
v_res_1767_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8(v_as_1761_, v_i_boxed_1765_, v_stop_boxed_1766_, v_b_1764_);
lean_dec_ref(v_as_1761_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4_spec__6(lean_object* v_left_1768_, lean_object* v_right_1769_, lean_object* v_pref_1770_){
_start:
{
lean_object* v_start_1771_; lean_object* v_stop_1772_; lean_object* v_start_1773_; lean_object* v_stop_1774_; lean_object* v_i_1775_; uint8_t v___y_1777_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v_start_1771_ = lean_ctor_get(v_left_1768_, 1);
v_stop_1772_ = lean_ctor_get(v_left_1768_, 2);
v_start_1773_ = lean_ctor_get(v_right_1769_, 1);
v_stop_1774_ = lean_ctor_get(v_right_1769_, 2);
v_i_1775_ = lean_array_get_size(v_pref_1770_);
v___x_1791_ = lean_nat_sub(v_stop_1772_, v_start_1771_);
v___x_1792_ = lean_nat_dec_lt(v_i_1775_, v___x_1791_);
lean_dec(v___x_1791_);
if (v___x_1792_ == 0)
{
v___y_1777_ = v___x_1792_;
goto v___jp_1776_;
}
else
{
lean_object* v___x_1793_; uint8_t v___x_1794_; 
v___x_1793_ = lean_nat_sub(v_stop_1774_, v_start_1773_);
v___x_1794_ = lean_nat_dec_lt(v_i_1775_, v___x_1793_);
lean_dec(v___x_1793_);
v___y_1777_ = v___x_1794_;
goto v___jp_1776_;
}
v___jp_1776_:
{
if (v___y_1777_ == 0)
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1778_ = l_Subarray_drop___redArg(v_left_1768_, v_i_1775_);
v___x_1779_ = l_Subarray_drop___redArg(v_right_1769_, v_i_1775_);
v___x_1780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1780_, 0, v___x_1778_);
lean_ctor_set(v___x_1780_, 1, v___x_1779_);
v___x_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1781_, 0, v_pref_1770_);
lean_ctor_set(v___x_1781_, 1, v___x_1780_);
return v___x_1781_;
}
else
{
lean_object* v___x_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1782_ = l_Subarray_get___redArg(v_left_1768_, v_i_1775_);
v___x_1783_ = l_Subarray_get___redArg(v_right_1769_, v_i_1775_);
v___x_1784_ = lean_string_dec_eq(v___x_1782_, v___x_1783_);
lean_dec(v___x_1783_);
if (v___x_1784_ == 0)
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
lean_dec(v___x_1782_);
v___x_1785_ = l_Subarray_drop___redArg(v_left_1768_, v_i_1775_);
v___x_1786_ = l_Subarray_drop___redArg(v_right_1769_, v_i_1775_);
v___x_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1785_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1788_, 0, v_pref_1770_);
lean_ctor_set(v___x_1788_, 1, v___x_1787_);
return v___x_1788_;
}
else
{
lean_object* v___x_1789_; 
v___x_1789_ = lean_array_push(v_pref_1770_, v___x_1782_);
v_pref_1770_ = v___x_1789_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4(lean_object* v_left_1795_, lean_object* v_right_1796_){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_1798_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4_spec__6(v_left_1795_, v_right_1796_, v___x_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(lean_object* v_a_1799_, lean_object* v_x_1800_){
_start:
{
if (lean_obj_tag(v_x_1800_) == 0)
{
lean_object* v___x_1801_; 
v___x_1801_ = lean_box(0);
return v___x_1801_;
}
else
{
lean_object* v_key_1802_; lean_object* v_value_1803_; lean_object* v_tail_1804_; uint8_t v___x_1805_; 
v_key_1802_ = lean_ctor_get(v_x_1800_, 0);
v_value_1803_ = lean_ctor_get(v_x_1800_, 1);
v_tail_1804_ = lean_ctor_get(v_x_1800_, 2);
v___x_1805_ = lean_string_dec_eq(v_key_1802_, v_a_1799_);
if (v___x_1805_ == 0)
{
v_x_1800_ = v_tail_1804_;
goto _start;
}
else
{
lean_object* v___x_1807_; 
lean_inc(v_value_1803_);
v___x_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1807_, 0, v_value_1803_);
return v___x_1807_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg___boxed(lean_object* v_a_1808_, lean_object* v_x_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(v_a_1808_, v_x_1809_);
lean_dec(v_x_1809_);
lean_dec_ref(v_a_1808_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(lean_object* v_m_1811_, lean_object* v_a_1812_){
_start:
{
lean_object* v_buckets_1813_; lean_object* v___x_1814_; uint64_t v___x_1815_; uint64_t v___x_1816_; uint64_t v___x_1817_; uint64_t v_fold_1818_; uint64_t v___x_1819_; uint64_t v___x_1820_; uint64_t v___x_1821_; size_t v___x_1822_; size_t v___x_1823_; size_t v___x_1824_; size_t v___x_1825_; size_t v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v_buckets_1813_ = lean_ctor_get(v_m_1811_, 1);
v___x_1814_ = lean_array_get_size(v_buckets_1813_);
v___x_1815_ = lean_string_hash(v_a_1812_);
v___x_1816_ = 32ULL;
v___x_1817_ = lean_uint64_shift_right(v___x_1815_, v___x_1816_);
v_fold_1818_ = lean_uint64_xor(v___x_1815_, v___x_1817_);
v___x_1819_ = 16ULL;
v___x_1820_ = lean_uint64_shift_right(v_fold_1818_, v___x_1819_);
v___x_1821_ = lean_uint64_xor(v_fold_1818_, v___x_1820_);
v___x_1822_ = lean_uint64_to_usize(v___x_1821_);
v___x_1823_ = lean_usize_of_nat(v___x_1814_);
v___x_1824_ = ((size_t)1ULL);
v___x_1825_ = lean_usize_sub(v___x_1823_, v___x_1824_);
v___x_1826_ = lean_usize_land(v___x_1822_, v___x_1825_);
v___x_1827_ = lean_array_uget_borrowed(v_buckets_1813_, v___x_1826_);
v___x_1828_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(v_a_1812_, v___x_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg___boxed(lean_object* v_m_1829_, lean_object* v_a_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_m_1829_, v_a_1830_);
lean_dec_ref(v_a_1830_);
lean_dec_ref(v_m_1829_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29___redArg(lean_object* v_x_1832_, lean_object* v_x_1833_){
_start:
{
if (lean_obj_tag(v_x_1833_) == 0)
{
return v_x_1832_;
}
else
{
lean_object* v_key_1834_; lean_object* v_value_1835_; lean_object* v_tail_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1859_; 
v_key_1834_ = lean_ctor_get(v_x_1833_, 0);
v_value_1835_ = lean_ctor_get(v_x_1833_, 1);
v_tail_1836_ = lean_ctor_get(v_x_1833_, 2);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_x_1833_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1838_ = v_x_1833_;
v_isShared_1839_ = v_isSharedCheck_1859_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_tail_1836_);
lean_inc(v_value_1835_);
lean_inc(v_key_1834_);
lean_dec(v_x_1833_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1859_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; uint64_t v___x_1841_; uint64_t v___x_1842_; uint64_t v___x_1843_; uint64_t v_fold_1844_; uint64_t v___x_1845_; uint64_t v___x_1846_; uint64_t v___x_1847_; size_t v___x_1848_; size_t v___x_1849_; size_t v___x_1850_; size_t v___x_1851_; size_t v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1855_; 
v___x_1840_ = lean_array_get_size(v_x_1832_);
v___x_1841_ = lean_string_hash(v_key_1834_);
v___x_1842_ = 32ULL;
v___x_1843_ = lean_uint64_shift_right(v___x_1841_, v___x_1842_);
v_fold_1844_ = lean_uint64_xor(v___x_1841_, v___x_1843_);
v___x_1845_ = 16ULL;
v___x_1846_ = lean_uint64_shift_right(v_fold_1844_, v___x_1845_);
v___x_1847_ = lean_uint64_xor(v_fold_1844_, v___x_1846_);
v___x_1848_ = lean_uint64_to_usize(v___x_1847_);
v___x_1849_ = lean_usize_of_nat(v___x_1840_);
v___x_1850_ = ((size_t)1ULL);
v___x_1851_ = lean_usize_sub(v___x_1849_, v___x_1850_);
v___x_1852_ = lean_usize_land(v___x_1848_, v___x_1851_);
v___x_1853_ = lean_array_uget_borrowed(v_x_1832_, v___x_1852_);
lean_inc(v___x_1853_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 2, v___x_1853_);
v___x_1855_ = v___x_1838_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_key_1834_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_value_1835_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
lean_object* v___x_1856_; 
v___x_1856_ = lean_array_uset(v_x_1832_, v___x_1852_, v___x_1855_);
v_x_1832_ = v___x_1856_;
v_x_1833_ = v_tail_1836_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28___redArg(lean_object* v_i_1860_, lean_object* v_source_1861_, lean_object* v_target_1862_){
_start:
{
lean_object* v___x_1863_; uint8_t v___x_1864_; 
v___x_1863_ = lean_array_get_size(v_source_1861_);
v___x_1864_ = lean_nat_dec_lt(v_i_1860_, v___x_1863_);
if (v___x_1864_ == 0)
{
lean_dec_ref(v_source_1861_);
lean_dec(v_i_1860_);
return v_target_1862_;
}
else
{
lean_object* v_es_1865_; lean_object* v___x_1866_; lean_object* v_source_1867_; lean_object* v_target_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v_es_1865_ = lean_array_fget(v_source_1861_, v_i_1860_);
v___x_1866_ = lean_box(0);
v_source_1867_ = lean_array_fset(v_source_1861_, v_i_1860_, v___x_1866_);
v_target_1868_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29___redArg(v_target_1862_, v_es_1865_);
v___x_1869_ = lean_unsigned_to_nat(1u);
v___x_1870_ = lean_nat_add(v_i_1860_, v___x_1869_);
lean_dec(v_i_1860_);
v_i_1860_ = v___x_1870_;
v_source_1861_ = v_source_1867_;
v_target_1862_ = v_target_1868_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23___redArg(lean_object* v_data_1872_){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v_nbuckets_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1873_ = lean_array_get_size(v_data_1872_);
v___x_1874_ = lean_unsigned_to_nat(2u);
v_nbuckets_1875_ = lean_nat_mul(v___x_1873_, v___x_1874_);
v___x_1876_ = lean_unsigned_to_nat(0u);
v___x_1877_ = lean_box(0);
v___x_1878_ = lean_mk_array(v_nbuckets_1875_, v___x_1877_);
v___x_1879_ = lean_array_propagate_mark(v_data_1872_, v___x_1878_);
v___x_1880_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28___redArg(v___x_1876_, v_data_1872_, v___x_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(lean_object* v_a_1881_, lean_object* v_b_1882_, lean_object* v_x_1883_){
_start:
{
if (lean_obj_tag(v_x_1883_) == 0)
{
lean_dec(v_b_1882_);
lean_dec_ref(v_a_1881_);
return v_x_1883_;
}
else
{
lean_object* v_key_1884_; lean_object* v_value_1885_; lean_object* v_tail_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1898_; 
v_key_1884_ = lean_ctor_get(v_x_1883_, 0);
v_value_1885_ = lean_ctor_get(v_x_1883_, 1);
v_tail_1886_ = lean_ctor_get(v_x_1883_, 2);
v_isSharedCheck_1898_ = !lean_is_exclusive(v_x_1883_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1888_ = v_x_1883_;
v_isShared_1889_ = v_isSharedCheck_1898_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_tail_1886_);
lean_inc(v_value_1885_);
lean_inc(v_key_1884_);
lean_dec(v_x_1883_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1898_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
uint8_t v___x_1890_; 
v___x_1890_ = lean_string_dec_eq(v_key_1884_, v_a_1881_);
if (v___x_1890_ == 0)
{
lean_object* v___x_1891_; lean_object* v___x_1893_; 
v___x_1891_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(v_a_1881_, v_b_1882_, v_tail_1886_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 2, v___x_1891_);
v___x_1893_ = v___x_1888_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_key_1884_);
lean_ctor_set(v_reuseFailAlloc_1894_, 1, v_value_1885_);
lean_ctor_set(v_reuseFailAlloc_1894_, 2, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
else
{
lean_object* v___x_1896_; 
lean_dec(v_value_1885_);
lean_dec(v_key_1884_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 1, v_b_1882_);
lean_ctor_set(v___x_1888_, 0, v_a_1881_);
v___x_1896_ = v___x_1888_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1881_);
lean_ctor_set(v_reuseFailAlloc_1897_, 1, v_b_1882_);
lean_ctor_set(v_reuseFailAlloc_1897_, 2, v_tail_1886_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(lean_object* v_a_1899_, lean_object* v_x_1900_){
_start:
{
if (lean_obj_tag(v_x_1900_) == 0)
{
uint8_t v___x_1901_; 
v___x_1901_ = 0;
return v___x_1901_;
}
else
{
lean_object* v_key_1902_; lean_object* v_tail_1903_; uint8_t v___x_1904_; 
v_key_1902_ = lean_ctor_get(v_x_1900_, 0);
v_tail_1903_ = lean_ctor_get(v_x_1900_, 2);
v___x_1904_ = lean_string_dec_eq(v_key_1902_, v_a_1899_);
if (v___x_1904_ == 0)
{
v_x_1900_ = v_tail_1903_;
goto _start;
}
else
{
return v___x_1904_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg___boxed(lean_object* v_a_1906_, lean_object* v_x_1907_){
_start:
{
uint8_t v_res_1908_; lean_object* v_r_1909_; 
v_res_1908_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(v_a_1906_, v_x_1907_);
lean_dec(v_x_1907_);
lean_dec_ref(v_a_1906_);
v_r_1909_ = lean_box(v_res_1908_);
return v_r_1909_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(lean_object* v_m_1910_, lean_object* v_a_1911_, lean_object* v_b_1912_){
_start:
{
lean_object* v_size_1913_; lean_object* v_buckets_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1957_; 
v_size_1913_ = lean_ctor_get(v_m_1910_, 0);
v_buckets_1914_ = lean_ctor_get(v_m_1910_, 1);
v_isSharedCheck_1957_ = !lean_is_exclusive(v_m_1910_);
if (v_isSharedCheck_1957_ == 0)
{
v___x_1916_ = v_m_1910_;
v_isShared_1917_ = v_isSharedCheck_1957_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_buckets_1914_);
lean_inc(v_size_1913_);
lean_dec(v_m_1910_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1957_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1918_; uint64_t v___x_1919_; uint64_t v___x_1920_; uint64_t v___x_1921_; uint64_t v_fold_1922_; uint64_t v___x_1923_; uint64_t v___x_1924_; uint64_t v___x_1925_; size_t v___x_1926_; size_t v___x_1927_; size_t v___x_1928_; size_t v___x_1929_; size_t v___x_1930_; lean_object* v_bkt_1931_; uint8_t v___x_1932_; 
v___x_1918_ = lean_array_get_size(v_buckets_1914_);
v___x_1919_ = lean_string_hash(v_a_1911_);
v___x_1920_ = 32ULL;
v___x_1921_ = lean_uint64_shift_right(v___x_1919_, v___x_1920_);
v_fold_1922_ = lean_uint64_xor(v___x_1919_, v___x_1921_);
v___x_1923_ = 16ULL;
v___x_1924_ = lean_uint64_shift_right(v_fold_1922_, v___x_1923_);
v___x_1925_ = lean_uint64_xor(v_fold_1922_, v___x_1924_);
v___x_1926_ = lean_uint64_to_usize(v___x_1925_);
v___x_1927_ = lean_usize_of_nat(v___x_1918_);
v___x_1928_ = ((size_t)1ULL);
v___x_1929_ = lean_usize_sub(v___x_1927_, v___x_1928_);
v___x_1930_ = lean_usize_land(v___x_1926_, v___x_1929_);
v_bkt_1931_ = lean_array_uget_borrowed(v_buckets_1914_, v___x_1930_);
v___x_1932_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(v_a_1911_, v_bkt_1931_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1933_; lean_object* v_size_x27_1934_; lean_object* v___x_1935_; lean_object* v_buckets_x27_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1933_ = lean_unsigned_to_nat(1u);
v_size_x27_1934_ = lean_nat_add(v_size_1913_, v___x_1933_);
lean_dec(v_size_1913_);
lean_inc(v_bkt_1931_);
v___x_1935_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1935_, 0, v_a_1911_);
lean_ctor_set(v___x_1935_, 1, v_b_1912_);
lean_ctor_set(v___x_1935_, 2, v_bkt_1931_);
v_buckets_x27_1936_ = lean_array_uset(v_buckets_1914_, v___x_1930_, v___x_1935_);
v___x_1937_ = lean_unsigned_to_nat(4u);
v___x_1938_ = lean_nat_mul(v_size_x27_1934_, v___x_1937_);
v___x_1939_ = lean_unsigned_to_nat(3u);
v___x_1940_ = lean_nat_div(v___x_1938_, v___x_1939_);
lean_dec(v___x_1938_);
v___x_1941_ = lean_array_get_size(v_buckets_x27_1936_);
v___x_1942_ = lean_nat_dec_le(v___x_1940_, v___x_1941_);
lean_dec(v___x_1940_);
if (v___x_1942_ == 0)
{
lean_object* v_val_1943_; lean_object* v___x_1945_; 
v_val_1943_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23___redArg(v_buckets_x27_1936_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 1, v_val_1943_);
lean_ctor_set(v___x_1916_, 0, v_size_x27_1934_);
v___x_1945_ = v___x_1916_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_size_x27_1934_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_val_1943_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
else
{
lean_object* v___x_1948_; 
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 1, v_buckets_x27_1936_);
lean_ctor_set(v___x_1916_, 0, v_size_x27_1934_);
v___x_1948_ = v___x_1916_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_size_x27_1934_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_buckets_x27_1936_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
else
{
lean_object* v___x_1950_; lean_object* v_buckets_x27_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1955_; 
lean_inc(v_bkt_1931_);
v___x_1950_ = lean_box(0);
v_buckets_x27_1951_ = lean_array_uset(v_buckets_1914_, v___x_1930_, v___x_1950_);
v___x_1952_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(v_a_1911_, v_b_1912_, v_bkt_1931_);
v___x_1953_ = lean_array_uset(v_buckets_x27_1951_, v___x_1930_, v___x_1952_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 1, v___x_1953_);
v___x_1955_ = v___x_1916_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_size_1913_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v___x_1953_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___redArg(lean_object* v_histogram_1958_, lean_object* v_index_1959_, lean_object* v_val_1960_){
_start:
{
lean_object* v___x_1961_; 
v___x_1961_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_histogram_1958_, v_val_1960_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; 
v___x_1962_ = lean_unsigned_to_nat(0u);
v___x_1963_ = lean_box(0);
v___x_1964_ = lean_unsigned_to_nat(1u);
v___x_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1965_, 0, v_index_1959_);
v___x_1966_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1966_, 0, v___x_1962_);
lean_ctor_set(v___x_1966_, 1, v___x_1963_);
lean_ctor_set(v___x_1966_, 2, v___x_1964_);
lean_ctor_set(v___x_1966_, 3, v___x_1965_);
v___x_1967_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_1958_, v_val_1960_, v___x_1966_);
return v___x_1967_;
}
else
{
lean_object* v_val_1968_; lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1989_; 
v_val_1968_ = lean_ctor_get(v___x_1961_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1970_ = v___x_1961_;
v_isShared_1971_ = v_isSharedCheck_1989_;
goto v_resetjp_1969_;
}
else
{
lean_inc(v_val_1968_);
lean_dec(v___x_1961_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1989_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v_leftCount_1972_; lean_object* v_leftIndex_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1986_; 
v_leftCount_1972_ = lean_ctor_get(v_val_1968_, 0);
v_leftIndex_1973_ = lean_ctor_get(v_val_1968_, 1);
v_isSharedCheck_1986_ = !lean_is_exclusive(v_val_1968_);
if (v_isSharedCheck_1986_ == 0)
{
lean_object* v_unused_1987_; lean_object* v_unused_1988_; 
v_unused_1987_ = lean_ctor_get(v_val_1968_, 3);
lean_dec(v_unused_1987_);
v_unused_1988_ = lean_ctor_get(v_val_1968_, 2);
lean_dec(v_unused_1988_);
v___x_1975_ = v_val_1968_;
v_isShared_1976_ = v_isSharedCheck_1986_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_leftIndex_1973_);
lean_inc(v_leftCount_1972_);
lean_dec(v_val_1968_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1986_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1980_; 
v___x_1977_ = lean_unsigned_to_nat(1u);
v___x_1978_ = lean_nat_add(v_leftCount_1972_, v___x_1977_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v_index_1959_);
v___x_1980_ = v___x_1970_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v_index_1959_);
v___x_1980_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
lean_object* v___x_1982_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 3, v___x_1980_);
lean_ctor_set(v___x_1975_, 2, v___x_1978_);
v___x_1982_ = v___x_1975_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v_leftCount_1972_);
lean_ctor_set(v_reuseFailAlloc_1984_, 1, v_leftIndex_1973_);
lean_ctor_set(v_reuseFailAlloc_1984_, 2, v___x_1978_);
lean_ctor_set(v_reuseFailAlloc_1984_, 3, v___x_1980_);
v___x_1982_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_1958_, v_val_1960_, v___x_1982_);
return v___x_1983_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(lean_object* v_upperBound_1990_, lean_object* v___x_1991_, lean_object* v_fst_1992_, lean_object* v___x_1993_, lean_object* v_a_1994_, lean_object* v_b_1995_){
_start:
{
uint8_t v___x_1996_; 
v___x_1996_ = lean_nat_dec_lt(v_a_1994_, v_upperBound_1990_);
if (v___x_1996_ == 0)
{
lean_dec(v_a_1994_);
return v_b_1995_;
}
else
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1997_ = l_Subarray_get___redArg(v_fst_1992_, v_a_1994_);
lean_inc(v_a_1994_);
v___x_1998_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___redArg(v_b_1995_, v_a_1994_, v___x_1997_);
v___x_1999_ = lean_unsigned_to_nat(1u);
v___x_2000_ = lean_nat_add(v_a_1994_, v___x_1999_);
lean_dec(v_a_1994_);
v_a_1994_ = v___x_2000_;
v_b_1995_ = v___x_1998_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg___boxed(lean_object* v_upperBound_2002_, lean_object* v___x_2003_, lean_object* v_fst_2004_, lean_object* v___x_2005_, lean_object* v_a_2006_, lean_object* v_b_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(v_upperBound_2002_, v___x_2003_, v_fst_2004_, v___x_2005_, v_a_2006_, v_b_2007_);
lean_dec(v___x_2005_);
lean_dec_ref(v_fst_2004_);
lean_dec(v___x_2003_);
lean_dec(v_upperBound_2002_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(lean_object* v_as_x27_2009_, lean_object* v_b_2010_){
_start:
{
if (lean_obj_tag(v_as_x27_2009_) == 0)
{
return v_b_2010_;
}
else
{
lean_object* v_head_2011_; lean_object* v_snd_2012_; lean_object* v_leftIndex_2013_; 
v_head_2011_ = lean_ctor_get(v_as_x27_2009_, 0);
v_snd_2012_ = lean_ctor_get(v_head_2011_, 1);
v_leftIndex_2013_ = lean_ctor_get(v_snd_2012_, 1);
if (lean_obj_tag(v_leftIndex_2013_) == 1)
{
lean_object* v_rightIndex_2014_; 
v_rightIndex_2014_ = lean_ctor_get(v_snd_2012_, 3);
if (lean_obj_tag(v_rightIndex_2014_) == 1)
{
if (lean_obj_tag(v_b_2010_) == 0)
{
lean_object* v_tail_2015_; lean_object* v_fst_2016_; lean_object* v_leftCount_2017_; lean_object* v_rightCount_2018_; lean_object* v_val_2019_; lean_object* v_val_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v_tail_2015_ = lean_ctor_get(v_as_x27_2009_, 1);
v_fst_2016_ = lean_ctor_get(v_head_2011_, 0);
v_leftCount_2017_ = lean_ctor_get(v_snd_2012_, 0);
v_rightCount_2018_ = lean_ctor_get(v_snd_2012_, 2);
v_val_2019_ = lean_ctor_get(v_leftIndex_2013_, 0);
v_val_2020_ = lean_ctor_get(v_rightIndex_2014_, 0);
v___x_2021_ = lean_nat_add(v_leftCount_2017_, v_rightCount_2018_);
lean_inc(v_val_2020_);
lean_inc(v_val_2019_);
v___x_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2022_, 0, v_val_2019_);
lean_ctor_set(v___x_2022_, 1, v_val_2020_);
lean_inc(v_fst_2016_);
v___x_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2023_, 0, v_fst_2016_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
v___x_2024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2021_);
lean_ctor_set(v___x_2024_, 1, v___x_2023_);
v___x_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
v_as_x27_2009_ = v_tail_2015_;
v_b_2010_ = v___x_2025_;
goto _start;
}
else
{
lean_object* v_val_2027_; lean_object* v_tail_2028_; lean_object* v_fst_2029_; lean_object* v_leftCount_2030_; lean_object* v_rightCount_2031_; lean_object* v_val_2032_; lean_object* v_val_2033_; lean_object* v_fst_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2055_; 
v_val_2027_ = lean_ctor_get(v_b_2010_, 0);
lean_inc(v_val_2027_);
v_tail_2028_ = lean_ctor_get(v_as_x27_2009_, 1);
v_fst_2029_ = lean_ctor_get(v_head_2011_, 0);
v_leftCount_2030_ = lean_ctor_get(v_snd_2012_, 0);
v_rightCount_2031_ = lean_ctor_get(v_snd_2012_, 2);
v_val_2032_ = lean_ctor_get(v_leftIndex_2013_, 0);
v_val_2033_ = lean_ctor_get(v_rightIndex_2014_, 0);
v_fst_2034_ = lean_ctor_get(v_val_2027_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_val_2027_);
if (v_isSharedCheck_2055_ == 0)
{
lean_object* v_unused_2056_; 
v_unused_2056_ = lean_ctor_get(v_val_2027_, 1);
lean_dec(v_unused_2056_);
v___x_2036_ = v_val_2027_;
v_isShared_2037_ = v_isSharedCheck_2055_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_fst_2034_);
lean_dec(v_val_2027_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2055_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2038_; uint8_t v___x_2039_; 
v___x_2038_ = lean_nat_add(v_leftCount_2030_, v_rightCount_2031_);
v___x_2039_ = lean_nat_dec_lt(v___x_2038_, v_fst_2034_);
lean_dec(v_fst_2034_);
if (v___x_2039_ == 0)
{
lean_dec(v___x_2038_);
lean_del_object(v___x_2036_);
v_as_x27_2009_ = v_tail_2028_;
goto _start;
}
else
{
lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2053_; 
v_isSharedCheck_2053_ = !lean_is_exclusive(v_b_2010_);
if (v_isSharedCheck_2053_ == 0)
{
lean_object* v_unused_2054_; 
v_unused_2054_ = lean_ctor_get(v_b_2010_, 0);
lean_dec(v_unused_2054_);
v___x_2042_ = v_b_2010_;
v_isShared_2043_ = v_isSharedCheck_2053_;
goto v_resetjp_2041_;
}
else
{
lean_dec(v_b_2010_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2053_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2045_; 
lean_inc(v_val_2033_);
lean_inc(v_val_2032_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 1, v_val_2033_);
lean_ctor_set(v___x_2036_, 0, v_val_2032_);
v___x_2045_ = v___x_2036_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_val_2032_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_val_2033_);
v___x_2045_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2049_; 
lean_inc(v_fst_2029_);
v___x_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2046_, 0, v_fst_2029_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
v___x_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2038_);
lean_ctor_set(v___x_2047_, 1, v___x_2046_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 0, v___x_2047_);
v___x_2049_ = v___x_2042_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
v_as_x27_2009_ = v_tail_2028_;
v_b_2010_ = v___x_2049_;
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
lean_object* v_tail_2057_; 
v_tail_2057_ = lean_ctor_get(v_as_x27_2009_, 1);
v_as_x27_2009_ = v_tail_2057_;
goto _start;
}
}
else
{
lean_object* v_tail_2059_; 
v_tail_2059_ = lean_ctor_get(v_as_x27_2009_, 1);
v_as_x27_2009_ = v_tail_2059_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_as_x27_2061_, lean_object* v_b_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(v_as_x27_2061_, v_b_2062_);
lean_dec(v_as_x27_2061_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(lean_object* v_a_2064_, lean_object* v_b_2065_){
_start:
{
lean_object* v_array_2066_; lean_object* v_start_2067_; lean_object* v_stop_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2081_; 
v_array_2066_ = lean_ctor_get(v_a_2064_, 0);
v_start_2067_ = lean_ctor_get(v_a_2064_, 1);
v_stop_2068_ = lean_ctor_get(v_a_2064_, 2);
v_isSharedCheck_2081_ = !lean_is_exclusive(v_a_2064_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2070_ = v_a_2064_;
v_isShared_2071_ = v_isSharedCheck_2081_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_stop_2068_);
lean_inc(v_start_2067_);
lean_inc(v_array_2066_);
lean_dec(v_a_2064_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2081_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
uint8_t v___x_2072_; 
v___x_2072_ = lean_nat_dec_lt(v_start_2067_, v_stop_2068_);
if (v___x_2072_ == 0)
{
lean_del_object(v___x_2070_);
lean_dec(v_stop_2068_);
lean_dec(v_start_2067_);
lean_dec_ref(v_array_2066_);
return v_b_2065_;
}
else
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2076_; 
v___x_2073_ = lean_unsigned_to_nat(1u);
v___x_2074_ = lean_nat_add(v_start_2067_, v___x_2073_);
lean_inc_ref(v_array_2066_);
if (v_isShared_2071_ == 0)
{
lean_ctor_set(v___x_2070_, 1, v___x_2074_);
v___x_2076_ = v___x_2070_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_array_2066_);
lean_ctor_set(v_reuseFailAlloc_2080_, 1, v___x_2074_);
lean_ctor_set(v_reuseFailAlloc_2080_, 2, v_stop_2068_);
v___x_2076_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2077_ = lean_array_fget(v_array_2066_, v_start_2067_);
lean_dec(v_start_2067_);
lean_dec_ref(v_array_2066_);
v___x_2078_ = lean_array_push(v_b_2065_, v___x_2077_);
v_a_2064_ = v___x_2076_;
v_b_2065_ = v___x_2078_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8(lean_object* v_left_2082_, lean_object* v_right_2083_, lean_object* v_i_2084_){
_start:
{
lean_object* v_start_2085_; lean_object* v_stop_2086_; lean_object* v_start_2087_; lean_object* v_stop_2088_; lean_object* v___x_2089_; uint8_t v___x_2090_; lean_object* v___x_2091_; uint8_t v___y_2093_; 
v_start_2085_ = lean_ctor_get(v_left_2082_, 1);
v_stop_2086_ = lean_ctor_get(v_left_2082_, 2);
v_start_2087_ = lean_ctor_get(v_right_2083_, 1);
v_stop_2088_ = lean_ctor_get(v_right_2083_, 2);
v___x_2089_ = lean_nat_sub(v_stop_2086_, v_start_2085_);
v___x_2090_ = lean_nat_dec_lt(v_i_2084_, v___x_2089_);
v___x_2091_ = lean_nat_sub(v_stop_2088_, v_start_2087_);
if (v___x_2090_ == 0)
{
v___y_2093_ = v___x_2090_;
goto v___jp_2092_;
}
else
{
uint8_t v___x_2120_; 
v___x_2120_ = lean_nat_dec_lt(v_i_2084_, v___x_2091_);
v___y_2093_ = v___x_2120_;
goto v___jp_2092_;
}
v___jp_2092_:
{
if (v___y_2093_ == 0)
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2094_ = lean_nat_sub(v___x_2089_, v_i_2084_);
lean_dec(v___x_2089_);
lean_inc_ref(v_left_2082_);
v___x_2095_ = l_Subarray_take___redArg(v_left_2082_, v___x_2094_);
v___x_2096_ = lean_nat_sub(v___x_2091_, v_i_2084_);
lean_dec(v_i_2084_);
lean_dec(v___x_2091_);
v___x_2097_ = l_Subarray_take___redArg(v_right_2083_, v___x_2096_);
lean_dec(v___x_2096_);
v___x_2098_ = l_Subarray_drop___redArg(v_left_2082_, v___x_2094_);
lean_dec(v___x_2094_);
v___x_2099_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2100_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(v___x_2098_, v___x_2099_);
v___x_2101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2101_, 0, v___x_2097_);
lean_ctor_set(v___x_2101_, 1, v___x_2100_);
v___x_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2095_);
lean_ctor_set(v___x_2102_, 1, v___x_2101_);
return v___x_2102_;
}
else
{
lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; uint8_t v___x_2110_; 
v___x_2103_ = lean_nat_sub(v___x_2089_, v_i_2084_);
lean_dec(v___x_2089_);
v___x_2104_ = lean_unsigned_to_nat(1u);
v___x_2105_ = lean_nat_sub(v___x_2103_, v___x_2104_);
v___x_2106_ = l_Subarray_get___redArg(v_left_2082_, v___x_2105_);
lean_dec(v___x_2105_);
v___x_2107_ = lean_nat_sub(v___x_2091_, v_i_2084_);
lean_dec(v___x_2091_);
v___x_2108_ = lean_nat_sub(v___x_2107_, v___x_2104_);
v___x_2109_ = l_Subarray_get___redArg(v_right_2083_, v___x_2108_);
lean_dec(v___x_2108_);
v___x_2110_ = lean_string_dec_eq(v___x_2106_, v___x_2109_);
lean_dec(v___x_2109_);
lean_dec(v___x_2106_);
if (v___x_2110_ == 0)
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
lean_dec(v_i_2084_);
lean_inc_ref(v_left_2082_);
v___x_2111_ = l_Subarray_take___redArg(v_left_2082_, v___x_2103_);
v___x_2112_ = l_Subarray_take___redArg(v_right_2083_, v___x_2107_);
lean_dec(v___x_2107_);
v___x_2113_ = l_Subarray_drop___redArg(v_left_2082_, v___x_2103_);
lean_dec(v___x_2103_);
v___x_2114_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2115_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(v___x_2113_, v___x_2114_);
v___x_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2112_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
v___x_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2111_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
return v___x_2117_;
}
else
{
lean_object* v___x_2118_; 
lean_dec(v___x_2107_);
lean_dec(v___x_2103_);
v___x_2118_ = lean_nat_add(v_i_2084_, v___x_2104_);
lean_dec(v_i_2084_);
v_i_2084_ = v___x_2118_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5(lean_object* v_left_2121_, lean_object* v_right_2122_){
_start:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = lean_unsigned_to_nat(0u);
v___x_2124_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8(v_left_2121_, v_right_2122_, v___x_2123_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___redArg(lean_object* v_histogram_2125_, lean_object* v_index_2126_, lean_object* v_val_2127_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_histogram_2125_, v_val_2127_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2129_ = lean_unsigned_to_nat(1u);
v___x_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2130_, 0, v_index_2126_);
v___x_2131_ = lean_unsigned_to_nat(0u);
v___x_2132_ = lean_box(0);
v___x_2133_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2133_, 0, v___x_2129_);
lean_ctor_set(v___x_2133_, 1, v___x_2130_);
lean_ctor_set(v___x_2133_, 2, v___x_2131_);
lean_ctor_set(v___x_2133_, 3, v___x_2132_);
v___x_2134_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_2125_, v_val_2127_, v___x_2133_);
return v___x_2134_;
}
else
{
lean_object* v_val_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2156_; 
v_val_2135_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2137_ = v___x_2128_;
v_isShared_2138_ = v_isSharedCheck_2156_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_val_2135_);
lean_dec(v___x_2128_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2156_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v_leftCount_2139_; lean_object* v_rightCount_2140_; lean_object* v_rightIndex_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2154_; 
v_leftCount_2139_ = lean_ctor_get(v_val_2135_, 0);
v_rightCount_2140_ = lean_ctor_get(v_val_2135_, 2);
v_rightIndex_2141_ = lean_ctor_get(v_val_2135_, 3);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_val_2135_);
if (v_isSharedCheck_2154_ == 0)
{
lean_object* v_unused_2155_; 
v_unused_2155_ = lean_ctor_get(v_val_2135_, 1);
lean_dec(v_unused_2155_);
v___x_2143_ = v_val_2135_;
v_isShared_2144_ = v_isSharedCheck_2154_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_rightIndex_2141_);
lean_inc(v_rightCount_2140_);
lean_inc(v_leftCount_2139_);
lean_dec(v_val_2135_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2154_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2148_; 
v___x_2145_ = lean_unsigned_to_nat(1u);
v___x_2146_ = lean_nat_add(v_leftCount_2139_, v___x_2145_);
lean_dec(v_leftCount_2139_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v_index_2126_);
v___x_2148_ = v___x_2137_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_index_2126_);
v___x_2148_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
lean_object* v___x_2150_; 
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 1, v___x_2148_);
lean_ctor_set(v___x_2143_, 0, v___x_2146_);
v___x_2150_ = v___x_2143_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2146_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2152_, 2, v_rightCount_2140_);
lean_ctor_set(v_reuseFailAlloc_2152_, 3, v_rightIndex_2141_);
v___x_2150_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2151_; 
v___x_2151_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_2125_, v_val_2127_, v___x_2150_);
return v___x_2151_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(lean_object* v_upperBound_2157_, lean_object* v_fst_2158_, lean_object* v___x_2159_, lean_object* v_fst_2160_, lean_object* v_a_2161_, lean_object* v_b_2162_){
_start:
{
uint8_t v___x_2163_; 
v___x_2163_ = lean_nat_dec_lt(v_a_2161_, v_upperBound_2157_);
if (v___x_2163_ == 0)
{
lean_dec(v_a_2161_);
return v_b_2162_;
}
else
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2164_ = l_Subarray_get___redArg(v_fst_2160_, v_a_2161_);
lean_inc(v_a_2161_);
v___x_2165_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___redArg(v_b_2162_, v_a_2161_, v___x_2164_);
v___x_2166_ = lean_unsigned_to_nat(1u);
v___x_2167_ = lean_nat_add(v_a_2161_, v___x_2166_);
lean_dec(v_a_2161_);
v_a_2161_ = v___x_2167_;
v_b_2162_ = v___x_2165_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg___boxed(lean_object* v_upperBound_2169_, lean_object* v_fst_2170_, lean_object* v___x_2171_, lean_object* v_fst_2172_, lean_object* v_a_2173_, lean_object* v_b_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(v_upperBound_2169_, v_fst_2170_, v___x_2171_, v_fst_2172_, v_a_2173_, v_b_2174_);
lean_dec_ref(v_fst_2172_);
lean_dec(v___x_2171_);
lean_dec_ref(v_fst_2170_);
lean_dec(v_upperBound_2169_);
return v_res_2175_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = lean_box(0);
v___x_2177_ = lean_unsigned_to_nat(16u);
v___x_2178_ = lean_mk_array(v___x_2177_, v___x_2176_);
return v___x_2178_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v_hist_2181_; 
v___x_2179_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0);
v___x_2180_ = lean_unsigned_to_nat(0u);
v_hist_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_2181_, 0, v___x_2180_);
lean_ctor_set(v_hist_2181_, 1, v___x_2179_);
return v_hist_2181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(lean_object* v_left_2182_, lean_object* v_right_2183_){
_start:
{
lean_object* v___x_2184_; lean_object* v_snd_2185_; lean_object* v_fst_2186_; lean_object* v_fst_2187_; lean_object* v_snd_2188_; lean_object* v___x_2189_; lean_object* v_snd_2190_; lean_object* v_fst_2191_; lean_object* v_fst_2192_; lean_object* v_snd_2193_; lean_object* v_start_2194_; lean_object* v_stop_2195_; lean_object* v___x_2196_; lean_object* v_hist_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v_start_2200_; lean_object* v_stop_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v_buckets_2204_; lean_object* v___x_2205_; lean_object* v___y_2207_; lean_object* v___x_2233_; lean_object* v___x_2234_; uint8_t v___x_2235_; 
v___x_2184_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4(v_left_2182_, v_right_2183_);
v_snd_2185_ = lean_ctor_get(v___x_2184_, 1);
lean_inc(v_snd_2185_);
v_fst_2186_ = lean_ctor_get(v___x_2184_, 0);
lean_inc(v_fst_2186_);
lean_dec_ref(v___x_2184_);
v_fst_2187_ = lean_ctor_get(v_snd_2185_, 0);
lean_inc(v_fst_2187_);
v_snd_2188_ = lean_ctor_get(v_snd_2185_, 1);
lean_inc(v_snd_2188_);
lean_dec(v_snd_2185_);
v___x_2189_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5(v_fst_2187_, v_snd_2188_);
v_snd_2190_ = lean_ctor_get(v___x_2189_, 1);
lean_inc(v_snd_2190_);
v_fst_2191_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_fst_2191_);
lean_dec_ref(v___x_2189_);
v_fst_2192_ = lean_ctor_get(v_snd_2190_, 0);
lean_inc(v_fst_2192_);
v_snd_2193_ = lean_ctor_get(v_snd_2190_, 1);
lean_inc(v_snd_2193_);
lean_dec(v_snd_2190_);
v_start_2194_ = lean_ctor_get(v_fst_2191_, 1);
v_stop_2195_ = lean_ctor_get(v_fst_2191_, 2);
v___x_2196_ = lean_unsigned_to_nat(0u);
v_hist_2197_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1);
v___x_2198_ = lean_nat_sub(v_stop_2195_, v_start_2194_);
v___x_2199_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(v___x_2198_, v_fst_2192_, v___x_2198_, v_fst_2191_, v___x_2196_, v_hist_2197_);
v_start_2200_ = lean_ctor_get(v_fst_2192_, 1);
v_stop_2201_ = lean_ctor_get(v_fst_2192_, 2);
v___x_2202_ = lean_nat_sub(v_stop_2201_, v_start_2200_);
v___x_2203_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(v___x_2202_, v___x_2202_, v_fst_2192_, v___x_2198_, v___x_2196_, v___x_2199_);
lean_dec(v___x_2198_);
lean_dec(v___x_2202_);
v_buckets_2204_ = lean_ctor_get(v___x_2203_, 1);
lean_inc_ref(v_buckets_2204_);
lean_dec_ref(v___x_2203_);
v___x_2205_ = lean_box(0);
v___x_2233_ = lean_box(0);
v___x_2234_ = lean_array_get_size(v_buckets_2204_);
v___x_2235_ = lean_nat_dec_lt(v___x_2196_, v___x_2234_);
if (v___x_2235_ == 0)
{
lean_dec_ref(v_buckets_2204_);
v___y_2207_ = v___x_2233_;
goto v___jp_2206_;
}
else
{
size_t v___x_2236_; size_t v___x_2237_; lean_object* v___x_2238_; 
v___x_2236_ = lean_usize_of_nat(v___x_2234_);
v___x_2237_ = ((size_t)0ULL);
v___x_2238_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8(v_buckets_2204_, v___x_2236_, v___x_2237_, v___x_2233_);
lean_dec_ref(v_buckets_2204_);
v___y_2207_ = v___x_2238_;
goto v___jp_2206_;
}
v___jp_2206_:
{
lean_object* v___x_2208_; 
v___x_2208_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(v___y_2207_, v___x_2205_);
lean_dec(v___y_2207_);
if (lean_obj_tag(v___x_2208_) == 1)
{
lean_object* v_val_2209_; lean_object* v_snd_2210_; lean_object* v_snd_2211_; lean_object* v_fst_2212_; lean_object* v_fst_2213_; lean_object* v_snd_2214_; lean_object* v___x_2215_; lean_object* v_fst_2216_; lean_object* v_snd_2217_; lean_object* v___x_2218_; lean_object* v_fst_2219_; lean_object* v_snd_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v_val_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_val_2209_);
lean_dec_ref_known(v___x_2208_, 1);
v_snd_2210_ = lean_ctor_get(v_val_2209_, 1);
lean_inc(v_snd_2210_);
lean_dec(v_val_2209_);
v_snd_2211_ = lean_ctor_get(v_snd_2210_, 1);
lean_inc(v_snd_2211_);
v_fst_2212_ = lean_ctor_get(v_snd_2210_, 0);
lean_inc(v_fst_2212_);
lean_dec(v_snd_2210_);
v_fst_2213_ = lean_ctor_get(v_snd_2211_, 0);
lean_inc(v_fst_2213_);
v_snd_2214_ = lean_ctor_get(v_snd_2211_, 1);
lean_inc(v_snd_2214_);
lean_dec(v_snd_2211_);
v___x_2215_ = l_Subarray_split___redArg(v_fst_2191_, v_fst_2213_);
lean_dec(v_fst_2213_);
v_fst_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_fst_2216_);
v_snd_2217_ = lean_ctor_get(v___x_2215_, 1);
lean_inc(v_snd_2217_);
lean_dec_ref(v___x_2215_);
v___x_2218_ = l_Subarray_split___redArg(v_fst_2192_, v_snd_2214_);
lean_dec(v_snd_2214_);
v_fst_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_fst_2219_);
v_snd_2220_ = lean_ctor_get(v___x_2218_, 1);
lean_inc(v_snd_2220_);
lean_dec_ref(v___x_2218_);
v___x_2221_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v_fst_2216_, v_fst_2219_);
v___x_2222_ = l_Array_append___redArg(v_fst_2186_, v___x_2221_);
lean_dec_ref(v___x_2221_);
v___x_2223_ = lean_unsigned_to_nat(1u);
v___x_2224_ = lean_mk_empty_array_with_capacity(v___x_2223_);
v___x_2225_ = lean_array_push(v___x_2224_, v_fst_2212_);
v___x_2226_ = l_Array_append___redArg(v___x_2222_, v___x_2225_);
lean_dec_ref(v___x_2225_);
v___x_2227_ = l_Subarray_drop___redArg(v_snd_2217_, v___x_2223_);
v___x_2228_ = l_Subarray_drop___redArg(v_snd_2220_, v___x_2223_);
v___x_2229_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v___x_2227_, v___x_2228_);
v___x_2230_ = l_Array_append___redArg(v___x_2226_, v___x_2229_);
lean_dec_ref(v___x_2229_);
v___x_2231_ = l_Array_append___redArg(v___x_2230_, v_snd_2193_);
lean_dec(v_snd_2193_);
return v___x_2231_;
}
else
{
lean_object* v___x_2232_; 
lean_dec(v___x_2208_);
lean_dec(v_fst_2192_);
lean_dec(v_fst_2191_);
v___x_2232_ = l_Array_append___redArg(v_fst_2186_, v_snd_2193_);
lean_dec(v_snd_2193_);
return v___x_2232_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(lean_object* v___x_2239_, lean_object* v_original_2240_, lean_object* v_a_2241_){
_start:
{
lean_object* v_fst_2242_; lean_object* v_snd_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2262_; 
v_fst_2242_ = lean_ctor_get(v_a_2241_, 0);
v_snd_2243_ = lean_ctor_get(v_a_2241_, 1);
v_isSharedCheck_2262_ = !lean_is_exclusive(v_a_2241_);
if (v_isSharedCheck_2262_ == 0)
{
v___x_2245_ = v_a_2241_;
v_isShared_2246_ = v_isSharedCheck_2262_;
goto v_resetjp_2244_;
}
else
{
lean_inc(v_snd_2243_);
lean_inc(v_fst_2242_);
lean_dec(v_a_2241_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2262_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
uint8_t v___x_2247_; 
v___x_2247_ = lean_nat_dec_lt(v_snd_2243_, v___x_2239_);
if (v___x_2247_ == 0)
{
lean_object* v___x_2249_; 
if (v_isShared_2246_ == 0)
{
v___x_2249_ = v___x_2245_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v_fst_2242_);
lean_ctor_set(v_reuseFailAlloc_2250_, 1, v_snd_2243_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
else
{
uint8_t v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2255_; 
v___x_2251_ = 1;
v___x_2252_ = lean_array_fget_borrowed(v_original_2240_, v_snd_2243_);
v___x_2253_ = lean_box(v___x_2251_);
lean_inc(v___x_2252_);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 1, v___x_2252_);
lean_ctor_set(v___x_2245_, 0, v___x_2253_);
v___x_2255_ = v___x_2245_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v___x_2253_);
lean_ctor_set(v_reuseFailAlloc_2261_, 1, v___x_2252_);
v___x_2255_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2256_ = lean_array_push(v_fst_2242_, v___x_2255_);
v___x_2257_ = lean_unsigned_to_nat(1u);
v___x_2258_ = lean_nat_add(v_snd_2243_, v___x_2257_);
lean_dec(v_snd_2243_);
v___x_2259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2259_, 0, v___x_2256_);
lean_ctor_set(v___x_2259_, 1, v___x_2258_);
v_a_2241_ = v___x_2259_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg___boxed(lean_object* v___x_2263_, lean_object* v_original_2264_, lean_object* v_a_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2263_, v_original_2264_, v_a_2265_);
lean_dec_ref(v_original_2264_);
lean_dec(v___x_2263_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(lean_object* v___x_2267_, lean_object* v_edited_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v_fst_2270_; lean_object* v_snd_2271_; lean_object* v___x_2273_; uint8_t v_isShared_2274_; uint8_t v_isSharedCheck_2290_; 
v_fst_2270_ = lean_ctor_get(v_a_2269_, 0);
v_snd_2271_ = lean_ctor_get(v_a_2269_, 1);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_a_2269_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2273_ = v_a_2269_;
v_isShared_2274_ = v_isSharedCheck_2290_;
goto v_resetjp_2272_;
}
else
{
lean_inc(v_snd_2271_);
lean_inc(v_fst_2270_);
lean_dec(v_a_2269_);
v___x_2273_ = lean_box(0);
v_isShared_2274_ = v_isSharedCheck_2290_;
goto v_resetjp_2272_;
}
v_resetjp_2272_:
{
uint8_t v___x_2275_; 
v___x_2275_ = lean_nat_dec_lt(v_snd_2271_, v___x_2267_);
if (v___x_2275_ == 0)
{
lean_object* v___x_2277_; 
if (v_isShared_2274_ == 0)
{
v___x_2277_ = v___x_2273_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_fst_2270_);
lean_ctor_set(v_reuseFailAlloc_2278_, 1, v_snd_2271_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
else
{
uint8_t v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2283_; 
v___x_2279_ = 0;
v___x_2280_ = lean_array_fget_borrowed(v_edited_2268_, v_snd_2271_);
v___x_2281_ = lean_box(v___x_2279_);
lean_inc(v___x_2280_);
if (v_isShared_2274_ == 0)
{
lean_ctor_set(v___x_2273_, 1, v___x_2280_);
lean_ctor_set(v___x_2273_, 0, v___x_2281_);
v___x_2283_ = v___x_2273_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2281_);
lean_ctor_set(v_reuseFailAlloc_2289_, 1, v___x_2280_);
v___x_2283_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2284_ = lean_array_push(v_fst_2270_, v___x_2283_);
v___x_2285_ = lean_unsigned_to_nat(1u);
v___x_2286_ = lean_nat_add(v_snd_2271_, v___x_2285_);
lean_dec(v_snd_2271_);
v___x_2287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2284_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
v_a_2269_ = v___x_2287_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg___boxed(lean_object* v___x_2291_, lean_object* v_edited_2292_, lean_object* v_a_2293_){
_start:
{
lean_object* v_res_2294_; 
v_res_2294_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2291_, v_edited_2292_, v_a_2293_);
lean_dec_ref(v_edited_2292_);
lean_dec(v___x_2291_);
return v_res_2294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(lean_object* v___x_2295_, lean_object* v_original_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_){
_start:
{
lean_object* v_fst_2299_; lean_object* v_snd_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2324_; 
v_fst_2299_ = lean_ctor_get(v_a_2298_, 0);
v_snd_2300_ = lean_ctor_get(v_a_2298_, 1);
v_isSharedCheck_2324_ = !lean_is_exclusive(v_a_2298_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2302_ = v_a_2298_;
v_isShared_2303_ = v_isSharedCheck_2324_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_snd_2300_);
lean_inc(v_fst_2299_);
lean_dec(v_a_2298_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2324_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
uint8_t v___x_2304_; 
v___x_2304_ = lean_nat_dec_lt(v_snd_2300_, v___x_2295_);
if (v___x_2304_ == 0)
{
lean_object* v___x_2306_; 
if (v_isShared_2303_ == 0)
{
v___x_2306_ = v___x_2302_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_fst_2299_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v_snd_2300_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
else
{
lean_object* v___x_2308_; lean_object* v___x_2309_; uint8_t v___x_2310_; 
v___x_2308_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2309_ = lean_array_get_borrowed(v___x_2308_, v_original_2296_, v_snd_2300_);
v___x_2310_ = lean_string_dec_eq(v___x_2309_, v_a_2297_);
if (v___x_2310_ == 0)
{
uint8_t v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2314_; 
v___x_2311_ = 1;
v___x_2312_ = lean_box(v___x_2311_);
lean_inc(v___x_2309_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 1, v___x_2309_);
lean_ctor_set(v___x_2302_, 0, v___x_2312_);
v___x_2314_ = v___x_2302_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2312_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v___x_2309_);
v___x_2314_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v___x_2315_ = lean_array_push(v_fst_2299_, v___x_2314_);
v___x_2316_ = lean_unsigned_to_nat(1u);
v___x_2317_ = lean_nat_add(v_snd_2300_, v___x_2316_);
lean_dec(v_snd_2300_);
v___x_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2315_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
v_a_2298_ = v___x_2318_;
goto _start;
}
}
else
{
lean_object* v___x_2322_; 
if (v_isShared_2303_ == 0)
{
v___x_2322_ = v___x_2302_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_fst_2299_);
lean_ctor_set(v_reuseFailAlloc_2323_, 1, v_snd_2300_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg___boxed(lean_object* v___x_2325_, lean_object* v_original_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2325_, v_original_2326_, v_a_2327_, v_a_2328_);
lean_dec_ref(v_a_2327_);
lean_dec_ref(v_original_2326_);
lean_dec(v___x_2325_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(lean_object* v___x_2330_, lean_object* v_edited_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_){
_start:
{
lean_object* v_fst_2334_; lean_object* v_snd_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2359_; 
v_fst_2334_ = lean_ctor_get(v_a_2333_, 0);
v_snd_2335_ = lean_ctor_get(v_a_2333_, 1);
v_isSharedCheck_2359_ = !lean_is_exclusive(v_a_2333_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2337_ = v_a_2333_;
v_isShared_2338_ = v_isSharedCheck_2359_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_snd_2335_);
lean_inc(v_fst_2334_);
lean_dec(v_a_2333_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2359_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
uint8_t v___x_2339_; 
v___x_2339_ = lean_nat_dec_lt(v_snd_2335_, v___x_2330_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2341_; 
if (v_isShared_2338_ == 0)
{
v___x_2341_ = v___x_2337_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_fst_2334_);
lean_ctor_set(v_reuseFailAlloc_2342_, 1, v_snd_2335_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
else
{
lean_object* v___x_2343_; lean_object* v___x_2344_; uint8_t v___x_2345_; 
v___x_2343_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2344_ = lean_array_get_borrowed(v___x_2343_, v_edited_2331_, v_snd_2335_);
v___x_2345_ = lean_string_dec_eq(v___x_2344_, v_a_2332_);
if (v___x_2345_ == 0)
{
uint8_t v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2349_; 
v___x_2346_ = 0;
v___x_2347_ = lean_box(v___x_2346_);
lean_inc(v___x_2344_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 1, v___x_2344_);
lean_ctor_set(v___x_2337_, 0, v___x_2347_);
v___x_2349_ = v___x_2337_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2347_);
lean_ctor_set(v_reuseFailAlloc_2355_, 1, v___x_2344_);
v___x_2349_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2350_ = lean_array_push(v_fst_2334_, v___x_2349_);
v___x_2351_ = lean_unsigned_to_nat(1u);
v___x_2352_ = lean_nat_add(v_snd_2335_, v___x_2351_);
lean_dec(v_snd_2335_);
v___x_2353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2350_);
lean_ctor_set(v___x_2353_, 1, v___x_2352_);
v_a_2333_ = v___x_2353_;
goto _start;
}
}
else
{
lean_object* v___x_2357_; 
if (v_isShared_2338_ == 0)
{
v___x_2357_ = v___x_2337_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_fst_2334_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_snd_2335_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg___boxed(lean_object* v___x_2360_, lean_object* v_edited_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2360_, v_edited_2361_, v_a_2362_, v_a_2363_);
lean_dec_ref(v_a_2362_);
lean_dec_ref(v_edited_2361_);
lean_dec(v___x_2360_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(lean_object* v___x_2365_, lean_object* v_original_2366_, lean_object* v___x_2367_, lean_object* v_edited_2368_, lean_object* v_as_2369_, size_t v_sz_2370_, size_t v_i_2371_, lean_object* v_b_2372_){
_start:
{
uint8_t v___x_2373_; 
v___x_2373_ = lean_usize_dec_lt(v_i_2371_, v_sz_2370_);
if (v___x_2373_ == 0)
{
return v_b_2372_;
}
else
{
lean_object* v_snd_2374_; lean_object* v_fst_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2422_; 
v_snd_2374_ = lean_ctor_get(v_b_2372_, 1);
v_fst_2375_ = lean_ctor_get(v_b_2372_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v_b_2372_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2377_ = v_b_2372_;
v_isShared_2378_ = v_isSharedCheck_2422_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_snd_2374_);
lean_inc(v_fst_2375_);
lean_dec(v_b_2372_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2422_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v_fst_2379_; lean_object* v_snd_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2421_; 
v_fst_2379_ = lean_ctor_get(v_snd_2374_, 0);
v_snd_2380_ = lean_ctor_get(v_snd_2374_, 1);
v_isSharedCheck_2421_ = !lean_is_exclusive(v_snd_2374_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2382_ = v_snd_2374_;
v_isShared_2383_ = v_isSharedCheck_2421_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_snd_2380_);
lean_inc(v_fst_2379_);
lean_dec(v_snd_2374_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2421_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v_a_2384_; lean_object* v___x_2386_; 
v_a_2384_ = lean_array_uget_borrowed(v_as_2369_, v_i_2371_);
if (v_isShared_2383_ == 0)
{
lean_ctor_set(v___x_2382_, 1, v_fst_2379_);
lean_ctor_set(v___x_2382_, 0, v_fst_2375_);
v___x_2386_ = v___x_2382_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_fst_2375_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_fst_2379_);
v___x_2386_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
lean_object* v___x_2387_; lean_object* v_fst_2388_; lean_object* v_snd_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2419_; 
v___x_2387_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2365_, v_original_2366_, v_a_2384_, v___x_2386_);
v_fst_2388_ = lean_ctor_get(v___x_2387_, 0);
v_snd_2389_ = lean_ctor_get(v___x_2387_, 1);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2391_ = v___x_2387_;
v_isShared_2392_ = v_isSharedCheck_2419_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_snd_2389_);
lean_inc(v_fst_2388_);
lean_dec(v___x_2387_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2419_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 1, v_snd_2380_);
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_fst_2388_);
lean_ctor_set(v_reuseFailAlloc_2418_, 1, v_snd_2380_);
v___x_2394_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
lean_object* v___x_2395_; lean_object* v_fst_2396_; lean_object* v_snd_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2417_; 
v___x_2395_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2367_, v_edited_2368_, v_a_2384_, v___x_2394_);
v_fst_2396_ = lean_ctor_get(v___x_2395_, 0);
v_snd_2397_ = lean_ctor_get(v___x_2395_, 1);
v_isSharedCheck_2417_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2417_ == 0)
{
v___x_2399_ = v___x_2395_;
v_isShared_2400_ = v_isSharedCheck_2417_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_snd_2397_);
lean_inc(v_fst_2396_);
lean_dec(v___x_2395_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2417_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
uint8_t v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2404_; 
v___x_2401_ = 2;
v___x_2402_ = lean_box(v___x_2401_);
lean_inc(v_a_2384_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 1, v_a_2384_);
lean_ctor_set(v___x_2399_, 0, v___x_2402_);
v___x_2404_ = v___x_2399_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2402_);
lean_ctor_set(v_reuseFailAlloc_2416_, 1, v_a_2384_);
v___x_2404_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2410_; 
v___x_2405_ = lean_array_push(v_fst_2396_, v___x_2404_);
v___x_2406_ = lean_unsigned_to_nat(1u);
v___x_2407_ = lean_nat_add(v_snd_2389_, v___x_2406_);
lean_dec(v_snd_2389_);
v___x_2408_ = lean_nat_add(v_snd_2397_, v___x_2406_);
lean_dec(v_snd_2397_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 1, v___x_2408_);
lean_ctor_set(v___x_2377_, 0, v___x_2407_);
v___x_2410_ = v___x_2377_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v___x_2407_);
lean_ctor_set(v_reuseFailAlloc_2415_, 1, v___x_2408_);
v___x_2410_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
lean_object* v___x_2411_; size_t v___x_2412_; size_t v___x_2413_; 
v___x_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2405_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
v___x_2412_ = ((size_t)1ULL);
v___x_2413_ = lean_usize_add(v_i_2371_, v___x_2412_);
v_i_2371_ = v___x_2413_;
v_b_2372_ = v___x_2411_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14___boxed(lean_object* v___x_2423_, lean_object* v_original_2424_, lean_object* v___x_2425_, lean_object* v_edited_2426_, lean_object* v_as_2427_, lean_object* v_sz_2428_, lean_object* v_i_2429_, lean_object* v_b_2430_){
_start:
{
size_t v_sz_boxed_2431_; size_t v_i_boxed_2432_; lean_object* v_res_2433_; 
v_sz_boxed_2431_ = lean_unbox_usize(v_sz_2428_);
lean_dec(v_sz_2428_);
v_i_boxed_2432_ = lean_unbox_usize(v_i_2429_);
lean_dec(v_i_2429_);
v_res_2433_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v___x_2423_, v_original_2424_, v___x_2425_, v_edited_2426_, v_as_2427_, v_sz_boxed_2431_, v_i_boxed_2432_, v_b_2430_);
lean_dec_ref(v_as_2427_);
lean_dec_ref(v_edited_2426_);
lean_dec(v___x_2425_);
lean_dec_ref(v_original_2424_);
lean_dec(v___x_2423_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(lean_object* v___x_2434_, lean_object* v_edited_2435_, lean_object* v___x_2436_, lean_object* v_original_2437_, lean_object* v_as_2438_, size_t v_sz_2439_, size_t v_i_2440_, lean_object* v_b_2441_){
_start:
{
uint8_t v___x_2442_; 
v___x_2442_ = lean_usize_dec_lt(v_i_2440_, v_sz_2439_);
if (v___x_2442_ == 0)
{
return v_b_2441_;
}
else
{
lean_object* v_snd_2443_; lean_object* v_fst_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2491_; 
v_snd_2443_ = lean_ctor_get(v_b_2441_, 1);
v_fst_2444_ = lean_ctor_get(v_b_2441_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v_b_2441_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2446_ = v_b_2441_;
v_isShared_2447_ = v_isSharedCheck_2491_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_snd_2443_);
lean_inc(v_fst_2444_);
lean_dec(v_b_2441_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2491_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v_fst_2448_; lean_object* v_snd_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2490_; 
v_fst_2448_ = lean_ctor_get(v_snd_2443_, 0);
v_snd_2449_ = lean_ctor_get(v_snd_2443_, 1);
v_isSharedCheck_2490_ = !lean_is_exclusive(v_snd_2443_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2451_ = v_snd_2443_;
v_isShared_2452_ = v_isSharedCheck_2490_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_snd_2449_);
lean_inc(v_fst_2448_);
lean_dec(v_snd_2443_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2490_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v_a_2453_; lean_object* v___x_2455_; 
v_a_2453_ = lean_array_uget_borrowed(v_as_2438_, v_i_2440_);
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 1, v_fst_2448_);
lean_ctor_set(v___x_2451_, 0, v_fst_2444_);
v___x_2455_ = v___x_2451_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_fst_2444_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v_fst_2448_);
v___x_2455_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
lean_object* v___x_2456_; lean_object* v_fst_2457_; lean_object* v_snd_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2488_; 
v___x_2456_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2436_, v_original_2437_, v_a_2453_, v___x_2455_);
v_fst_2457_ = lean_ctor_get(v___x_2456_, 0);
v_snd_2458_ = lean_ctor_get(v___x_2456_, 1);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2460_ = v___x_2456_;
v_isShared_2461_ = v_isSharedCheck_2488_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_snd_2458_);
lean_inc(v_fst_2457_);
lean_dec(v___x_2456_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2488_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 1, v_snd_2449_);
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_fst_2457_);
lean_ctor_set(v_reuseFailAlloc_2487_, 1, v_snd_2449_);
v___x_2463_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
lean_object* v___x_2464_; lean_object* v_fst_2465_; lean_object* v_snd_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2486_; 
v___x_2464_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2434_, v_edited_2435_, v_a_2453_, v___x_2463_);
v_fst_2465_ = lean_ctor_get(v___x_2464_, 0);
v_snd_2466_ = lean_ctor_get(v___x_2464_, 1);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2468_ = v___x_2464_;
v_isShared_2469_ = v_isSharedCheck_2486_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_snd_2466_);
lean_inc(v_fst_2465_);
lean_dec(v___x_2464_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2486_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
uint8_t v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2473_; 
v___x_2470_ = 2;
v___x_2471_ = lean_box(v___x_2470_);
lean_inc(v_a_2453_);
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 1, v_a_2453_);
lean_ctor_set(v___x_2468_, 0, v___x_2471_);
v___x_2473_ = v___x_2468_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2471_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v_a_2453_);
v___x_2473_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2479_; 
v___x_2474_ = lean_array_push(v_fst_2465_, v___x_2473_);
v___x_2475_ = lean_unsigned_to_nat(1u);
v___x_2476_ = lean_nat_add(v_snd_2458_, v___x_2475_);
lean_dec(v_snd_2458_);
v___x_2477_ = lean_nat_add(v_snd_2466_, v___x_2475_);
lean_dec(v_snd_2466_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 1, v___x_2477_);
lean_ctor_set(v___x_2446_, 0, v___x_2476_);
v___x_2479_ = v___x_2446_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2476_);
lean_ctor_set(v_reuseFailAlloc_2484_, 1, v___x_2477_);
v___x_2479_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
lean_object* v___x_2480_; size_t v___x_2481_; size_t v___x_2482_; lean_object* v___x_2483_; 
v___x_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2474_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
v___x_2481_ = ((size_t)1ULL);
v___x_2482_ = lean_usize_add(v_i_2440_, v___x_2481_);
v___x_2483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v___x_2436_, v_original_2437_, v___x_2434_, v_edited_2435_, v_as_2438_, v_sz_2439_, v___x_2482_, v___x_2480_);
return v___x_2483_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4___boxed(lean_object* v___x_2492_, lean_object* v_edited_2493_, lean_object* v___x_2494_, lean_object* v_original_2495_, lean_object* v_as_2496_, lean_object* v_sz_2497_, lean_object* v_i_2498_, lean_object* v_b_2499_){
_start:
{
size_t v_sz_boxed_2500_; size_t v_i_boxed_2501_; lean_object* v_res_2502_; 
v_sz_boxed_2500_ = lean_unbox_usize(v_sz_2497_);
lean_dec(v_sz_2497_);
v_i_boxed_2501_ = lean_unbox_usize(v_i_2498_);
lean_dec(v_i_2498_);
v_res_2502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v___x_2492_, v_edited_2493_, v___x_2494_, v_original_2495_, v_as_2496_, v_sz_boxed_2500_, v_i_boxed_2501_, v_b_2499_);
lean_dec_ref(v_as_2496_);
lean_dec_ref(v_original_2495_);
lean_dec(v___x_2494_);
lean_dec_ref(v_edited_2493_);
lean_dec(v___x_2492_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(size_t v_sz_2503_, size_t v_i_2504_, lean_object* v_bs_2505_){
_start:
{
uint8_t v___x_2506_; 
v___x_2506_ = lean_usize_dec_lt(v_i_2504_, v_sz_2503_);
if (v___x_2506_ == 0)
{
return v_bs_2505_;
}
else
{
lean_object* v_v_2507_; lean_object* v___x_2508_; lean_object* v_bs_x27_2509_; uint8_t v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; size_t v___x_2513_; size_t v___x_2514_; lean_object* v___x_2515_; 
v_v_2507_ = lean_array_uget(v_bs_2505_, v_i_2504_);
v___x_2508_ = lean_unsigned_to_nat(0u);
v_bs_x27_2509_ = lean_array_uset(v_bs_2505_, v_i_2504_, v___x_2508_);
v___x_2510_ = 1;
v___x_2511_ = lean_box(v___x_2510_);
v___x_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2511_);
lean_ctor_set(v___x_2512_, 1, v_v_2507_);
v___x_2513_ = ((size_t)1ULL);
v___x_2514_ = lean_usize_add(v_i_2504_, v___x_2513_);
v___x_2515_ = lean_array_uset(v_bs_x27_2509_, v_i_2504_, v___x_2512_);
v_i_2504_ = v___x_2514_;
v_bs_2505_ = v___x_2515_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7___boxed(lean_object* v_sz_2517_, lean_object* v_i_2518_, lean_object* v_bs_2519_){
_start:
{
size_t v_sz_boxed_2520_; size_t v_i_boxed_2521_; lean_object* v_res_2522_; 
v_sz_boxed_2520_ = lean_unbox_usize(v_sz_2517_);
lean_dec(v_sz_2517_);
v_i_boxed_2521_ = lean_unbox_usize(v_i_2518_);
lean_dec(v_i_2518_);
v_res_2522_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_boxed_2520_, v_i_boxed_2521_, v_bs_2519_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(lean_object* v_original_2528_, lean_object* v_edited_2529_){
_start:
{
lean_object* v_i_2530_; lean_object* v___x_2531_; uint8_t v___x_2532_; 
v_i_2530_ = lean_unsigned_to_nat(0u);
v___x_2531_ = lean_array_get_size(v_original_2528_);
v___x_2532_ = lean_nat_dec_lt(v_i_2530_, v___x_2531_);
if (v___x_2532_ == 0)
{
size_t v_sz_2533_; size_t v___x_2534_; lean_object* v___x_2535_; 
lean_dec_ref(v_original_2528_);
v_sz_2533_ = lean_array_size(v_edited_2529_);
v___x_2534_ = ((size_t)0ULL);
v___x_2535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_2533_, v___x_2534_, v_edited_2529_);
return v___x_2535_;
}
else
{
lean_object* v___x_2536_; uint8_t v___x_2537_; 
v___x_2536_ = lean_array_get_size(v_edited_2529_);
v___x_2537_ = lean_nat_dec_lt(v_i_2530_, v___x_2536_);
if (v___x_2537_ == 0)
{
size_t v_sz_2538_; size_t v___x_2539_; lean_object* v___x_2540_; 
lean_dec_ref(v_edited_2529_);
v_sz_2538_ = lean_array_size(v_original_2528_);
v___x_2539_ = ((size_t)0ULL);
v___x_2540_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_2538_, v___x_2539_, v_original_2528_);
return v___x_2540_;
}
else
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v_ds_2543_; lean_object* v___x_2544_; size_t v_sz_2545_; size_t v___x_2546_; lean_object* v___x_2547_; lean_object* v_snd_2548_; lean_object* v_fst_2549_; lean_object* v_fst_2550_; lean_object* v_snd_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2570_; 
lean_inc_ref(v_original_2528_);
v___x_2541_ = l_Array_toSubarray___redArg(v_original_2528_, v_i_2530_, v___x_2531_);
lean_inc_ref(v_edited_2529_);
v___x_2542_ = l_Array_toSubarray___redArg(v_edited_2529_, v_i_2530_, v___x_2536_);
v_ds_2543_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v___x_2541_, v___x_2542_);
v___x_2544_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__1));
v_sz_2545_ = lean_array_size(v_ds_2543_);
v___x_2546_ = ((size_t)0ULL);
v___x_2547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v___x_2536_, v_edited_2529_, v___x_2531_, v_original_2528_, v_ds_2543_, v_sz_2545_, v___x_2546_, v___x_2544_);
lean_dec_ref(v_ds_2543_);
v_snd_2548_ = lean_ctor_get(v___x_2547_, 1);
lean_inc(v_snd_2548_);
v_fst_2549_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_fst_2549_);
lean_dec_ref(v___x_2547_);
v_fst_2550_ = lean_ctor_get(v_snd_2548_, 0);
v_snd_2551_ = lean_ctor_get(v_snd_2548_, 1);
v_isSharedCheck_2570_ = !lean_is_exclusive(v_snd_2548_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2553_ = v_snd_2548_;
v_isShared_2554_ = v_isSharedCheck_2570_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_snd_2551_);
lean_inc(v_fst_2550_);
lean_dec(v_snd_2548_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2570_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 1, v_fst_2550_);
lean_ctor_set(v___x_2553_, 0, v_fst_2549_);
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_fst_2549_);
lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_fst_2550_);
v___x_2556_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
lean_object* v___x_2557_; lean_object* v_fst_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2567_; 
v___x_2557_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2531_, v_original_2528_, v___x_2556_);
lean_dec_ref(v_original_2528_);
v_fst_2558_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2567_ == 0)
{
lean_object* v_unused_2568_; 
v_unused_2568_ = lean_ctor_get(v___x_2557_, 1);
lean_dec(v_unused_2568_);
v___x_2560_ = v___x_2557_;
v_isShared_2561_ = v_isSharedCheck_2567_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_fst_2558_);
lean_dec(v___x_2557_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2567_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 1, v_snd_2551_);
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_fst_2558_);
lean_ctor_set(v_reuseFailAlloc_2566_, 1, v_snd_2551_);
v___x_2563_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
lean_object* v___x_2564_; lean_object* v_fst_2565_; 
v___x_2564_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2536_, v_edited_2529_, v___x_2563_);
lean_dec_ref(v_edited_2529_);
v_fst_2565_ = lean_ctor_get(v___x_2564_, 0);
lean_inc(v_fst_2565_);
lean_dec_ref(v___x_2564_);
return v_fst_2565_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(lean_object* v___x_2571_, uint8_t v_inSubst_2572_, lean_object* v___x_2573_, lean_object* v_____r_2574_, lean_object* v_wssIdx_2575_){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2576_ = lean_box(v_inSubst_2572_);
v___x_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2571_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
v___x_2578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2578_, 0, v_wssIdx_2575_);
lean_ctor_set(v___x_2578_, 1, v___x_2577_);
v___x_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2573_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
v___x_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1___boxed(lean_object* v___x_2581_, lean_object* v_inSubst_2582_, lean_object* v___x_2583_, lean_object* v_____r_2584_, lean_object* v_wssIdx_2585_){
_start:
{
uint8_t v_inSubst_boxed_2586_; lean_object* v_res_2587_; 
v_inSubst_boxed_2586_ = lean_unbox(v_inSubst_2582_);
v_res_2587_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2581_, v_inSubst_boxed_2586_, v___x_2583_, v_____r_2584_, v_wssIdx_2585_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(lean_object* v_fst_2588_, uint8_t v___x_2589_, lean_object* v_fst_2590_, lean_object* v___x_2591_, lean_object* v_00___2592_){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2593_ = lean_box(v___x_2589_);
v___x_2594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2594_, 0, v_fst_2588_);
lean_ctor_set(v___x_2594_, 1, v___x_2593_);
v___x_2595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2595_, 0, v_fst_2590_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
v___x_2596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2591_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
v___x_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2597_, 0, v___x_2596_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0___boxed(lean_object* v_fst_2598_, lean_object* v___x_2599_, lean_object* v_fst_2600_, lean_object* v___x_2601_, lean_object* v_00___2602_){
_start:
{
uint8_t v___x_9194__boxed_2603_; lean_object* v_res_2604_; 
v___x_9194__boxed_2603_ = lean_unbox(v___x_2599_);
v_res_2604_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2598_, v___x_9194__boxed_2603_, v_fst_2600_, v___x_2601_, v_00___2602_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(uint8_t v_inSubst_2605_, lean_object* v_snd_2606_, lean_object* v_fst_2607_, lean_object* v_____r_2608_, lean_object* v_withWs_2609_, lean_object* v_wssIdx_2610_){
_start:
{
lean_object* v_wss_x27Idx_2612_; uint8_t v___x_2618_; 
v___x_2618_ = lean_unbox(v_snd_2606_);
if (v___x_2618_ == 0)
{
v_wss_x27Idx_2612_ = v_fst_2607_;
goto v___jp_2611_;
}
else
{
lean_object* v___x_2619_; lean_object* v___x_2620_; 
v___x_2619_ = lean_unsigned_to_nat(1u);
v___x_2620_ = lean_nat_add(v_fst_2607_, v___x_2619_);
lean_dec(v_fst_2607_);
v_wss_x27Idx_2612_ = v___x_2620_;
goto v___jp_2611_;
}
v___jp_2611_:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; 
v___x_2613_ = lean_box(v_inSubst_2605_);
v___x_2614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2614_, 0, v_wss_x27Idx_2612_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
v___x_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2615_, 0, v_wssIdx_2610_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v___x_2616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2616_, 0, v_withWs_2609_);
lean_ctor_set(v___x_2616_, 1, v___x_2615_);
v___x_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2617_, 0, v___x_2616_);
return v___x_2617_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2___boxed(lean_object* v_inSubst_2621_, lean_object* v_snd_2622_, lean_object* v_fst_2623_, lean_object* v_____r_2624_, lean_object* v_withWs_2625_, lean_object* v_wssIdx_2626_){
_start:
{
uint8_t v_inSubst_boxed_2627_; lean_object* v_res_2628_; 
v_inSubst_boxed_2627_ = lean_unbox(v_inSubst_2621_);
v_res_2628_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_boxed_2627_, v_snd_2622_, v_fst_2623_, v_____r_2624_, v_withWs_2625_, v_wssIdx_2626_);
lean_dec(v_snd_2622_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(lean_object* v_upperBound_2629_, lean_object* v_diff_2630_, lean_object* v_snd_2631_, lean_object* v_snd_2632_, lean_object* v_a_2633_, lean_object* v_b_2634_){
_start:
{
lean_object* v_a_2636_; lean_object* v___y_2641_; uint8_t v___x_2644_; 
v___x_2644_ = lean_nat_dec_lt(v_a_2633_, v_upperBound_2629_);
if (v___x_2644_ == 0)
{
lean_dec(v_a_2633_);
return v_b_2634_;
}
else
{
lean_object* v___x_2645_; lean_object* v_snd_2646_; lean_object* v_snd_2647_; lean_object* v_fst_2648_; lean_object* v_fst_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2789_; 
v___x_2645_ = lean_array_fget_borrowed(v_diff_2630_, v_a_2633_);
v_snd_2646_ = lean_ctor_get(v_b_2634_, 1);
lean_inc(v_snd_2646_);
v_snd_2647_ = lean_ctor_get(v_snd_2646_, 1);
lean_inc(v_snd_2647_);
v_fst_2648_ = lean_ctor_get(v___x_2645_, 0);
v_fst_2649_ = lean_ctor_get(v_b_2634_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_b_2634_);
if (v_isSharedCheck_2789_ == 0)
{
lean_object* v_unused_2790_; 
v_unused_2790_ = lean_ctor_get(v_b_2634_, 1);
lean_dec(v_unused_2790_);
v___x_2651_ = v_b_2634_;
v_isShared_2652_ = v_isSharedCheck_2789_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_fst_2649_);
lean_dec(v_b_2634_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2789_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v_fst_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2787_; 
v_fst_2653_ = lean_ctor_get(v_snd_2646_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v_snd_2646_);
if (v_isSharedCheck_2787_ == 0)
{
lean_object* v_unused_2788_; 
v_unused_2788_ = lean_ctor_get(v_snd_2646_, 1);
lean_dec(v_unused_2788_);
v___x_2655_ = v_snd_2646_;
v_isShared_2656_ = v_isSharedCheck_2787_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_fst_2653_);
lean_dec(v_snd_2646_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2787_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v_fst_2657_; lean_object* v_snd_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2786_; 
v_fst_2657_ = lean_ctor_get(v_snd_2647_, 0);
v_snd_2658_ = lean_ctor_get(v_snd_2647_, 1);
v_isSharedCheck_2786_ = !lean_is_exclusive(v_snd_2647_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2660_ = v_snd_2647_;
v_isShared_2661_ = v_isSharedCheck_2786_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_snd_2658_);
lean_inc(v_fst_2657_);
lean_dec(v_snd_2647_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2786_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2662_; lean_object* v___y_2664_; lean_object* v___y_2679_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; uint8_t v___x_2690_; 
lean_inc(v___x_2645_);
v___x_2662_ = lean_array_push(v_fst_2649_, v___x_2645_);
v___x_2687_ = lean_unsigned_to_nat(1u);
v___x_2688_ = lean_nat_add(v_a_2633_, v___x_2687_);
v___x_2689_ = lean_array_get_size(v_diff_2630_);
v___x_2690_ = lean_nat_dec_lt(v___x_2688_, v___x_2689_);
if (v___x_2690_ == 0)
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
lean_dec(v___x_2688_);
lean_del_object(v___x_2660_);
lean_del_object(v___x_2655_);
lean_del_object(v___x_2651_);
v___x_2691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2691_, 0, v_fst_2657_);
lean_ctor_set(v___x_2691_, 1, v_snd_2658_);
v___x_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2692_, 0, v_fst_2653_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
v___x_2693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2662_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v_a_2636_ = v___x_2693_;
goto v___jp_2635_;
}
else
{
lean_object* v___x_2694_; lean_object* v_fst_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2784_; 
v___x_2694_ = lean_array_fget(v_diff_2630_, v___x_2688_);
lean_dec(v___x_2688_);
v_fst_2695_ = lean_ctor_get(v___x_2694_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2694_);
if (v_isSharedCheck_2784_ == 0)
{
lean_object* v_unused_2785_; 
v_unused_2785_ = lean_ctor_get(v___x_2694_, 1);
lean_dec(v_unused_2785_);
v___x_2697_ = v___x_2694_;
v_isShared_2698_ = v_isSharedCheck_2784_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_fst_2695_);
lean_dec(v___x_2694_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2784_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
uint8_t v_inSubst_2699_; lean_object* v___y_2701_; lean_object* v___x_2710_; uint8_t v___x_2711_; 
v_inSubst_2699_ = 0;
v___x_2710_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2711_ = lean_unbox(v_fst_2648_);
switch(v___x_2711_)
{
case 0:
{
uint8_t v___x_2712_; 
lean_del_object(v___x_2660_);
lean_del_object(v___x_2655_);
lean_del_object(v___x_2651_);
v___x_2712_ = lean_unbox(v_fst_2695_);
switch(v___x_2712_)
{
case 0:
{
lean_object* v___x_2713_; lean_object* v___x_2715_; 
v___x_2713_ = lean_array_get_borrowed(v___x_2710_, v_snd_2631_, v_fst_2657_);
lean_inc(v___x_2713_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 1, v___x_2713_);
v___x_2715_ = v___x_2697_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_fst_2695_);
lean_ctor_set(v_reuseFailAlloc_2721_, 1, v___x_2713_);
v___x_2715_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2716_ = lean_array_push(v___x_2662_, v___x_2715_);
v___x_2717_ = lean_nat_add(v_fst_2657_, v___x_2687_);
lean_dec(v_fst_2657_);
v___x_2718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2717_);
lean_ctor_set(v___x_2718_, 1, v_snd_2658_);
v___x_2719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2719_, 0, v_fst_2653_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
v___x_2720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2720_, 0, v___x_2716_);
lean_ctor_set(v___x_2720_, 1, v___x_2719_);
v_a_2636_ = v___x_2720_;
goto v___jp_2635_;
}
}
case 1:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
lean_del_object(v___x_2697_);
lean_dec(v_fst_2695_);
lean_dec(v_snd_2658_);
v___x_2722_ = lean_box(0);
v___x_2723_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2657_, v___x_2644_, v_fst_2653_, v___x_2662_, v___x_2722_);
v___y_2641_ = v___x_2723_;
goto v___jp_2640_;
}
default: 
{
lean_object* v___x_2724_; uint8_t v___x_2725_; 
lean_dec(v_fst_2695_);
v___x_2724_ = lean_array_get_borrowed(v___x_2710_, v_snd_2631_, v_fst_2657_);
v___x_2725_ = lean_unbox(v_snd_2658_);
if (v___x_2725_ == 0)
{
lean_object* v___x_2727_; 
lean_inc(v___x_2724_);
lean_inc(v_fst_2648_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 1, v___x_2724_);
lean_ctor_set(v___x_2697_, 0, v_fst_2648_);
v___x_2727_ = v___x_2697_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_fst_2648_);
lean_ctor_set(v_reuseFailAlloc_2730_, 1, v___x_2724_);
v___x_2727_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2728_ = lean_mk_empty_array_with_capacity(v___x_2687_);
v___x_2729_ = lean_array_push(v___x_2728_, v___x_2727_);
v___y_2701_ = v___x_2729_;
goto v___jp_2700_;
}
}
else
{
lean_object* v___x_2731_; lean_object* v___x_2732_; 
lean_del_object(v___x_2697_);
v___x_2731_ = lean_array_get_borrowed(v___x_2710_, v_snd_2632_, v_fst_2653_);
lean_inc(v___x_2724_);
lean_inc(v___x_2731_);
v___x_2732_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2731_, v___x_2724_);
v___y_2701_ = v___x_2732_;
goto v___jp_2700_;
}
}
}
}
case 1:
{
uint8_t v___x_2733_; 
lean_del_object(v___x_2660_);
lean_del_object(v___x_2655_);
lean_del_object(v___x_2651_);
v___x_2733_ = lean_unbox(v_fst_2695_);
switch(v___x_2733_)
{
case 0:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; 
lean_del_object(v___x_2697_);
lean_dec(v_fst_2695_);
lean_dec(v_snd_2658_);
v___x_2734_ = lean_box(0);
v___x_2735_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2657_, v___x_2644_, v_fst_2653_, v___x_2662_, v___x_2734_);
v___y_2641_ = v___x_2735_;
goto v___jp_2640_;
}
case 1:
{
lean_object* v___x_2736_; lean_object* v___x_2738_; 
v___x_2736_ = lean_array_get_borrowed(v___x_2710_, v_snd_2632_, v_fst_2653_);
lean_inc(v___x_2736_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 1, v___x_2736_);
v___x_2738_ = v___x_2697_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_fst_2695_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v___x_2736_);
v___x_2738_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2739_ = lean_array_push(v___x_2662_, v___x_2738_);
v___x_2740_ = lean_nat_add(v_fst_2653_, v___x_2687_);
lean_dec(v_fst_2653_);
v___x_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2741_, 0, v_fst_2657_);
lean_ctor_set(v___x_2741_, 1, v_snd_2658_);
v___x_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2740_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v___x_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2743_, 0, v___x_2739_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
v_a_2636_ = v___x_2743_;
goto v___jp_2635_;
}
}
default: 
{
uint8_t v___x_2748_; 
lean_dec(v_fst_2695_);
v___x_2748_ = lean_unbox(v_snd_2658_);
if (v___x_2748_ == 0)
{
lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; uint8_t v___x_2753_; 
v___x_2749_ = lean_array_get_borrowed(v___x_2710_, v_snd_2632_, v_fst_2653_);
v___x_2750_ = lean_unsigned_to_nat(0u);
v___x_2751_ = lean_string_utf8_byte_size(v___x_2749_);
lean_inc(v___x_2749_);
v___x_2752_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2749_);
lean_ctor_set(v___x_2752_, 1, v___x_2750_);
lean_ctor_set(v___x_2752_, 2, v___x_2751_);
v___x_2753_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_2752_);
lean_dec_ref_known(v___x_2752_, 3);
if (v___x_2753_ == 0)
{
lean_object* v___x_2755_; 
lean_inc(v___x_2749_);
lean_inc(v_fst_2648_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 1, v___x_2749_);
lean_ctor_set(v___x_2697_, 0, v_fst_2648_);
v___x_2755_ = v___x_2697_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_fst_2648_);
lean_ctor_set(v_reuseFailAlloc_2760_, 1, v___x_2749_);
v___x_2755_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2756_ = lean_array_push(v___x_2662_, v___x_2755_);
v___x_2757_ = lean_nat_add(v_fst_2653_, v___x_2687_);
lean_dec(v_fst_2653_);
v___x_2758_ = lean_box(0);
v___x_2759_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2699_, v_snd_2658_, v_fst_2657_, v___x_2758_, v___x_2756_, v___x_2757_);
lean_dec(v_snd_2658_);
v___y_2641_ = v___x_2759_;
goto v___jp_2640_;
}
}
else
{
lean_del_object(v___x_2697_);
goto v___jp_2745_;
}
}
else
{
lean_del_object(v___x_2697_);
goto v___jp_2745_;
}
v___jp_2745_:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2746_ = lean_box(0);
v___x_2747_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2699_, v_snd_2658_, v_fst_2657_, v___x_2746_, v___x_2662_, v_fst_2653_);
lean_dec(v_snd_2658_);
v___y_2641_ = v___x_2747_;
goto v___jp_2640_;
}
}
}
}
default: 
{
uint8_t v___x_2761_; 
v___x_2761_ = lean_unbox(v_fst_2695_);
if (v___x_2761_ == 1)
{
lean_object* v___x_2762_; lean_object* v___x_2763_; uint8_t v___x_2764_; 
v___x_2762_ = lean_array_get_borrowed(v___x_2710_, v_snd_2632_, v_fst_2653_);
v___x_2763_ = lean_array_get_size(v_snd_2631_);
v___x_2764_ = lean_nat_dec_lt(v_fst_2657_, v___x_2763_);
if (v___x_2764_ == 0)
{
lean_object* v___x_2766_; 
lean_inc(v___x_2762_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 1, v___x_2762_);
v___x_2766_ = v___x_2697_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_fst_2695_);
lean_ctor_set(v_reuseFailAlloc_2769_, 1, v___x_2762_);
v___x_2766_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = lean_mk_empty_array_with_capacity(v___x_2687_);
v___x_2768_ = lean_array_push(v___x_2767_, v___x_2766_);
v___y_2664_ = v___x_2768_;
goto v___jp_2663_;
}
}
else
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
lean_del_object(v___x_2697_);
lean_dec(v_fst_2695_);
v___x_2770_ = lean_array_fget_borrowed(v_snd_2631_, v_fst_2657_);
lean_inc(v___x_2770_);
lean_inc(v___x_2762_);
v___x_2771_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2762_, v___x_2770_);
v___y_2664_ = v___x_2771_;
goto v___jp_2663_;
}
}
else
{
lean_object* v___x_2772_; lean_object* v___x_2773_; uint8_t v___x_2774_; 
lean_dec(v_fst_2695_);
lean_del_object(v___x_2660_);
lean_del_object(v___x_2655_);
lean_del_object(v___x_2651_);
v___x_2772_ = lean_array_get_borrowed(v___x_2710_, v_snd_2631_, v_fst_2657_);
v___x_2773_ = lean_array_get_size(v_snd_2632_);
v___x_2774_ = lean_nat_dec_lt(v_fst_2653_, v___x_2773_);
if (v___x_2774_ == 0)
{
uint8_t v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2778_; 
v___x_2775_ = 0;
v___x_2776_ = lean_box(v___x_2775_);
lean_inc(v___x_2772_);
if (v_isShared_2698_ == 0)
{
lean_ctor_set(v___x_2697_, 1, v___x_2772_);
lean_ctor_set(v___x_2697_, 0, v___x_2776_);
v___x_2778_ = v___x_2697_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v___x_2776_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v___x_2772_);
v___x_2778_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = lean_mk_empty_array_with_capacity(v___x_2687_);
v___x_2780_ = lean_array_push(v___x_2779_, v___x_2778_);
v___y_2679_ = v___x_2780_;
goto v___jp_2678_;
}
}
else
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
lean_del_object(v___x_2697_);
v___x_2782_ = lean_array_fget_borrowed(v_snd_2632_, v_fst_2653_);
lean_inc(v___x_2772_);
lean_inc(v___x_2782_);
v___x_2783_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2782_, v___x_2772_);
v___y_2679_ = v___x_2783_;
goto v___jp_2678_;
}
}
}
}
v___jp_2700_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; uint8_t v___x_2704_; 
v___x_2702_ = l_Array_append___redArg(v___x_2662_, v___y_2701_);
lean_dec_ref(v___y_2701_);
v___x_2703_ = lean_nat_add(v_fst_2657_, v___x_2687_);
lean_dec(v_fst_2657_);
v___x_2704_ = lean_unbox(v_snd_2658_);
lean_dec(v_snd_2658_);
if (v___x_2704_ == 0)
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2705_ = lean_box(0);
v___x_2706_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2703_, v_inSubst_2699_, v___x_2702_, v___x_2705_, v_fst_2653_);
v___y_2641_ = v___x_2706_;
goto v___jp_2640_;
}
else
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2707_ = lean_nat_add(v_fst_2653_, v___x_2687_);
lean_dec(v_fst_2653_);
v___x_2708_ = lean_box(0);
v___x_2709_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2703_, v_inSubst_2699_, v___x_2702_, v___x_2708_, v___x_2707_);
v___y_2641_ = v___x_2709_;
goto v___jp_2640_;
}
}
}
}
v___jp_2663_:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2670_; 
v___x_2665_ = l_Array_append___redArg(v___x_2662_, v___y_2664_);
lean_dec_ref(v___y_2664_);
v___x_2666_ = lean_unsigned_to_nat(1u);
v___x_2667_ = lean_nat_add(v_fst_2653_, v___x_2666_);
lean_dec(v_fst_2653_);
v___x_2668_ = lean_nat_add(v_fst_2657_, v___x_2666_);
lean_dec(v_fst_2657_);
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v___x_2668_);
v___x_2670_ = v___x_2660_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2677_, 1, v_snd_2658_);
v___x_2670_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
lean_object* v___x_2672_; 
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 1, v___x_2670_);
lean_ctor_set(v___x_2655_, 0, v___x_2667_);
v___x_2672_ = v___x_2655_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2667_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
lean_object* v___x_2674_; 
if (v_isShared_2652_ == 0)
{
lean_ctor_set(v___x_2651_, 1, v___x_2672_);
lean_ctor_set(v___x_2651_, 0, v___x_2665_);
v___x_2674_ = v___x_2651_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2665_);
lean_ctor_set(v_reuseFailAlloc_2675_, 1, v___x_2672_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
v_a_2636_ = v___x_2674_;
goto v___jp_2635_;
}
}
}
}
v___jp_2678_:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2680_ = l_Array_append___redArg(v___x_2662_, v___y_2679_);
lean_dec_ref(v___y_2679_);
v___x_2681_ = lean_unsigned_to_nat(1u);
v___x_2682_ = lean_nat_add(v_fst_2653_, v___x_2681_);
lean_dec(v_fst_2653_);
v___x_2683_ = lean_nat_add(v_fst_2657_, v___x_2681_);
lean_dec(v_fst_2657_);
v___x_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
lean_ctor_set(v___x_2684_, 1, v_snd_2658_);
v___x_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2682_);
lean_ctor_set(v___x_2685_, 1, v___x_2684_);
v___x_2686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2686_, 0, v___x_2680_);
lean_ctor_set(v___x_2686_, 1, v___x_2685_);
v_a_2636_ = v___x_2686_;
goto v___jp_2635_;
}
}
}
}
}
v___jp_2635_:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2637_ = lean_unsigned_to_nat(1u);
v___x_2638_ = lean_nat_add(v_a_2633_, v___x_2637_);
lean_dec(v_a_2633_);
v_a_2633_ = v___x_2638_;
v_b_2634_ = v_a_2636_;
goto _start;
}
v___jp_2640_:
{
if (lean_obj_tag(v___y_2641_) == 0)
{
lean_object* v_a_2642_; 
lean_dec(v_a_2633_);
v_a_2642_ = lean_ctor_get(v___y_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___y_2641_, 1);
return v_a_2642_;
}
else
{
lean_object* v_a_2643_; 
v_a_2643_ = lean_ctor_get(v___y_2641_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___y_2641_, 1);
v_a_2636_ = v_a_2643_;
goto v___jp_2635_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___boxed(lean_object* v_upperBound_2791_, lean_object* v_diff_2792_, lean_object* v_snd_2793_, lean_object* v_snd_2794_, lean_object* v_a_2795_, lean_object* v_b_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2791_, v_diff_2792_, v_snd_2793_, v_snd_2794_, v_a_2795_, v_b_2796_);
lean_dec_ref(v_snd_2794_);
lean_dec_ref(v_snd_2793_);
lean_dec_ref(v_diff_2792_);
lean_dec(v_upperBound_2791_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(lean_object* v_s_2808_, lean_object* v_s_x27_2809_){
_start:
{
lean_object* v___x_2810_; lean_object* v_fst_2811_; lean_object* v_snd_2812_; lean_object* v___x_2813_; lean_object* v_fst_2814_; lean_object* v_snd_2815_; lean_object* v_diff_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v_fst_2821_; lean_object* v___x_2822_; size_t v_sz_2823_; size_t v___x_2824_; lean_object* v___x_2825_; 
v___x_2810_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_2808_);
v_fst_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_fst_2811_);
v_snd_2812_ = lean_ctor_get(v___x_2810_, 1);
lean_inc(v_snd_2812_);
lean_dec_ref(v___x_2810_);
v___x_2813_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_x27_2809_);
v_fst_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_fst_2814_);
v_snd_2815_ = lean_ctor_get(v___x_2813_, 1);
lean_inc(v_snd_2815_);
lean_dec_ref(v___x_2813_);
v_diff_2816_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(v_fst_2811_, v_fst_2814_);
v___x_2817_ = lean_unsigned_to_nat(0u);
v___x_2818_ = lean_array_get_size(v_diff_2816_);
v___x_2819_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__2));
v___x_2820_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v___x_2818_, v_diff_2816_, v_snd_2815_, v_snd_2812_, v___x_2817_, v___x_2819_);
lean_dec(v_snd_2812_);
lean_dec(v_snd_2815_);
lean_dec_ref(v_diff_2816_);
v_fst_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_fst_2821_);
lean_dec_ref(v___x_2820_);
v___x_2822_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_fst_2821_);
lean_dec(v_fst_2821_);
v_sz_2823_ = lean_array_size(v___x_2822_);
v___x_2824_ = ((size_t)0ULL);
v___x_2825_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_2823_, v___x_2824_, v___x_2822_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___boxed(lean_object* v_s_2826_, lean_object* v_s_x27_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_2826_, v_s_x27_2827_);
lean_dec_ref(v_s_x27_2827_);
lean_dec_ref(v_s_2826_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(lean_object* v_upperBound_2829_, lean_object* v_diff_2830_, lean_object* v_snd_2831_, lean_object* v_snd_2832_, lean_object* v_inst_2833_, lean_object* v_R_2834_, lean_object* v_a_2835_, lean_object* v_b_2836_, lean_object* v_c_2837_){
_start:
{
lean_object* v___x_2838_; 
v___x_2838_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2829_, v_diff_2830_, v_snd_2831_, v_snd_2832_, v_a_2835_, v_b_2836_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___boxed(lean_object* v_upperBound_2839_, lean_object* v_diff_2840_, lean_object* v_snd_2841_, lean_object* v_snd_2842_, lean_object* v_inst_2843_, lean_object* v_R_2844_, lean_object* v_a_2845_, lean_object* v_b_2846_, lean_object* v_c_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(v_upperBound_2839_, v_diff_2840_, v_snd_2841_, v_snd_2842_, v_inst_2843_, v_R_2844_, v_a_2845_, v_b_2846_, v_c_2847_);
lean_dec_ref(v_snd_2842_);
lean_dec_ref(v_snd_2841_);
lean_dec_ref(v_diff_2840_);
lean_dec(v_upperBound_2839_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(lean_object* v___x_2849_, lean_object* v_original_2850_, lean_object* v_a_2851_, lean_object* v_inst_2852_, lean_object* v_a_2853_){
_start:
{
lean_object* v___x_2854_; 
v___x_2854_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2849_, v_original_2850_, v_a_2851_, v_a_2853_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___boxed(lean_object* v___x_2855_, lean_object* v_original_2856_, lean_object* v_a_2857_, lean_object* v_inst_2858_, lean_object* v_a_2859_){
_start:
{
lean_object* v_res_2860_; 
v_res_2860_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v___x_2855_, v_original_2856_, v_a_2857_, v_inst_2858_, v_a_2859_);
lean_dec_ref(v_a_2857_);
lean_dec_ref(v_original_2856_);
lean_dec(v___x_2855_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(lean_object* v___x_2861_, lean_object* v_edited_2862_, lean_object* v_a_2863_, lean_object* v_inst_2864_, lean_object* v_a_2865_){
_start:
{
lean_object* v___x_2866_; 
v___x_2866_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2861_, v_edited_2862_, v_a_2863_, v_a_2865_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___boxed(lean_object* v___x_2867_, lean_object* v_edited_2868_, lean_object* v_a_2869_, lean_object* v_inst_2870_, lean_object* v_a_2871_){
_start:
{
lean_object* v_res_2872_; 
v_res_2872_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(v___x_2867_, v_edited_2868_, v_a_2869_, v_inst_2870_, v_a_2871_);
lean_dec_ref(v_a_2869_);
lean_dec_ref(v_edited_2868_);
lean_dec(v___x_2867_);
return v_res_2872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(lean_object* v___x_2873_, lean_object* v_original_2874_, lean_object* v_inst_2875_, lean_object* v_a_2876_){
_start:
{
lean_object* v___x_2877_; 
v___x_2877_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2873_, v_original_2874_, v_a_2876_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___boxed(lean_object* v___x_2878_, lean_object* v_original_2879_, lean_object* v_inst_2880_, lean_object* v_a_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(v___x_2878_, v_original_2879_, v_inst_2880_, v_a_2881_);
lean_dec_ref(v_original_2879_);
lean_dec(v___x_2878_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(lean_object* v___x_2883_, lean_object* v_edited_2884_, lean_object* v_inst_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2883_, v_edited_2884_, v_a_2886_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___boxed(lean_object* v___x_2888_, lean_object* v_edited_2889_, lean_object* v_inst_2890_, lean_object* v_a_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(v___x_2888_, v_edited_2889_, v_inst_2890_, v_a_2891_);
lean_dec_ref(v_edited_2889_);
lean_dec(v___x_2888_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6(lean_object* v_as_2893_, lean_object* v_as_x27_2894_, lean_object* v_b_2895_, lean_object* v_a_2896_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(v_as_x27_2894_, v_b_2895_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___boxed(lean_object* v_as_2898_, lean_object* v_as_x27_2899_, lean_object* v_b_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6(v_as_2898_, v_as_x27_2899_, v_b_2900_, v_a_2901_);
lean_dec(v_as_x27_2899_);
lean_dec(v_as_2898_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9(lean_object* v_lsize_2903_, lean_object* v_rsize_2904_, lean_object* v_histogram_2905_, lean_object* v_index_2906_, lean_object* v_val_2907_){
_start:
{
lean_object* v___x_2908_; 
v___x_2908_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___redArg(v_histogram_2905_, v_index_2906_, v_val_2907_);
return v___x_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___boxed(lean_object* v_lsize_2909_, lean_object* v_rsize_2910_, lean_object* v_histogram_2911_, lean_object* v_index_2912_, lean_object* v_val_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9(v_lsize_2909_, v_rsize_2910_, v_histogram_2911_, v_index_2912_, v_val_2913_);
lean_dec(v_rsize_2910_);
lean_dec(v_lsize_2909_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10(lean_object* v_upperBound_2915_, lean_object* v___x_2916_, lean_object* v_fst_2917_, lean_object* v___x_2918_, lean_object* v_inst_2919_, lean_object* v_R_2920_, lean_object* v_a_2921_, lean_object* v_b_2922_, lean_object* v_c_2923_){
_start:
{
lean_object* v___x_2924_; 
v___x_2924_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(v_upperBound_2915_, v___x_2916_, v_fst_2917_, v___x_2918_, v_a_2921_, v_b_2922_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___boxed(lean_object* v_upperBound_2925_, lean_object* v___x_2926_, lean_object* v_fst_2927_, lean_object* v___x_2928_, lean_object* v_inst_2929_, lean_object* v_R_2930_, lean_object* v_a_2931_, lean_object* v_b_2932_, lean_object* v_c_2933_){
_start:
{
lean_object* v_res_2934_; 
v_res_2934_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10(v_upperBound_2925_, v___x_2926_, v_fst_2927_, v___x_2928_, v_inst_2929_, v_R_2930_, v_a_2931_, v_b_2932_, v_c_2933_);
lean_dec(v___x_2928_);
lean_dec_ref(v_fst_2927_);
lean_dec(v___x_2926_);
lean_dec(v_upperBound_2925_);
return v_res_2934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11(lean_object* v_lsize_2935_, lean_object* v_rsize_2936_, lean_object* v_histogram_2937_, lean_object* v_index_2938_, lean_object* v_val_2939_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___redArg(v_histogram_2937_, v_index_2938_, v_val_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___boxed(lean_object* v_lsize_2941_, lean_object* v_rsize_2942_, lean_object* v_histogram_2943_, lean_object* v_index_2944_, lean_object* v_val_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11(v_lsize_2941_, v_rsize_2942_, v_histogram_2943_, v_index_2944_, v_val_2945_);
lean_dec(v_rsize_2942_);
lean_dec(v_lsize_2941_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12(lean_object* v_upperBound_2947_, lean_object* v_fst_2948_, lean_object* v___x_2949_, lean_object* v_fst_2950_, lean_object* v_inst_2951_, lean_object* v_R_2952_, lean_object* v_a_2953_, lean_object* v_b_2954_, lean_object* v_c_2955_){
_start:
{
lean_object* v___x_2956_; 
v___x_2956_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(v_upperBound_2947_, v_fst_2948_, v___x_2949_, v_fst_2950_, v_a_2953_, v_b_2954_);
return v___x_2956_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___boxed(lean_object* v_upperBound_2957_, lean_object* v_fst_2958_, lean_object* v___x_2959_, lean_object* v_fst_2960_, lean_object* v_inst_2961_, lean_object* v_R_2962_, lean_object* v_a_2963_, lean_object* v_b_2964_, lean_object* v_c_2965_){
_start:
{
lean_object* v_res_2966_; 
v_res_2966_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12(v_upperBound_2957_, v_fst_2958_, v___x_2959_, v_fst_2960_, v_inst_2961_, v_R_2962_, v_a_2963_, v_b_2964_, v_c_2965_);
lean_dec_ref(v_fst_2960_);
lean_dec(v___x_2959_);
lean_dec_ref(v_fst_2958_);
lean_dec(v_upperBound_2957_);
return v_res_2966_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13(lean_object* v_00_u03b2_2967_, lean_object* v_m_2968_, lean_object* v_a_2969_){
_start:
{
lean_object* v___x_2970_; 
v___x_2970_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_m_2968_, v_a_2969_);
return v___x_2970_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___boxed(lean_object* v_00_u03b2_2971_, lean_object* v_m_2972_, lean_object* v_a_2973_){
_start:
{
lean_object* v_res_2974_; 
v_res_2974_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13(v_00_u03b2_2971_, v_m_2972_, v_a_2973_);
lean_dec_ref(v_a_2973_);
lean_dec_ref(v_m_2972_);
return v_res_2974_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_2975_, lean_object* v_m_2976_, lean_object* v_a_2977_, lean_object* v_b_2978_){
_start:
{
lean_object* v___x_2979_; 
v___x_2979_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_m_2976_, v_a_2977_, v_b_2978_);
return v___x_2979_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14(lean_object* v_inst_2980_, lean_object* v_R_2981_, lean_object* v_a_2982_, lean_object* v_b_2983_){
_start:
{
lean_object* v___x_2984_; 
v___x_2984_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(v_a_2982_, v_b_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20(lean_object* v_00_u03b2_2985_, lean_object* v_a_2986_, lean_object* v_x_2987_){
_start:
{
lean_object* v___x_2988_; 
v___x_2988_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(v_a_2986_, v_x_2987_);
return v___x_2988_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___boxed(lean_object* v_00_u03b2_2989_, lean_object* v_a_2990_, lean_object* v_x_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20(v_00_u03b2_2989_, v_a_2990_, v_x_2991_);
lean_dec(v_x_2991_);
lean_dec_ref(v_a_2990_);
return v_res_2992_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22(lean_object* v_00_u03b2_2993_, lean_object* v_a_2994_, lean_object* v_x_2995_){
_start:
{
uint8_t v___x_2996_; 
v___x_2996_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(v_a_2994_, v_x_2995_);
return v___x_2996_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___boxed(lean_object* v_00_u03b2_2997_, lean_object* v_a_2998_, lean_object* v_x_2999_){
_start:
{
uint8_t v_res_3000_; lean_object* v_r_3001_; 
v_res_3000_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22(v_00_u03b2_2997_, v_a_2998_, v_x_2999_);
lean_dec(v_x_2999_);
lean_dec_ref(v_a_2998_);
v_r_3001_ = lean_box(v_res_3000_);
return v_r_3001_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23(lean_object* v_00_u03b2_3002_, lean_object* v_data_3003_){
_start:
{
lean_object* v___x_3004_; 
v___x_3004_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23___redArg(v_data_3003_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24(lean_object* v_00_u03b2_3005_, lean_object* v_a_3006_, lean_object* v_b_3007_, lean_object* v_x_3008_){
_start:
{
lean_object* v___x_3009_; 
v___x_3009_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(v_a_3006_, v_b_3007_, v_x_3008_);
return v___x_3009_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28(lean_object* v_00_u03b2_3010_, lean_object* v_i_3011_, lean_object* v_source_3012_, lean_object* v_target_3013_){
_start:
{
lean_object* v___x_3014_; 
v___x_3014_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28___redArg(v_i_3011_, v_source_3012_, v_target_3013_);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_3015_, lean_object* v_x_3016_, lean_object* v_x_3017_){
_start:
{
lean_object* v___x_3018_; 
v___x_3018_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29___redArg(v_x_3016_, v_x_3017_);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(lean_object* v_s_3019_){
_start:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3020_ = lean_string_data(v_s_3019_);
v___x_3021_ = lean_array_mk(v___x_3020_);
return v___x_3021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(lean_object* v_s_3022_, lean_object* v_s_x27_3023_){
_start:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3024_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3022_);
v___x_3025_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3023_);
v___x_3026_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3024_, v___x_3025_);
v___x_3027_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_3026_);
lean_dec_ref(v___x_3026_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(lean_object* v_s_3028_, lean_object* v_s_x27_3029_){
_start:
{
uint8_t v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; uint8_t v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3030_ = 1;
v___x_3031_ = lean_box(v___x_3030_);
v___x_3032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3032_, 0, v___x_3031_);
lean_ctor_set(v___x_3032_, 1, v_s_3028_);
v___x_3033_ = 0;
v___x_3034_ = lean_box(v___x_3033_);
v___x_3035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
lean_ctor_set(v___x_3035_, 1, v_s_x27_3029_);
v___x_3036_ = lean_unsigned_to_nat(2u);
v___x_3037_ = lean_mk_empty_array_with_capacity(v___x_3036_);
v___x_3038_ = lean_array_push(v___x_3037_, v___x_3032_);
v___x_3039_ = lean_array_push(v___x_3038_, v___x_3035_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(lean_object* v_as_3040_, size_t v_i_3041_, size_t v_stop_3042_, lean_object* v_b_3043_){
_start:
{
lean_object* v___y_3045_; uint8_t v___x_3049_; 
v___x_3049_ = lean_usize_dec_eq(v_i_3041_, v_stop_3042_);
if (v___x_3049_ == 0)
{
lean_object* v___x_3050_; lean_object* v_fst_3051_; uint8_t v___x_3052_; uint8_t v___x_3053_; uint8_t v___x_3054_; 
v___x_3050_ = lean_array_uget_borrowed(v_as_3040_, v_i_3041_);
v_fst_3051_ = lean_ctor_get(v___x_3050_, 0);
v___x_3052_ = 2;
v___x_3053_ = lean_unbox(v_fst_3051_);
v___x_3054_ = l_Lean_Diff_instBEqAction_beq(v___x_3053_, v___x_3052_);
if (v___x_3054_ == 0)
{
lean_object* v___x_3055_; 
lean_inc(v___x_3050_);
v___x_3055_ = lean_array_push(v_b_3043_, v___x_3050_);
v___y_3045_ = v___x_3055_;
goto v___jp_3044_;
}
else
{
v___y_3045_ = v_b_3043_;
goto v___jp_3044_;
}
}
else
{
return v_b_3043_;
}
v___jp_3044_:
{
size_t v___x_3046_; size_t v___x_3047_; 
v___x_3046_ = ((size_t)1ULL);
v___x_3047_ = lean_usize_add(v_i_3041_, v___x_3046_);
v_i_3041_ = v___x_3047_;
v_b_3043_ = v___y_3045_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0___boxed(lean_object* v_as_3056_, lean_object* v_i_3057_, lean_object* v_stop_3058_, lean_object* v_b_3059_){
_start:
{
size_t v_i_boxed_3060_; size_t v_stop_boxed_3061_; lean_object* v_res_3062_; 
v_i_boxed_3060_ = lean_unbox_usize(v_i_3057_);
lean_dec(v_i_3057_);
v_stop_boxed_3061_ = lean_unbox_usize(v_stop_3058_);
lean_dec(v_stop_3058_);
v_res_3062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_as_3056_, v_i_boxed_3060_, v_stop_boxed_3061_, v_b_3059_);
lean_dec_ref(v_as_3056_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff(lean_object* v_s_3063_, lean_object* v_s_x27_3064_, uint8_t v_granularity_3065_){
_start:
{
lean_object* v___y_3067_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3088_; lean_object* v___y_3089_; 
switch(v_granularity_3065_)
{
case 0:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___y_3109_; uint8_t v___x_3115_; 
v___x_3106_ = lean_string_length(v_s_3063_);
v___x_3107_ = lean_string_length(v_s_x27_3064_);
v___x_3115_ = lean_nat_dec_le(v___x_3106_, v___x_3107_);
if (v___x_3115_ == 0)
{
v___y_3109_ = v___x_3107_;
goto v___jp_3108_;
}
else
{
v___y_3109_ = v___x_3106_;
goto v___jp_3108_;
}
v___jp_3108_:
{
lean_object* v___x_3110_; lean_object* v_maxCharDiffDistance_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; uint8_t v___x_3114_; 
v___x_3110_ = lean_unsigned_to_nat(5u);
v_maxCharDiffDistance_3111_ = lean_nat_div(v___y_3109_, v___x_3110_);
v___x_3112_ = lean_unsigned_to_nat(1u);
v___x_3113_ = lean_nat_shiftr(v___y_3109_, v___x_3112_);
lean_dec(v___y_3109_);
v___x_3114_ = lean_nat_dec_le(v___x_3106_, v___x_3107_);
if (v___x_3114_ == 0)
{
v___y_3086_ = v___x_3112_;
v___y_3087_ = v___x_3113_;
v___y_3088_ = v_maxCharDiffDistance_3111_;
v___y_3089_ = v___x_3106_;
goto v___jp_3085_;
}
else
{
v___y_3086_ = v___x_3112_;
v___y_3087_ = v___x_3113_;
v___y_3088_ = v_maxCharDiffDistance_3111_;
v___y_3089_ = v___x_3107_;
goto v___jp_3085_;
}
}
}
case 1:
{
lean_object* v___x_3116_; 
v___x_3116_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(v_s_3063_, v_s_x27_3064_);
return v___x_3116_;
}
case 2:
{
lean_object* v___x_3117_; 
v___x_3117_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3063_, v_s_x27_3064_);
lean_dec_ref(v_s_x27_3064_);
lean_dec_ref(v_s_3063_);
return v___x_3117_;
}
case 3:
{
lean_object* v___x_3118_; 
v___x_3118_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3063_, v_s_x27_3064_);
return v___x_3118_;
}
default: 
{
uint8_t v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; 
lean_dec_ref(v_s_3063_);
v___x_3119_ = 0;
v___x_3120_ = lean_box(v___x_3119_);
v___x_3121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3121_, 0, v___x_3120_);
lean_ctor_set(v___x_3121_, 1, v_s_x27_3064_);
v___x_3122_ = lean_unsigned_to_nat(1u);
v___x_3123_ = lean_mk_empty_array_with_capacity(v___x_3122_);
v___x_3124_ = lean_array_push(v___x_3123_, v___x_3121_);
return v___x_3124_;
}
}
v___jp_3066_:
{
size_t v_sz_3068_; size_t v___x_3069_; lean_object* v___x_3070_; 
v_sz_3068_ = lean_array_size(v___y_3067_);
v___x_3069_ = ((size_t)0ULL);
v___x_3070_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_3068_, v___x_3069_, v___y_3067_);
return v___x_3070_;
}
v___jp_3071_:
{
lean_object* v_charArrDiff_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; uint8_t v___x_3079_; 
v_charArrDiff_3076_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v___y_3073_);
lean_dec_ref(v___y_3073_);
v___x_3077_ = lean_array_get_size(v_charArrDiff_3076_);
v___x_3078_ = lean_unsigned_to_nat(3u);
v___x_3079_ = lean_nat_dec_le(v___x_3077_, v___x_3078_);
if (v___x_3079_ == 0)
{
lean_object* v_approxEditDistance_3080_; uint8_t v___x_3081_; 
v_approxEditDistance_3080_ = lean_array_get_size(v___y_3075_);
lean_dec_ref(v___y_3075_);
v___x_3081_ = lean_nat_dec_le(v_approxEditDistance_3080_, v___y_3074_);
lean_dec(v___y_3074_);
if (v___x_3081_ == 0)
{
uint8_t v___x_3082_; 
lean_dec_ref(v_charArrDiff_3076_);
v___x_3082_ = lean_nat_dec_le(v_approxEditDistance_3080_, v___y_3072_);
lean_dec(v___y_3072_);
if (v___x_3082_ == 0)
{
lean_object* v___x_3083_; 
v___x_3083_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3063_, v_s_x27_3064_);
return v___x_3083_;
}
else
{
lean_object* v___x_3084_; 
v___x_3084_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3063_, v_s_x27_3064_);
lean_dec_ref(v_s_x27_3064_);
lean_dec_ref(v_s_3063_);
return v___x_3084_;
}
}
else
{
lean_dec(v___y_3072_);
lean_dec_ref(v_s_x27_3064_);
lean_dec_ref(v_s_3063_);
v___y_3067_ = v_charArrDiff_3076_;
goto v___jp_3066_;
}
}
else
{
lean_dec_ref(v___y_3075_);
lean_dec(v___y_3074_);
lean_dec(v___y_3072_);
lean_dec_ref(v_s_x27_3064_);
lean_dec_ref(v_s_3063_);
v___y_3067_ = v_charArrDiff_3076_;
goto v___jp_3066_;
}
}
v___jp_3085_:
{
lean_object* v___x_3090_; lean_object* v_maxWordDiffDistance_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v_charDiffRaw_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; uint8_t v___x_3098_; 
v___x_3090_ = lean_nat_shiftr(v___y_3089_, v___y_3086_);
lean_dec(v___y_3089_);
v_maxWordDiffDistance_3091_ = lean_nat_add(v___y_3087_, v___x_3090_);
lean_dec(v___x_3090_);
lean_dec(v___y_3087_);
lean_inc_ref(v_s_3063_);
v___x_3092_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3063_);
lean_inc_ref(v_s_x27_3064_);
v___x_3093_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3064_);
v_charDiffRaw_3094_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3092_, v___x_3093_);
v___x_3095_ = lean_unsigned_to_nat(0u);
v___x_3096_ = lean_array_get_size(v_charDiffRaw_3094_);
v___x_3097_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0));
v___x_3098_ = lean_nat_dec_lt(v___x_3095_, v___x_3096_);
if (v___x_3098_ == 0)
{
v___y_3072_ = v_maxWordDiffDistance_3091_;
v___y_3073_ = v_charDiffRaw_3094_;
v___y_3074_ = v___y_3088_;
v___y_3075_ = v___x_3097_;
goto v___jp_3071_;
}
else
{
uint8_t v___x_3099_; 
v___x_3099_ = lean_nat_dec_le(v___x_3096_, v___x_3096_);
if (v___x_3099_ == 0)
{
if (v___x_3098_ == 0)
{
v___y_3072_ = v_maxWordDiffDistance_3091_;
v___y_3073_ = v_charDiffRaw_3094_;
v___y_3074_ = v___y_3088_;
v___y_3075_ = v___x_3097_;
goto v___jp_3071_;
}
else
{
size_t v___x_3100_; size_t v___x_3101_; lean_object* v___x_3102_; 
v___x_3100_ = ((size_t)0ULL);
v___x_3101_ = lean_usize_of_nat(v___x_3096_);
v___x_3102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3094_, v___x_3100_, v___x_3101_, v___x_3097_);
v___y_3072_ = v_maxWordDiffDistance_3091_;
v___y_3073_ = v_charDiffRaw_3094_;
v___y_3074_ = v___y_3088_;
v___y_3075_ = v___x_3102_;
goto v___jp_3071_;
}
}
else
{
size_t v___x_3103_; size_t v___x_3104_; lean_object* v___x_3105_; 
v___x_3103_ = ((size_t)0ULL);
v___x_3104_ = lean_usize_of_nat(v___x_3096_);
v___x_3105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3094_, v___x_3103_, v___x_3104_, v___x_3097_);
v___y_3072_ = v_maxWordDiffDistance_3091_;
v___y_3073_ = v_charDiffRaw_3094_;
v___y_3074_ = v___y_3088_;
v___y_3075_ = v___x_3105_;
goto v___jp_3071_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff___boxed(lean_object* v_s_3125_, lean_object* v_s_x27_3126_, lean_object* v_granularity_3127_){
_start:
{
uint8_t v_granularity_boxed_3128_; lean_object* v_res_3129_; 
v_granularity_boxed_3128_ = lean_unbox(v_granularity_3127_);
v_res_3129_ = l_Lean_Meta_Hint_readableDiff(v_s_3125_, v_s_x27_3126_, v_granularity_boxed_3128_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(lean_object* v_as_3130_, size_t v_i_3131_, size_t v_stop_3132_, lean_object* v_b_3133_){
_start:
{
uint8_t v___x_3134_; 
v___x_3134_ = lean_usize_dec_eq(v_i_3131_, v_stop_3132_);
if (v___x_3134_ == 0)
{
lean_object* v___x_3135_; lean_object* v_snd_3136_; lean_object* v___x_3137_; size_t v___x_3138_; size_t v___x_3139_; 
v___x_3135_ = lean_array_uget_borrowed(v_as_3130_, v_i_3131_);
v_snd_3136_ = lean_ctor_get(v___x_3135_, 1);
v___x_3137_ = lean_string_append(v_b_3133_, v_snd_3136_);
v___x_3138_ = ((size_t)1ULL);
v___x_3139_ = lean_usize_add(v_i_3131_, v___x_3138_);
v_i_3131_ = v___x_3139_;
v_b_3133_ = v___x_3137_;
goto _start;
}
else
{
return v_b_3133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0___boxed(lean_object* v_as_3141_, lean_object* v_i_3142_, lean_object* v_stop_3143_, lean_object* v_b_3144_){
_start:
{
size_t v_i_boxed_3145_; size_t v_stop_boxed_3146_; lean_object* v_res_3147_; 
v_i_boxed_3145_ = lean_unbox_usize(v_i_3142_);
lean_dec(v_i_3142_);
v_stop_boxed_3146_ = lean_unbox_usize(v_stop_3143_);
lean_dec(v_stop_3143_);
v_res_3147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v_as_3141_, v_i_boxed_3145_, v_stop_boxed_3146_, v_b_3144_);
lean_dec_ref(v_as_3141_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(lean_object* v_t_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v___x_3151_; lean_object* v_infoState_3152_; uint8_t v_enabled_3153_; 
v___x_3151_ = lean_st_ref_get(v___y_3149_);
v_infoState_3152_ = lean_ctor_get(v___x_3151_, 8);
lean_inc_ref(v_infoState_3152_);
lean_dec(v___x_3151_);
v_enabled_3153_ = lean_ctor_get_uint8(v_infoState_3152_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3152_);
if (v_enabled_3153_ == 0)
{
lean_object* v___x_3154_; lean_object* v___x_3155_; 
lean_dec_ref(v_t_3148_);
v___x_3154_ = lean_box(0);
v___x_3155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3155_, 0, v___x_3154_);
return v___x_3155_;
}
else
{
lean_object* v___x_3156_; lean_object* v_infoState_3157_; lean_object* v_env_3158_; lean_object* v_nextMacroScope_3159_; lean_object* v_ngen_3160_; lean_object* v_auxDeclNGen_3161_; lean_object* v_traceState_3162_; lean_object* v_cache_3163_; lean_object* v_recordedDeps_3164_; lean_object* v_messages_3165_; lean_object* v_snapshotTasks_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3188_; 
v___x_3156_ = lean_st_ref_take(v___y_3149_);
v_infoState_3157_ = lean_ctor_get(v___x_3156_, 8);
v_env_3158_ = lean_ctor_get(v___x_3156_, 0);
v_nextMacroScope_3159_ = lean_ctor_get(v___x_3156_, 1);
v_ngen_3160_ = lean_ctor_get(v___x_3156_, 2);
v_auxDeclNGen_3161_ = lean_ctor_get(v___x_3156_, 3);
v_traceState_3162_ = lean_ctor_get(v___x_3156_, 4);
v_cache_3163_ = lean_ctor_get(v___x_3156_, 5);
v_recordedDeps_3164_ = lean_ctor_get(v___x_3156_, 6);
v_messages_3165_ = lean_ctor_get(v___x_3156_, 7);
v_snapshotTasks_3166_ = lean_ctor_get(v___x_3156_, 9);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3168_ = v___x_3156_;
v_isShared_3169_ = v_isSharedCheck_3188_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_snapshotTasks_3166_);
lean_inc(v_infoState_3157_);
lean_inc(v_messages_3165_);
lean_inc(v_recordedDeps_3164_);
lean_inc(v_cache_3163_);
lean_inc(v_traceState_3162_);
lean_inc(v_auxDeclNGen_3161_);
lean_inc(v_ngen_3160_);
lean_inc(v_nextMacroScope_3159_);
lean_inc(v_env_3158_);
lean_dec(v___x_3156_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3188_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
uint8_t v_enabled_3170_; lean_object* v_assignment_3171_; lean_object* v_lazyAssignment_3172_; lean_object* v_trees_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3187_; 
v_enabled_3170_ = lean_ctor_get_uint8(v_infoState_3157_, sizeof(void*)*3);
v_assignment_3171_ = lean_ctor_get(v_infoState_3157_, 0);
v_lazyAssignment_3172_ = lean_ctor_get(v_infoState_3157_, 1);
v_trees_3173_ = lean_ctor_get(v_infoState_3157_, 2);
v_isSharedCheck_3187_ = !lean_is_exclusive(v_infoState_3157_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3175_ = v_infoState_3157_;
v_isShared_3176_ = v_isSharedCheck_3187_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_trees_3173_);
lean_inc(v_lazyAssignment_3172_);
lean_inc(v_assignment_3171_);
lean_dec(v_infoState_3157_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3187_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3180_; 
v___x_3177_ = lean_box(0);
v___x_3178_ = l_Lean_PersistentArray_push___redArg(v_trees_3173_, v_t_3148_);
if (v_isShared_3176_ == 0)
{
lean_ctor_set(v___x_3175_, 2, v___x_3178_);
v___x_3180_ = v___x_3175_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_assignment_3171_);
lean_ctor_set(v_reuseFailAlloc_3186_, 1, v_lazyAssignment_3172_);
lean_ctor_set(v_reuseFailAlloc_3186_, 2, v___x_3178_);
lean_ctor_set_uint8(v_reuseFailAlloc_3186_, sizeof(void*)*3, v_enabled_3170_);
v___x_3180_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
lean_object* v___x_3182_; 
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 8, v___x_3180_);
v___x_3182_ = v___x_3168_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_env_3158_);
lean_ctor_set(v_reuseFailAlloc_3185_, 1, v_nextMacroScope_3159_);
lean_ctor_set(v_reuseFailAlloc_3185_, 2, v_ngen_3160_);
lean_ctor_set(v_reuseFailAlloc_3185_, 3, v_auxDeclNGen_3161_);
lean_ctor_set(v_reuseFailAlloc_3185_, 4, v_traceState_3162_);
lean_ctor_set(v_reuseFailAlloc_3185_, 5, v_cache_3163_);
lean_ctor_set(v_reuseFailAlloc_3185_, 6, v_recordedDeps_3164_);
lean_ctor_set(v_reuseFailAlloc_3185_, 7, v_messages_3165_);
lean_ctor_set(v_reuseFailAlloc_3185_, 8, v___x_3180_);
lean_ctor_set(v_reuseFailAlloc_3185_, 9, v_snapshotTasks_3166_);
v___x_3182_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3183_ = lean_st_ref_put(v___y_3149_, v___x_3182_);
v___x_3184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3177_);
return v___x_3184_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg___boxed(lean_object* v_t_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
lean_object* v_res_3192_; 
v_res_3192_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3189_, v___y_3190_);
lean_dec(v___y_3190_);
return v_res_3192_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3193_ = lean_unsigned_to_nat(32u);
v___x_3194_ = lean_mk_empty_array_with_capacity(v___x_3193_);
v___x_3195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3194_);
return v___x_3195_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1(void){
_start:
{
size_t v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3196_ = ((size_t)5ULL);
v___x_3197_ = lean_unsigned_to_nat(0u);
v___x_3198_ = lean_unsigned_to_nat(32u);
v___x_3199_ = lean_mk_empty_array_with_capacity(v___x_3198_);
v___x_3200_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0);
v___x_3201_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3201_, 0, v___x_3200_);
lean_ctor_set(v___x_3201_, 1, v___x_3199_);
lean_ctor_set(v___x_3201_, 2, v___x_3197_);
lean_ctor_set(v___x_3201_, 3, v___x_3197_);
lean_ctor_set_usize(v___x_3201_, 4, v___x_3196_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(lean_object* v_t_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_){
_start:
{
lean_object* v___x_3206_; lean_object* v_infoState_3207_; uint8_t v_enabled_3208_; 
v___x_3206_ = lean_st_ref_get(v___y_3204_);
v_infoState_3207_ = lean_ctor_get(v___x_3206_, 8);
lean_inc_ref(v_infoState_3207_);
lean_dec(v___x_3206_);
v_enabled_3208_ = lean_ctor_get_uint8(v_infoState_3207_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3207_);
if (v_enabled_3208_ == 0)
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
lean_dec_ref(v_t_3202_);
v___x_3209_ = lean_box(0);
v___x_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
return v___x_3210_;
}
else
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3211_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1);
v___x_3212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3212_, 0, v_t_3202_);
lean_ctor_set(v___x_3212_, 1, v___x_3211_);
v___x_3213_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v___x_3212_, v___y_3204_);
return v___x_3213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___boxed(lean_object* v_t_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_, lean_object* v___y_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v_t_3214_, v___y_3215_, v___y_3216_);
lean_dec(v___y_3216_);
lean_dec_ref(v___y_3215_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0(lean_object* v___x_3219_, lean_object* v___y_3220_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3219_);
lean_ctor_set(v___x_3221_, 1, v___y_3220_);
return v___x_3221_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__0));
v___x_3224_ = l_Lean_stringToMessageData(v___x_3223_);
return v___x_3224_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__2));
v___x_3227_ = l_Lean_stringToMessageData(v___x_3226_);
return v___x_3227_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29(void){
_start:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3276_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__28));
v___x_3277_ = l_Lean_Json_mkObj(v___x_3276_);
return v___x_3277_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30(void){
_start:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3278_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29);
v___x_3279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__19));
v___x_3280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3279_);
lean_ctor_set(v___x_3280_, 1, v___x_3278_);
return v___x_3280_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31(void){
_start:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3281_ = lean_box(0);
v___x_3282_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30);
v___x_3283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3282_);
lean_ctor_set(v___x_3283_, 1, v___x_3281_);
return v___x_3283_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33(void){
_start:
{
lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3286_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__32));
v___x_3287_ = l_Lean_MessageData_ofFormat(v___x_3286_);
return v___x_3287_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35(void){
_start:
{
lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3289_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__34));
v___x_3290_ = l_Lean_stringToMessageData(v___x_3289_);
return v___x_3290_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(lean_object* v_suggestions_3292_, uint8_t v_forceList_3293_, lean_object* v_codeActionPrefix_x3f_3294_, lean_object* v_ref_3295_, lean_object* v_as_3296_, size_t v_sz_3297_, size_t v_i_3298_, lean_object* v_b_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
lean_object* v_a_3304_; lean_object* v___y_3309_; lean_object* v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3320_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; uint8_t v___x_3348_; 
v___x_3348_ = lean_usize_dec_lt(v_i_3298_, v_sz_3297_);
if (v___x_3348_ == 0)
{
lean_object* v___x_3349_; 
lean_dec(v_ref_3295_);
lean_dec(v_codeActionPrefix_x3f_3294_);
v___x_3349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3349_, 0, v_b_3299_);
return v___x_3349_;
}
else
{
lean_object* v_a_3350_; lean_object* v_span_x3f_3351_; lean_object* v___x_3352_; lean_object* v___y_3354_; lean_object* v___y_3355_; uint8_t v___y_3356_; lean_object* v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3387_; lean_object* v___y_3388_; uint8_t v___y_3389_; lean_object* v___y_3390_; lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; uint8_t v___y_3440_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; uint8_t v___y_3446_; uint8_t v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; lean_object* v_postInfo_x3f_3456_; uint8_t v___y_3457_; lean_object* v___y_3458_; uint8_t v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3464_; lean_object* v___y_3465_; uint8_t v___y_3466_; uint8_t v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v_edits_3470_; lean_object* v___y_3476_; lean_object* v___y_3477_; uint8_t v___y_3478_; lean_object* v___y_3479_; uint8_t v___y_3480_; lean_object* v___y_3481_; lean_object* v_stop_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v_edits_3485_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; uint8_t v___y_3499_; lean_object* v___y_3500_; uint8_t v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v_edits_3505_; lean_object* v___y_3506_; lean_object* v___x_3532_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3538_; uint8_t v___y_3539_; uint8_t v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; uint8_t v___y_3584_; lean_object* v___y_3585_; uint8_t v___y_3586_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3598_; 
v_a_3350_ = lean_array_uget_borrowed(v_as_3296_, v_i_3298_);
v_span_x3f_3351_ = lean_ctor_get(v_a_3350_, 1);
v___x_3352_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_3532_ = l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_;
if (lean_obj_tag(v_span_x3f_3351_) == 0)
{
lean_inc(v_ref_3295_);
v___y_3598_ = v_ref_3295_;
goto v___jp_3597_;
}
else
{
lean_object* v_val_3619_; 
v_val_3619_ = lean_ctor_get(v_span_x3f_3351_, 0);
lean_inc(v_val_3619_);
v___y_3598_ = v_val_3619_;
goto v___jp_3597_;
}
v___jp_3353_:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___f_3374_; 
lean_inc_ref(v___y_3355_);
v___x_3360_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson(v___y_3355_);
v___x_3361_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__9));
v___x_3362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3361_);
lean_ctor_set(v___x_3362_, 1, v___x_3360_);
v___x_3363_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3364_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3364_, 0, v___y_3354_);
v___x_3365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3363_);
lean_ctor_set(v___x_3365_, 1, v___x_3364_);
v___x_3366_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3367_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3357_);
v___x_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3368_, 0, v___x_3366_);
lean_ctor_set(v___x_3368_, 1, v___x_3367_);
v___x_3369_ = lean_box(0);
v___x_3370_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3368_);
lean_ctor_set(v___x_3370_, 1, v___x_3369_);
v___x_3371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3365_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
v___x_3372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3362_);
lean_ctor_set(v___x_3372_, 1, v___x_3371_);
v___x_3373_ = l_Lean_Json_mkObj(v___x_3372_);
lean_dec_ref_known(v___x_3372_, 2);
v___f_3374_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3374_, 0, v___x_3373_);
if (v___y_3356_ == 0)
{
lean_object* v___x_3375_; 
v___x_3375_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString(v___y_3355_);
v___y_3328_ = v___f_3374_;
v___y_3329_ = v___y_3358_;
v___y_3330_ = v___y_3359_;
v___y_3331_ = v___x_3375_;
goto v___jp_3327_;
}
else
{
lean_object* v___x_3376_; lean_object* v___x_3377_; uint8_t v___x_3378_; 
v___x_3376_ = lean_unsigned_to_nat(0u);
v___x_3377_ = lean_array_get_size(v___y_3355_);
v___x_3378_ = lean_nat_dec_lt(v___x_3376_, v___x_3377_);
if (v___x_3378_ == 0)
{
lean_dec_ref(v___y_3355_);
v___y_3328_ = v___f_3374_;
v___y_3329_ = v___y_3358_;
v___y_3330_ = v___y_3359_;
v___y_3331_ = v___x_3352_;
goto v___jp_3327_;
}
else
{
uint8_t v___x_3379_; 
v___x_3379_ = lean_nat_dec_le(v___x_3377_, v___x_3377_);
if (v___x_3379_ == 0)
{
if (v___x_3378_ == 0)
{
lean_dec_ref(v___y_3355_);
v___y_3328_ = v___f_3374_;
v___y_3329_ = v___y_3358_;
v___y_3330_ = v___y_3359_;
v___y_3331_ = v___x_3352_;
goto v___jp_3327_;
}
else
{
size_t v___x_3380_; size_t v___x_3381_; lean_object* v___x_3382_; 
v___x_3380_ = ((size_t)0ULL);
v___x_3381_ = lean_usize_of_nat(v___x_3377_);
v___x_3382_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3355_, v___x_3380_, v___x_3381_, v___x_3352_);
lean_dec_ref(v___y_3355_);
v___y_3328_ = v___f_3374_;
v___y_3329_ = v___y_3358_;
v___y_3330_ = v___y_3359_;
v___y_3331_ = v___x_3382_;
goto v___jp_3327_;
}
}
else
{
size_t v___x_3383_; size_t v___x_3384_; lean_object* v___x_3385_; 
v___x_3383_ = ((size_t)0ULL);
v___x_3384_ = lean_usize_of_nat(v___x_3377_);
v___x_3385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3355_, v___x_3383_, v___x_3384_, v___x_3352_);
lean_dec_ref(v___y_3355_);
v___y_3328_ = v___f_3374_;
v___y_3329_ = v___y_3358_;
v___y_3330_ = v___y_3359_;
v___y_3331_ = v___x_3385_;
goto v___jp_3327_;
}
}
}
}
v___jp_3386_:
{
if (lean_obj_tag(v___y_3393_) == 0)
{
lean_object* v___x_3395_; uint64_t v_javascriptHash_3396_; lean_object* v_suggestion_3397_; lean_object* v_messageData_x3f_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___f_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
lean_dec_ref(v___y_3388_);
v___x_3395_ = ((lean_object*)(l_Lean_Meta_Hint_textInsertionWidget));
v_javascriptHash_3396_ = lean_ctor_get_uint64(v___x_3395_, sizeof(void*)*1);
v_suggestion_3397_ = lean_ctor_get(v___y_3390_, 0);
lean_inc_ref(v_suggestion_3397_);
v_messageData_x3f_3398_ = lean_ctor_get(v___y_3390_, 4);
lean_inc(v_messageData_x3f_3398_);
lean_dec_ref(v___y_3390_);
v___x_3399_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18));
v___x_3400_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3401_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3391_);
v___x_3402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3400_);
lean_ctor_set(v___x_3402_, 1, v___x_3401_);
v___x_3403_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3404_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3404_, 0, v___y_3387_);
v___x_3405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3405_, 0, v___x_3403_);
lean_ctor_set(v___x_3405_, 1, v___x_3404_);
v___x_3406_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31);
v___x_3407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3405_);
lean_ctor_set(v___x_3407_, 1, v___x_3406_);
v___x_3408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3402_);
lean_ctor_set(v___x_3408_, 1, v___x_3407_);
v___x_3409_ = l_Lean_Json_mkObj(v___x_3408_);
lean_dec_ref_known(v___x_3408_, 2);
v___f_3410_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3410_, 0, v___x_3409_);
v___x_3411_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3411_, 0, v___x_3399_);
lean_ctor_set(v___x_3411_, 1, v___f_3410_);
lean_ctor_set_uint64(v___x_3411_, sizeof(void*)*2, v_javascriptHash_3396_);
v___x_3412_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33);
v___x_3413_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3411_);
lean_ctor_set(v___x_3413_, 1, v___x_3412_);
v___x_3414_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3415_, 0, v___x_3414_);
lean_ctor_set(v___x_3415_, 1, v___x_3413_);
v___x_3416_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35);
v___x_3417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3415_);
lean_ctor_set(v___x_3417_, 1, v___x_3416_);
v___x_3418_ = l_Lean_stringToMessageData(v___y_3394_);
v___x_3419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3417_);
lean_ctor_set(v___x_3419_, 1, v___x_3418_);
if (lean_obj_tag(v_messageData_x3f_3398_) == 0)
{
if (lean_obj_tag(v_suggestion_3397_) == 0)
{
lean_object* v_a_3420_; lean_object* v___x_3421_; 
v_a_3420_ = lean_ctor_get(v_suggestion_3397_, 1);
lean_inc(v_a_3420_);
lean_dec_ref_known(v_suggestion_3397_, 2);
v___x_3421_ = l_Lean_MessageData_ofSyntax(v_a_3420_);
v___y_3313_ = v___x_3419_;
v___y_3314_ = v___y_3392_;
v___y_3315_ = v___x_3421_;
goto v___jp_3312_;
}
else
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3430_; 
v_a_3422_ = lean_ctor_get(v_suggestion_3397_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v_suggestion_3397_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3424_ = v_suggestion_3397_;
v_isShared_3425_ = v_isSharedCheck_3430_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v_suggestion_3397_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3430_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3427_; 
if (v_isShared_3425_ == 0)
{
lean_ctor_set_tag(v___x_3424_, 3);
v___x_3427_ = v___x_3424_;
goto v_reusejp_3426_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3422_);
v___x_3427_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3426_;
}
v_reusejp_3426_:
{
lean_object* v___x_3428_; 
v___x_3428_ = l_Lean_MessageData_ofFormat(v___x_3427_);
v___y_3313_ = v___x_3419_;
v___y_3314_ = v___y_3392_;
v___y_3315_ = v___x_3428_;
goto v___jp_3312_;
}
}
}
}
else
{
lean_object* v_val_3431_; 
lean_dec_ref(v_suggestion_3397_);
v_val_3431_ = lean_ctor_get(v_messageData_x3f_3398_, 0);
lean_inc(v_val_3431_);
lean_dec_ref_known(v_messageData_x3f_3398_, 1);
v___y_3313_ = v___x_3419_;
v___y_3314_ = v___y_3392_;
v___y_3315_ = v_val_3431_;
goto v___jp_3312_;
}
}
else
{
lean_dec_ref_known(v___y_3393_, 1);
lean_dec_ref(v___y_3390_);
v___y_3354_ = v___y_3387_;
v___y_3355_ = v___y_3388_;
v___y_3356_ = v___y_3389_;
v___y_3357_ = v___y_3391_;
v___y_3358_ = v___y_3392_;
v___y_3359_ = v___y_3394_;
goto v___jp_3353_;
}
}
v___jp_3432_:
{
if (v___y_3440_ == 0)
{
lean_object* v_messageData_x3f_3441_; 
v_messageData_x3f_3441_ = lean_ctor_get(v___y_3435_, 4);
if (lean_obj_tag(v_messageData_x3f_3441_) == 0)
{
lean_dec(v___y_3437_);
lean_dec_ref(v___y_3435_);
v___y_3354_ = v___y_3433_;
v___y_3355_ = v___y_3434_;
v___y_3356_ = v___y_3440_;
v___y_3357_ = v___y_3436_;
v___y_3358_ = v___y_3438_;
v___y_3359_ = v___y_3439_;
goto v___jp_3353_;
}
else
{
v___y_3387_ = v___y_3433_;
v___y_3388_ = v___y_3434_;
v___y_3389_ = v___y_3440_;
v___y_3390_ = v___y_3435_;
v___y_3391_ = v___y_3436_;
v___y_3392_ = v___y_3438_;
v___y_3393_ = v___y_3437_;
v___y_3394_ = v___y_3439_;
goto v___jp_3386_;
}
}
else
{
v___y_3387_ = v___y_3433_;
v___y_3388_ = v___y_3434_;
v___y_3389_ = v___y_3440_;
v___y_3390_ = v___y_3435_;
v___y_3391_ = v___y_3436_;
v___y_3392_ = v___y_3438_;
v___y_3393_ = v___y_3437_;
v___y_3394_ = v___y_3439_;
goto v___jp_3386_;
}
}
v___jp_3442_:
{
if (v___y_3447_ == 4)
{
v___y_3433_ = v___y_3443_;
v___y_3434_ = v___y_3444_;
v___y_3435_ = v___y_3445_;
v___y_3436_ = v___y_3448_;
v___y_3437_ = v___y_3449_;
v___y_3438_ = v___y_3451_;
v___y_3439_ = v___y_3450_;
v___y_3440_ = v___x_3348_;
goto v___jp_3432_;
}
else
{
v___y_3433_ = v___y_3443_;
v___y_3434_ = v___y_3444_;
v___y_3435_ = v___y_3445_;
v___y_3436_ = v___y_3448_;
v___y_3437_ = v___y_3449_;
v___y_3438_ = v___y_3451_;
v___y_3439_ = v___y_3450_;
v___y_3440_ = v___y_3446_;
goto v___jp_3432_;
}
}
v___jp_3452_:
{
if (lean_obj_tag(v_postInfo_x3f_3456_) == 0)
{
v___y_3443_ = v___y_3453_;
v___y_3444_ = v___y_3454_;
v___y_3445_ = v___y_3455_;
v___y_3446_ = v___y_3457_;
v___y_3447_ = v___y_3459_;
v___y_3448_ = v___y_3458_;
v___y_3449_ = v___y_3460_;
v___y_3450_ = v___y_3461_;
v___y_3451_ = v___x_3352_;
goto v___jp_3442_;
}
else
{
lean_object* v_val_3462_; 
v_val_3462_ = lean_ctor_get(v_postInfo_x3f_3456_, 0);
lean_inc(v_val_3462_);
lean_dec_ref_known(v_postInfo_x3f_3456_, 1);
v___y_3443_ = v___y_3453_;
v___y_3444_ = v___y_3454_;
v___y_3445_ = v___y_3455_;
v___y_3446_ = v___y_3457_;
v___y_3447_ = v___y_3459_;
v___y_3448_ = v___y_3458_;
v___y_3449_ = v___y_3460_;
v___y_3450_ = v___y_3461_;
v___y_3451_ = v_val_3462_;
goto v___jp_3442_;
}
}
v___jp_3463_:
{
lean_object* v_preInfo_x3f_3471_; 
v_preInfo_x3f_3471_ = lean_ctor_get(v___y_3465_, 1);
if (lean_obj_tag(v_preInfo_x3f_3471_) == 0)
{
lean_object* v_postInfo_x3f_3472_; 
v_postInfo_x3f_3472_ = lean_ctor_get(v___y_3465_, 2);
lean_inc(v_postInfo_x3f_3472_);
v___y_3453_ = v___y_3464_;
v___y_3454_ = v_edits_3470_;
v___y_3455_ = v___y_3465_;
v_postInfo_x3f_3456_ = v_postInfo_x3f_3472_;
v___y_3457_ = v___y_3466_;
v___y_3458_ = v___y_3468_;
v___y_3459_ = v___y_3467_;
v___y_3460_ = v___y_3469_;
v___y_3461_ = v___x_3352_;
goto v___jp_3452_;
}
else
{
lean_object* v_postInfo_x3f_3473_; lean_object* v_val_3474_; 
v_postInfo_x3f_3473_ = lean_ctor_get(v___y_3465_, 2);
lean_inc(v_postInfo_x3f_3473_);
v_val_3474_ = lean_ctor_get(v_preInfo_x3f_3471_, 0);
lean_inc(v_val_3474_);
v___y_3453_ = v___y_3464_;
v___y_3454_ = v_edits_3470_;
v___y_3455_ = v___y_3465_;
v_postInfo_x3f_3456_ = v_postInfo_x3f_3473_;
v___y_3457_ = v___y_3466_;
v___y_3458_ = v___y_3468_;
v___y_3459_ = v___y_3467_;
v___y_3460_ = v___y_3469_;
v___y_3461_ = v_val_3474_;
goto v___jp_3452_;
}
}
v___jp_3475_:
{
lean_object* v___x_3486_; lean_object* v___x_3487_; uint8_t v___x_3488_; 
v___x_3486_ = lean_unsigned_to_nat(1u);
v___x_3487_ = lean_nat_add(v___y_3481_, v___x_3486_);
v___x_3488_ = lean_nat_dec_le(v___x_3487_, v_stop_3482_);
lean_dec(v___x_3487_);
if (v___x_3488_ == 0)
{
lean_dec(v_stop_3482_);
lean_dec(v___y_3481_);
v___y_3464_ = v___y_3476_;
v___y_3465_ = v___y_3477_;
v___y_3466_ = v___y_3478_;
v___y_3467_ = v___y_3480_;
v___y_3468_ = v___y_3479_;
v___y_3469_ = v___y_3483_;
v_edits_3470_ = v_edits_3485_;
goto v___jp_3463_;
}
else
{
lean_object* v_source_3489_; uint8_t v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v_source_3489_ = lean_ctor_get(v___y_3484_, 0);
v___x_3490_ = 2;
v___x_3491_ = lean_string_utf8_extract(v_source_3489_, v___y_3481_, v_stop_3482_);
lean_dec(v_stop_3482_);
lean_dec(v___y_3481_);
v___x_3492_ = lean_box(v___x_3490_);
v___x_3493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3492_);
lean_ctor_set(v___x_3493_, 1, v___x_3491_);
v___x_3494_ = lean_array_push(v_edits_3485_, v___x_3493_);
v___y_3464_ = v___y_3476_;
v___y_3465_ = v___y_3477_;
v___y_3466_ = v___y_3478_;
v___y_3467_ = v___y_3480_;
v___y_3468_ = v___y_3479_;
v___y_3469_ = v___y_3483_;
v_edits_3470_ = v___x_3494_;
goto v___jp_3463_;
}
}
v___jp_3495_:
{
if (lean_obj_tag(v___y_3504_) == 0)
{
lean_dec(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3497_);
v___y_3464_ = v___y_3496_;
v___y_3465_ = v___y_3498_;
v___y_3466_ = v___y_3499_;
v___y_3467_ = v___y_3501_;
v___y_3468_ = v___y_3500_;
v___y_3469_ = v___y_3504_;
v_edits_3470_ = v_edits_3505_;
goto v___jp_3463_;
}
else
{
lean_object* v_val_3507_; lean_object* v___x_3508_; 
v_val_3507_ = lean_ctor_get(v___y_3504_, 0);
v___x_3508_ = l_Lean_Syntax_getRange_x3f(v_val_3507_, v___y_3499_);
if (lean_obj_tag(v___x_3508_) == 1)
{
lean_object* v_val_3509_; uint8_t v___x_3510_; 
v_val_3509_ = lean_ctor_get(v___x_3508_, 0);
lean_inc(v_val_3509_);
lean_dec_ref_known(v___x_3508_, 1);
v___x_3510_ = l_Lean_Syntax_Range_includes(v_val_3509_, v___y_3497_, v___y_3499_, v___y_3499_);
lean_dec_ref(v___y_3497_);
if (v___x_3510_ == 0)
{
lean_dec(v_val_3509_);
lean_dec(v___y_3503_);
lean_dec(v___y_3502_);
v___y_3464_ = v___y_3496_;
v___y_3465_ = v___y_3498_;
v___y_3466_ = v___y_3499_;
v___y_3467_ = v___y_3501_;
v___y_3468_ = v___y_3500_;
v___y_3469_ = v___y_3504_;
v_edits_3470_ = v_edits_3505_;
goto v___jp_3463_;
}
else
{
lean_object* v_toCold_3511_; lean_object* v_fileMap_3512_; lean_object* v_start_3513_; lean_object* v_stop_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3531_; 
v_toCold_3511_ = lean_ctor_get(v___y_3506_, 0);
v_fileMap_3512_ = lean_ctor_get(v_toCold_3511_, 1);
v_start_3513_ = lean_ctor_get(v_val_3509_, 0);
v_stop_3514_ = lean_ctor_get(v_val_3509_, 1);
v_isSharedCheck_3531_ = !lean_is_exclusive(v_val_3509_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3516_ = v_val_3509_;
v_isShared_3517_ = v_isSharedCheck_3531_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_stop_3514_);
lean_inc(v_start_3513_);
lean_dec(v_val_3509_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3531_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; uint8_t v___x_3520_; 
v___x_3518_ = lean_unsigned_to_nat(1u);
v___x_3519_ = lean_nat_add(v_start_3513_, v___x_3518_);
v___x_3520_ = lean_nat_dec_le(v___x_3519_, v___y_3502_);
lean_dec(v___x_3519_);
if (v___x_3520_ == 0)
{
lean_del_object(v___x_3516_);
lean_dec(v_start_3513_);
lean_dec(v___y_3502_);
v___y_3476_ = v___y_3496_;
v___y_3477_ = v___y_3498_;
v___y_3478_ = v___y_3499_;
v___y_3479_ = v___y_3500_;
v___y_3480_ = v___y_3501_;
v___y_3481_ = v___y_3503_;
v_stop_3482_ = v_stop_3514_;
v___y_3483_ = v___y_3504_;
v___y_3484_ = v_fileMap_3512_;
v_edits_3485_ = v_edits_3505_;
goto v___jp_3475_;
}
else
{
lean_object* v_source_3521_; uint8_t v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3526_; 
v_source_3521_ = lean_ctor_get(v_fileMap_3512_, 0);
v___x_3522_ = 2;
v___x_3523_ = lean_string_utf8_extract(v_source_3521_, v_start_3513_, v___y_3502_);
lean_dec(v___y_3502_);
lean_dec(v_start_3513_);
v___x_3524_ = lean_box(v___x_3522_);
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 1, v___x_3523_);
lean_ctor_set(v___x_3516_, 0, v___x_3524_);
v___x_3526_ = v___x_3516_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3524_);
lean_ctor_set(v_reuseFailAlloc_3530_, 1, v___x_3523_);
v___x_3526_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3527_ = lean_mk_empty_array_with_capacity(v___x_3518_);
v___x_3528_ = lean_array_push(v___x_3527_, v___x_3526_);
v___x_3529_ = l_Array_append___redArg(v___x_3528_, v_edits_3505_);
lean_dec_ref(v_edits_3505_);
v___y_3476_ = v___y_3496_;
v___y_3477_ = v___y_3498_;
v___y_3478_ = v___y_3499_;
v___y_3479_ = v___y_3500_;
v___y_3480_ = v___y_3501_;
v___y_3481_ = v___y_3503_;
v_stop_3482_ = v_stop_3514_;
v___y_3483_ = v___y_3504_;
v___y_3484_ = v_fileMap_3512_;
v_edits_3485_ = v___x_3529_;
goto v___jp_3475_;
}
}
}
}
}
else
{
lean_dec(v___x_3508_);
lean_dec(v___y_3503_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3497_);
v___y_3464_ = v___y_3496_;
v___y_3465_ = v___y_3498_;
v___y_3466_ = v___y_3499_;
v___y_3467_ = v___y_3501_;
v___y_3468_ = v___y_3500_;
v___y_3469_ = v___y_3504_;
v_edits_3470_ = v_edits_3505_;
goto v___jp_3463_;
}
}
}
v___jp_3533_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
lean_inc_ref(v___y_3538_);
v___x_3544_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3544_, 0, v___y_3536_);
lean_ctor_set(v___x_3544_, 1, v___y_3543_);
lean_ctor_set(v___x_3544_, 2, v___y_3538_);
v___x_3545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3532_);
lean_ctor_set(v___x_3545_, 1, v___x_3544_);
v___x_3546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3546_, 0, v___y_3535_);
lean_ctor_set(v___x_3546_, 1, v___x_3545_);
v___x_3547_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3546_);
v___x_3548_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v___x_3547_, v___y_3300_, v___y_3301_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_messageData_x3f_3549_; 
lean_dec_ref_known(v___x_3548_, 1);
v_messageData_x3f_3549_ = lean_ctor_get(v___y_3538_, 4);
if (lean_obj_tag(v_messageData_x3f_3549_) == 1)
{
lean_object* v_start_3550_; lean_object* v_stop_3551_; lean_object* v_val_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; uint8_t v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v_start_3550_ = lean_ctor_get(v___y_3537_, 0);
lean_inc(v_start_3550_);
v_stop_3551_ = lean_ctor_get(v___y_3537_, 1);
lean_inc(v_stop_3551_);
v_val_3552_ = lean_ctor_get(v_messageData_x3f_3549_, 0);
v___x_3553_ = lean_box(0);
lean_inc(v_val_3552_);
v___x_3554_ = l_Lean_MessageData_format(v_val_3552_, v___x_3553_);
v___x_3555_ = 0;
v___x_3556_ = l_Std_Format_defWidth;
v___x_3557_ = lean_unsigned_to_nat(0u);
v___x_3558_ = l_Std_Format_pretty(v___x_3554_, v___x_3556_, v___x_3557_, v___x_3557_);
v___x_3559_ = lean_box(v___x_3555_);
v___x_3560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3560_, 0, v___x_3559_);
lean_ctor_set(v___x_3560_, 1, v___x_3558_);
v___x_3561_ = lean_unsigned_to_nat(1u);
v___x_3562_ = lean_mk_empty_array_with_capacity(v___x_3561_);
v___x_3563_ = lean_array_push(v___x_3562_, v___x_3560_);
v___y_3496_ = v___y_3534_;
v___y_3497_ = v___y_3537_;
v___y_3498_ = v___y_3538_;
v___y_3499_ = v___y_3539_;
v___y_3500_ = v___y_3541_;
v___y_3501_ = v___y_3540_;
v___y_3502_ = v_start_3550_;
v___y_3503_ = v_stop_3551_;
v___y_3504_ = v___y_3542_;
v_edits_3505_ = v___x_3563_;
v___y_3506_ = v___y_3300_;
goto v___jp_3495_;
}
else
{
lean_object* v_toCold_3564_; lean_object* v_fileMap_3565_; lean_object* v_start_3566_; lean_object* v_stop_3567_; lean_object* v_source_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; 
v_toCold_3564_ = lean_ctor_get(v___y_3300_, 0);
v_fileMap_3565_ = lean_ctor_get(v_toCold_3564_, 1);
v_start_3566_ = lean_ctor_get(v___y_3537_, 0);
lean_inc(v_start_3566_);
v_stop_3567_ = lean_ctor_get(v___y_3537_, 1);
lean_inc(v_stop_3567_);
v_source_3568_ = lean_ctor_get(v_fileMap_3565_, 0);
v___x_3569_ = lean_string_utf8_extract(v_source_3568_, v_start_3566_, v_stop_3567_);
lean_inc_ref(v___y_3534_);
v___x_3570_ = l_Lean_Meta_Hint_readableDiff(v___x_3569_, v___y_3534_, v___y_3540_);
v___y_3496_ = v___y_3534_;
v___y_3497_ = v___y_3537_;
v___y_3498_ = v___y_3538_;
v___y_3499_ = v___y_3539_;
v___y_3500_ = v___y_3541_;
v___y_3501_ = v___y_3540_;
v___y_3502_ = v_start_3566_;
v___y_3503_ = v_stop_3567_;
v___y_3504_ = v___y_3542_;
v_edits_3505_ = v___x_3570_;
v___y_3506_ = v___y_3300_;
goto v___jp_3495_;
}
}
else
{
lean_object* v_a_3571_; lean_object* v___x_3573_; uint8_t v_isShared_3574_; uint8_t v_isSharedCheck_3578_; 
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec_ref(v___y_3538_);
lean_dec_ref(v___y_3537_);
lean_dec_ref(v___y_3534_);
lean_dec_ref(v_b_3299_);
lean_dec(v_ref_3295_);
lean_dec(v_codeActionPrefix_x3f_3294_);
v_a_3571_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3573_ = v___x_3548_;
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
else
{
lean_inc(v_a_3571_);
lean_dec(v___x_3548_);
v___x_3573_ = lean_box(0);
v_isShared_3574_ = v_isSharedCheck_3578_;
goto v_resetjp_3572_;
}
v_resetjp_3572_:
{
lean_object* v___x_3576_; 
if (v_isShared_3574_ == 0)
{
v___x_3576_ = v___x_3573_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_a_3571_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
}
v___jp_3579_:
{
lean_object* v_toCodeActionTitle_x3f_3589_; lean_object* v___x_3590_; 
v_toCodeActionTitle_x3f_3589_ = lean_ctor_get(v___y_3583_, 5);
v___x_3590_ = l_Lean_Syntax_ofRange(v___y_3588_, v___x_3348_);
if (lean_obj_tag(v_toCodeActionTitle_x3f_3589_) == 0)
{
if (lean_obj_tag(v_codeActionPrefix_x3f_3294_) == 0)
{
lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__36));
v___x_3592_ = lean_string_append(v___x_3591_, v___y_3580_);
v___y_3534_ = v___y_3580_;
v___y_3535_ = v___x_3590_;
v___y_3536_ = v___y_3581_;
v___y_3537_ = v___y_3582_;
v___y_3538_ = v___y_3583_;
v___y_3539_ = v___y_3584_;
v___y_3540_ = v___y_3586_;
v___y_3541_ = v___y_3585_;
v___y_3542_ = v___y_3587_;
v___y_3543_ = v___x_3592_;
goto v___jp_3533_;
}
else
{
lean_object* v_val_3593_; lean_object* v___x_3594_; 
v_val_3593_ = lean_ctor_get(v_codeActionPrefix_x3f_3294_, 0);
lean_inc(v_val_3593_);
v___x_3594_ = lean_string_append(v_val_3593_, v___y_3580_);
v___y_3534_ = v___y_3580_;
v___y_3535_ = v___x_3590_;
v___y_3536_ = v___y_3581_;
v___y_3537_ = v___y_3582_;
v___y_3538_ = v___y_3583_;
v___y_3539_ = v___y_3584_;
v___y_3540_ = v___y_3586_;
v___y_3541_ = v___y_3585_;
v___y_3542_ = v___y_3587_;
v___y_3543_ = v___x_3594_;
goto v___jp_3533_;
}
}
else
{
lean_object* v_val_3595_; lean_object* v___x_3596_; 
v_val_3595_ = lean_ctor_get(v_toCodeActionTitle_x3f_3589_, 0);
lean_inc(v_val_3595_);
lean_inc_ref(v___y_3580_);
v___x_3596_ = lean_apply_1(v_val_3595_, v___y_3580_);
v___y_3534_ = v___y_3580_;
v___y_3535_ = v___x_3590_;
v___y_3536_ = v___y_3581_;
v___y_3537_ = v___y_3582_;
v___y_3538_ = v___y_3583_;
v___y_3539_ = v___y_3584_;
v___y_3540_ = v___y_3586_;
v___y_3541_ = v___y_3585_;
v___y_3542_ = v___y_3587_;
v___y_3543_ = v___x_3596_;
goto v___jp_3533_;
}
}
v___jp_3597_:
{
uint8_t v___x_3599_; lean_object* v___x_3600_; 
v___x_3599_ = 0;
v___x_3600_ = l_Lean_Syntax_getRange_x3f(v___y_3598_, v___x_3599_);
lean_dec(v___y_3598_);
if (lean_obj_tag(v___x_3600_) == 1)
{
lean_object* v_val_3601_; lean_object* v_toTryThisSuggestion_3602_; lean_object* v_previewSpan_x3f_3603_; uint8_t v_diffGranularity_3604_; lean_object* v___x_3605_; 
v_val_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc_n(v_val_3601_, 2);
lean_dec_ref_known(v___x_3600_, 1);
v_toTryThisSuggestion_3602_ = lean_ctor_get(v_a_3350_, 0);
v_previewSpan_x3f_3603_ = lean_ctor_get(v_a_3350_, 2);
v_diffGranularity_3604_ = lean_ctor_get_uint8(v_a_3350_, sizeof(void*)*3);
lean_inc_ref(v_toTryThisSuggestion_3602_);
v___x_3605_ = l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(v_toTryThisSuggestion_3602_, v_val_3601_, v___y_3300_, v___y_3301_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_a_3606_; lean_object* v_range_3607_; lean_object* v_newText_3608_; lean_object* v___x_3609_; 
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_a_3606_);
lean_dec_ref_known(v___x_3605_, 1);
v_range_3607_ = lean_ctor_get(v_a_3606_, 0);
lean_inc_ref(v_range_3607_);
v_newText_3608_ = lean_ctor_get(v_a_3606_, 1);
lean_inc_ref(v_newText_3608_);
v___x_3609_ = l_Lean_Syntax_getRange_x3f(v_ref_3295_, v___x_3599_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_inc(v_previewSpan_x3f_3603_);
lean_inc_ref(v_toTryThisSuggestion_3602_);
lean_inc(v_val_3601_);
v___y_3580_ = v_newText_3608_;
v___y_3581_ = v_a_3606_;
v___y_3582_ = v_val_3601_;
v___y_3583_ = v_toTryThisSuggestion_3602_;
v___y_3584_ = v___x_3599_;
v___y_3585_ = v_range_3607_;
v___y_3586_ = v_diffGranularity_3604_;
v___y_3587_ = v_previewSpan_x3f_3603_;
v___y_3588_ = v_val_3601_;
goto v___jp_3579_;
}
else
{
lean_object* v_val_3610_; 
v_val_3610_ = lean_ctor_get(v___x_3609_, 0);
lean_inc(v_val_3610_);
lean_dec_ref_known(v___x_3609_, 1);
lean_inc(v_previewSpan_x3f_3603_);
lean_inc_ref(v_toTryThisSuggestion_3602_);
v___y_3580_ = v_newText_3608_;
v___y_3581_ = v_a_3606_;
v___y_3582_ = v_val_3601_;
v___y_3583_ = v_toTryThisSuggestion_3602_;
v___y_3584_ = v___x_3599_;
v___y_3585_ = v_range_3607_;
v___y_3586_ = v_diffGranularity_3604_;
v___y_3587_ = v_previewSpan_x3f_3603_;
v___y_3588_ = v_val_3610_;
goto v___jp_3579_;
}
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec(v_val_3601_);
lean_dec_ref(v_b_3299_);
lean_dec(v_ref_3295_);
lean_dec(v_codeActionPrefix_x3f_3294_);
v_a_3611_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3605_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3605_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
else
{
lean_dec(v___x_3600_);
v_a_3304_ = v_b_3299_;
goto v___jp_3303_;
}
}
}
v___jp_3303_:
{
size_t v___x_3305_; size_t v___x_3306_; 
v___x_3305_ = ((size_t)1ULL);
v___x_3306_ = lean_usize_add(v_i_3298_, v___x_3305_);
v_i_3298_ = v___x_3306_;
v_b_3299_ = v_a_3304_;
goto _start;
}
v___jp_3308_:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3310_ = l_Lean_MessageData_nestD(v___y_3309_);
v___x_3311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3311_, 0, v_b_3299_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
v_a_3304_ = v___x_3311_;
goto v___jp_3303_;
}
v___jp_3312_:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; 
v___x_3316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___y_3313_);
lean_ctor_set(v___x_3316_, 1, v___y_3315_);
v___x_3317_ = l_Lean_stringToMessageData(v___y_3314_);
v___x_3318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3316_);
lean_ctor_set(v___x_3318_, 1, v___x_3317_);
v___y_3309_ = v___x_3318_;
goto v___jp_3308_;
}
v___jp_3319_:
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; 
v___x_3321_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3322_ = lean_unsigned_to_nat(2u);
v___x_3323_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3);
v___x_3324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
lean_ctor_set(v___x_3324_, 1, v___y_3320_);
v___x_3325_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3322_);
lean_ctor_set(v___x_3325_, 1, v___x_3324_);
v___x_3326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3321_);
lean_ctor_set(v___x_3326_, 1, v___x_3325_);
v___y_3309_ = v___x_3326_;
goto v___jp_3308_;
}
v___jp_3327_:
{
lean_object* v___x_3332_; uint64_t v_javascriptHash_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; uint8_t v___x_3345_; 
v___x_3332_ = ((lean_object*)(l_Lean_Meta_Hint_tryThisDiffWidget));
v_javascriptHash_3333_ = lean_ctor_get_uint64(v___x_3332_, sizeof(void*)*1);
v___x_3334_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8));
v___x_3335_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
lean_ctor_set(v___x_3335_, 1, v___y_3328_);
lean_ctor_set_uint64(v___x_3335_, sizeof(void*)*2, v_javascriptHash_3333_);
v___x_3336_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3336_, 0, v___y_3331_);
v___x_3337_ = l_Lean_MessageData_ofFormat(v___x_3336_);
v___x_3338_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3335_);
lean_ctor_set(v___x_3338_, 1, v___x_3337_);
v___x_3339_ = l_Lean_stringToMessageData(v___y_3330_);
v___x_3340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3340_, 0, v___x_3339_);
lean_ctor_set(v___x_3340_, 1, v___x_3338_);
v___x_3341_ = l_Lean_stringToMessageData(v___y_3329_);
v___x_3342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3340_);
lean_ctor_set(v___x_3342_, 1, v___x_3341_);
v___x_3343_ = lean_array_get_size(v_suggestions_3292_);
v___x_3344_ = lean_unsigned_to_nat(1u);
v___x_3345_ = lean_nat_dec_eq(v___x_3343_, v___x_3344_);
if (v___x_3345_ == 0)
{
v___y_3320_ = v___x_3342_;
goto v___jp_3319_;
}
else
{
if (v_forceList_3293_ == 0)
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
lean_ctor_set(v___x_3347_, 1, v___x_3342_);
v___y_3309_ = v___x_3347_;
goto v___jp_3308_;
}
else
{
v___y_3320_ = v___x_3342_;
goto v___jp_3319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___boxed(lean_object* v_suggestions_3620_, lean_object* v_forceList_3621_, lean_object* v_codeActionPrefix_x3f_3622_, lean_object* v_ref_3623_, lean_object* v_as_3624_, lean_object* v_sz_3625_, lean_object* v_i_3626_, lean_object* v_b_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
uint8_t v_forceList_boxed_3631_; size_t v_sz_boxed_3632_; size_t v_i_boxed_3633_; lean_object* v_res_3634_; 
v_forceList_boxed_3631_ = lean_unbox(v_forceList_3621_);
v_sz_boxed_3632_ = lean_unbox_usize(v_sz_3625_);
lean_dec(v_sz_3625_);
v_i_boxed_3633_ = lean_unbox_usize(v_i_3626_);
lean_dec(v_i_3626_);
v_res_3634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3620_, v_forceList_boxed_3631_, v_codeActionPrefix_x3f_3622_, v_ref_3623_, v_as_3624_, v_sz_boxed_3632_, v_i_boxed_3633_, v_b_3627_, v___y_3628_, v___y_3629_);
lean_dec(v___y_3629_);
lean_dec_ref(v___y_3628_);
lean_dec_ref(v_as_3624_);
lean_dec_ref(v_suggestions_3620_);
return v_res_3634_;
}
}
static lean_object* _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0(void){
_start:
{
lean_object* v___x_3635_; lean_object* v_msg_3636_; 
v___x_3635_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v_msg_3636_ = l_Lean_stringToMessageData(v___x_3635_);
return v_msg_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage(lean_object* v_suggestions_3637_, lean_object* v_ref_3638_, lean_object* v_codeActionPrefix_x3f_3639_, uint8_t v_forceList_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_){
_start:
{
lean_object* v_msg_3644_; size_t v_sz_3645_; size_t v___x_3646_; lean_object* v___x_3647_; 
v_msg_3644_ = lean_obj_once(&l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0, &l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0_once, _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0);
v_sz_3645_ = lean_array_size(v_suggestions_3637_);
v___x_3646_ = ((size_t)0ULL);
v___x_3647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3637_, v_forceList_3640_, v_codeActionPrefix_x3f_3639_, v_ref_3638_, v_suggestions_3637_, v_sz_3645_, v___x_3646_, v_msg_3644_, v_a_3641_, v_a_3642_);
return v___x_3647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage___boxed(lean_object* v_suggestions_3648_, lean_object* v_ref_3649_, lean_object* v_codeActionPrefix_x3f_3650_, lean_object* v_forceList_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_){
_start:
{
uint8_t v_forceList_boxed_3655_; lean_object* v_res_3656_; 
v_forceList_boxed_3655_ = lean_unbox(v_forceList_3651_);
v_res_3656_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3648_, v_ref_3649_, v_codeActionPrefix_x3f_3650_, v_forceList_boxed_3655_, v_a_3652_, v_a_3653_);
lean_dec(v_a_3653_);
lean_dec_ref(v_a_3652_);
lean_dec_ref(v_suggestions_3648_);
return v_res_3656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(lean_object* v_t_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
lean_object* v___x_3661_; 
v___x_3661_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3657_, v___y_3659_);
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___boxed(lean_object* v_t_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(v_t_3662_, v___y_3663_, v___y_3664_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
return v_res_3666_;
}
}
static lean_object* _init_l_Lean_MessageData_hint___closed__3(void){
_start:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3671_ = ((lean_object*)(l_Lean_MessageData_hint___closed__2));
v___x_3672_ = l_Lean_stringToMessageData(v___x_3671_);
return v___x_3672_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint(lean_object* v_hint_3673_, lean_object* v_suggestions_3674_, lean_object* v_ref_x3f_3675_, lean_object* v_codeActionPrefix_x3f_3676_, uint8_t v_forceList_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_){
_start:
{
lean_object* v___y_3682_; 
if (lean_obj_tag(v_ref_x3f_3675_) == 0)
{
lean_object* v_ref_3697_; 
v_ref_3697_ = lean_ctor_get(v_a_3678_, 2);
lean_inc(v_ref_3697_);
v___y_3682_ = v_ref_3697_;
goto v___jp_3681_;
}
else
{
lean_object* v_val_3698_; 
v_val_3698_ = lean_ctor_get(v_ref_x3f_3675_, 0);
lean_inc(v_val_3698_);
lean_dec_ref_known(v_ref_x3f_3675_, 1);
v___y_3682_ = v_val_3698_;
goto v___jp_3681_;
}
v___jp_3681_:
{
lean_object* v___x_3683_; 
v___x_3683_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3674_, v___y_3682_, v_codeActionPrefix_x3f_3676_, v_forceList_3677_, v_a_3678_, v_a_3679_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v_a_3684_; lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3696_; 
v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3686_ = v___x_3683_;
v_isShared_3687_ = v_isSharedCheck_3696_;
goto v_resetjp_3685_;
}
else
{
lean_inc(v_a_3684_);
lean_dec(v___x_3683_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3696_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3694_; 
v___x_3688_ = ((lean_object*)(l_Lean_MessageData_hint___closed__1));
v___x_3689_ = lean_obj_once(&l_Lean_MessageData_hint___closed__3, &l_Lean_MessageData_hint___closed__3_once, _init_l_Lean_MessageData_hint___closed__3);
v___x_3690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3689_);
lean_ctor_set(v___x_3690_, 1, v_hint_3673_);
v___x_3691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3690_);
lean_ctor_set(v___x_3691_, 1, v_a_3684_);
v___x_3692_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3688_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set(v___x_3686_, 0, v___x_3692_);
v___x_3694_ = v___x_3686_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3692_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
else
{
lean_dec_ref(v_hint_3673_);
return v___x_3683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint___boxed(lean_object* v_hint_3699_, lean_object* v_suggestions_3700_, lean_object* v_ref_x3f_3701_, lean_object* v_codeActionPrefix_x3f_3702_, lean_object* v_forceList_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_){
_start:
{
uint8_t v_forceList_boxed_3707_; lean_object* v_res_3708_; 
v_forceList_boxed_3707_ = lean_unbox(v_forceList_3703_);
v_res_3708_ = l_Lean_MessageData_hint(v_hint_3699_, v_suggestions_3700_, v_ref_x3f_3701_, v_codeActionPrefix_x3f_3702_, v_forceList_boxed_3707_, v_a_3704_, v_a_3705_);
lean_dec(v_a_3705_);
lean_dec_ref(v_a_3704_);
lean_dec_ref(v_suggestions_3700_);
return v_res_3708_;
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
