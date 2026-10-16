// Lean compiler output
// Module: Lean.Meta.Hint
// Imports: public import Lean.Meta.TryThis public import Lean.Util.Diff import Init.Data.String.Csimp
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Subarray_get___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
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
lean_object* l_String_toListImpl(lean_object*);
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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorIdx___impl___boxed(lean_object*);
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
v___x_172_ = l_String_toListImpl(v_snd_162_);
v___x_173_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_174_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0(v___x_172_, v___x_173_);
v___x_175_ = lean_string_mk(v___x_174_);
v___y_166_ = v___x_175_;
goto v___jp_165_;
}
case 1:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_176_ = l_String_toListImpl(v_snd_162_);
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
size_t v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_usize_of_nat(v___x_210_);
v___x_213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_rangeStrs_207_, v___x_206_, v___x_212_, v___x_208_);
lean_dec_ref(v_rangeStrs_207_);
return v___x_213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorIdx___impl(uint8_t v_x_214_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_box(v_x_214_);
v___x_216_ = lean_obj_tag_nat(v___x_215_);
lean_dec(v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorIdx___impl___boxed(lean_object* v_x_217_){
_start:
{
uint8_t v_x_4__boxed_218_; lean_object* v_res_219_; 
v_x_4__boxed_218_ = lean_unbox(v_x_217_);
v_res_219_ = l_Lean_Meta_Hint_DiffGranularity_ctorIdx___impl(v_x_4__boxed_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim___redArg(lean_object* v_k_220_){
_start:
{
lean_inc(v_k_220_);
return v_k_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim___redArg___boxed(lean_object* v_k_221_){
_start:
{
lean_object* v_res_222_; 
v_res_222_ = l_Lean_Meta_Hint_DiffGranularity_ctorElim___redArg(v_k_221_);
lean_dec(v_k_221_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim(lean_object* v_motive_223_, lean_object* v_ctorIdx_224_, uint8_t v_t_225_, lean_object* v_h_226_, lean_object* v_k_227_){
_start:
{
lean_inc(v_k_227_);
return v_k_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim___boxed(lean_object* v_motive_228_, lean_object* v_ctorIdx_229_, lean_object* v_t_230_, lean_object* v_h_231_, lean_object* v_k_232_){
_start:
{
uint8_t v_t_boxed_233_; lean_object* v_res_234_; 
v_t_boxed_233_ = lean_unbox(v_t_230_);
v_res_234_ = l_Lean_Meta_Hint_DiffGranularity_ctorElim(v_motive_228_, v_ctorIdx_229_, v_t_boxed_233_, v_h_231_, v_k_232_);
lean_dec(v_k_232_);
lean_dec(v_ctorIdx_229_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim___redArg(lean_object* v_auto_235_){
_start:
{
lean_inc(v_auto_235_);
return v_auto_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim___redArg___boxed(lean_object* v_auto_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l_Lean_Meta_Hint_DiffGranularity_auto_elim___redArg(v_auto_236_);
lean_dec(v_auto_236_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim(lean_object* v_motive_238_, uint8_t v_t_239_, lean_object* v_h_240_, lean_object* v_auto_241_){
_start:
{
lean_inc(v_auto_241_);
return v_auto_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim___boxed(lean_object* v_motive_242_, lean_object* v_t_243_, lean_object* v_h_244_, lean_object* v_auto_245_){
_start:
{
uint8_t v_t_boxed_246_; lean_object* v_res_247_; 
v_t_boxed_246_ = lean_unbox(v_t_243_);
v_res_247_ = l_Lean_Meta_Hint_DiffGranularity_auto_elim(v_motive_242_, v_t_boxed_246_, v_h_244_, v_auto_245_);
lean_dec(v_auto_245_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim___redArg(lean_object* v_char_248_){
_start:
{
lean_inc(v_char_248_);
return v_char_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim___redArg___boxed(lean_object* v_char_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Lean_Meta_Hint_DiffGranularity_char_elim___redArg(v_char_249_);
lean_dec(v_char_249_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim(lean_object* v_motive_251_, uint8_t v_t_252_, lean_object* v_h_253_, lean_object* v_char_254_){
_start:
{
lean_inc(v_char_254_);
return v_char_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim___boxed(lean_object* v_motive_255_, lean_object* v_t_256_, lean_object* v_h_257_, lean_object* v_char_258_){
_start:
{
uint8_t v_t_boxed_259_; lean_object* v_res_260_; 
v_t_boxed_259_ = lean_unbox(v_t_256_);
v_res_260_ = l_Lean_Meta_Hint_DiffGranularity_char_elim(v_motive_255_, v_t_boxed_259_, v_h_257_, v_char_258_);
lean_dec(v_char_258_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim___redArg(lean_object* v_word_261_){
_start:
{
lean_inc(v_word_261_);
return v_word_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim___redArg___boxed(lean_object* v_word_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_Meta_Hint_DiffGranularity_word_elim___redArg(v_word_262_);
lean_dec(v_word_262_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim(lean_object* v_motive_264_, uint8_t v_t_265_, lean_object* v_h_266_, lean_object* v_word_267_){
_start:
{
lean_inc(v_word_267_);
return v_word_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim___boxed(lean_object* v_motive_268_, lean_object* v_t_269_, lean_object* v_h_270_, lean_object* v_word_271_){
_start:
{
uint8_t v_t_boxed_272_; lean_object* v_res_273_; 
v_t_boxed_272_ = lean_unbox(v_t_269_);
v_res_273_ = l_Lean_Meta_Hint_DiffGranularity_word_elim(v_motive_268_, v_t_boxed_272_, v_h_270_, v_word_271_);
lean_dec(v_word_271_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim___redArg(lean_object* v_all_274_){
_start:
{
lean_inc(v_all_274_);
return v_all_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim___redArg___boxed(lean_object* v_all_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Meta_Hint_DiffGranularity_all_elim___redArg(v_all_275_);
lean_dec(v_all_275_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim(lean_object* v_motive_277_, uint8_t v_t_278_, lean_object* v_h_279_, lean_object* v_all_280_){
_start:
{
lean_inc(v_all_280_);
return v_all_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim___boxed(lean_object* v_motive_281_, lean_object* v_t_282_, lean_object* v_h_283_, lean_object* v_all_284_){
_start:
{
uint8_t v_t_boxed_285_; lean_object* v_res_286_; 
v_t_boxed_285_ = lean_unbox(v_t_282_);
v_res_286_ = l_Lean_Meta_Hint_DiffGranularity_all_elim(v_motive_281_, v_t_boxed_285_, v_h_283_, v_all_284_);
lean_dec(v_all_284_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim___redArg(lean_object* v_none_287_){
_start:
{
lean_inc(v_none_287_);
return v_none_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim___redArg___boxed(lean_object* v_none_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Meta_Hint_DiffGranularity_none_elim___redArg(v_none_288_);
lean_dec(v_none_288_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim(lean_object* v_motive_290_, uint8_t v_t_291_, lean_object* v_h_292_, lean_object* v_none_293_){
_start:
{
lean_inc(v_none_293_);
return v_none_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim___boxed(lean_object* v_motive_294_, lean_object* v_t_295_, lean_object* v_h_296_, lean_object* v_none_297_){
_start:
{
uint8_t v_t_boxed_298_; lean_object* v_res_299_; 
v_t_boxed_298_ = lean_unbox(v_t_295_);
v_res_299_ = l_Lean_Meta_Hint_DiffGranularity_none_elim(v_motive_294_, v_t_boxed_298_, v_h_296_, v_none_297_);
lean_dec(v_none_297_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_instCoeSuggestionTextSuggestion___lam__0(lean_object* v_t_300_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; lean_object* v___x_304_; 
v___x_301_ = lean_box(0);
v___x_302_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_302_, 0, v_t_300_);
lean_ctor_set(v___x_302_, 1, v___x_301_);
lean_ctor_set(v___x_302_, 2, v___x_301_);
lean_ctor_set(v___x_302_, 3, v___x_301_);
lean_ctor_set(v___x_302_, 4, v___x_301_);
lean_ctor_set(v___x_302_, 5, v___x_301_);
v___x_303_ = 0;
v___x_304_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_304_, 0, v___x_302_);
lean_ctor_set(v___x_304_, 1, v___x_301_);
lean_ctor_set(v___x_304_, 2, v___x_301_);
lean_ctor_set_uint8(v___x_304_, sizeof(void*)*3, v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_instToMessageDataSuggestion___lam__0(lean_object* v_s_307_){
_start:
{
lean_object* v_toTryThisSuggestion_308_; lean_object* v_messageData_x3f_309_; 
v_toTryThisSuggestion_308_ = lean_ctor_get(v_s_307_, 0);
lean_inc_ref(v_toTryThisSuggestion_308_);
lean_dec_ref(v_s_307_);
v_messageData_x3f_309_ = lean_ctor_get(v_toTryThisSuggestion_308_, 4);
if (lean_obj_tag(v_messageData_x3f_309_) == 0)
{
lean_object* v_suggestion_310_; 
v_suggestion_310_ = lean_ctor_get(v_toTryThisSuggestion_308_, 0);
lean_inc_ref(v_suggestion_310_);
lean_dec_ref(v_toTryThisSuggestion_308_);
if (lean_obj_tag(v_suggestion_310_) == 0)
{
lean_object* v_a_311_; lean_object* v___x_312_; 
v_a_311_ = lean_ctor_get(v_suggestion_310_, 1);
lean_inc(v_a_311_);
lean_dec_ref_known(v_suggestion_310_, 2);
v___x_312_ = l_Lean_MessageData_ofSyntax(v_a_311_);
return v___x_312_;
}
else
{
lean_object* v_a_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_321_; 
v_a_313_ = lean_ctor_get(v_suggestion_310_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v_suggestion_310_);
if (v_isSharedCheck_321_ == 0)
{
v___x_315_ = v_suggestion_310_;
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_a_313_);
lean_dec(v_suggestion_310_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_321_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set_tag(v___x_315_, 3);
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_313_);
v___x_318_ = v_reuseFailAlloc_320_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_MessageData_ofFormat(v___x_318_);
return v___x_319_;
}
}
}
}
else
{
lean_object* v_val_322_; 
lean_inc_ref(v_messageData_x3f_309_);
lean_dec_ref(v_toTryThisSuggestion_308_);
v_val_322_ = lean_ctor_get(v_messageData_x3f_309_, 0);
lean_inc(v_val_322_);
lean_dec_ref_known(v_messageData_x3f_309_, 1);
return v_val_322_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(lean_object* v_as_325_, size_t v_i_326_, size_t v_stop_327_, lean_object* v_b_328_){
_start:
{
lean_object* v___y_330_; uint8_t v___x_334_; 
v___x_334_ = lean_usize_dec_eq(v_i_326_, v_stop_327_);
if (v___x_334_ == 0)
{
lean_object* v___x_335_; lean_object* v_fst_336_; lean_object* v_snd_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_374_; 
v___x_335_ = lean_array_uget(v_as_325_, v_i_326_);
v_fst_336_ = lean_ctor_get(v___x_335_, 0);
v_snd_337_ = lean_ctor_get(v___x_335_, 1);
v_isSharedCheck_374_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_374_ == 0)
{
v___x_339_ = v___x_335_;
v_isShared_340_ = v_isSharedCheck_374_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_snd_337_);
lean_inc(v_fst_336_);
lean_dec(v___x_335_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_374_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; 
v___x_341_ = lean_array_get_size(v_b_328_);
v___x_342_ = lean_unsigned_to_nat(0u);
v___x_343_ = lean_nat_dec_eq(v___x_341_, v___x_342_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v_fst_347_; lean_object* v_snd_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_366_; 
lean_del_object(v___x_339_);
v___x_344_ = lean_unsigned_to_nat(1u);
v___x_345_ = lean_nat_sub(v___x_341_, v___x_344_);
v___x_346_ = lean_array_fget(v_b_328_, v___x_345_);
v_fst_347_ = lean_ctor_get(v___x_346_, 0);
v_snd_348_ = lean_ctor_get(v___x_346_, 1);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_366_ == 0)
{
v___x_350_ = v___x_346_;
v_isShared_351_ = v_isSharedCheck_366_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_snd_348_);
lean_inc(v_fst_347_);
lean_dec(v___x_346_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_366_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
uint8_t v___x_352_; uint8_t v___x_353_; uint8_t v___x_354_; 
v___x_352_ = lean_unbox(v_fst_336_);
v___x_353_ = lean_unbox(v_fst_347_);
lean_dec(v_fst_347_);
v___x_354_ = l_Lean_Diff_instBEqAction_beq(v___x_352_, v___x_353_);
if (v___x_354_ == 0)
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_358_; 
lean_dec(v_snd_348_);
lean_dec(v___x_345_);
v___x_355_ = lean_mk_empty_array_with_capacity(v___x_344_);
v___x_356_ = lean_array_push(v___x_355_, v_snd_337_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 1, v___x_356_);
lean_ctor_set(v___x_350_, 0, v_fst_336_);
v___x_358_ = v___x_350_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_fst_336_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v___x_356_);
v___x_358_ = v_reuseFailAlloc_360_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_359_; 
v___x_359_ = lean_array_push(v_b_328_, v___x_358_);
v___y_330_ = v___x_359_;
goto v___jp_329_;
}
}
else
{
lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_361_ = lean_array_push(v_snd_348_, v_snd_337_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 1, v___x_361_);
lean_ctor_set(v___x_350_, 0, v_fst_336_);
v___x_363_ = v___x_350_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_fst_336_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v___x_361_);
v___x_363_ = v_reuseFailAlloc_365_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_364_; 
v___x_364_ = lean_array_fset(v_b_328_, v___x_345_, v___x_363_);
lean_dec(v___x_345_);
v___y_330_ = v___x_364_;
goto v___jp_329_;
}
}
}
}
else
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_371_; 
lean_dec_ref(v_b_328_);
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = lean_mk_empty_array_with_capacity(v___x_367_);
lean_inc_ref(v___x_368_);
v___x_369_ = lean_array_push(v___x_368_, v_snd_337_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 1, v___x_369_);
v___x_371_ = v___x_339_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_fst_336_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v___x_369_);
v___x_371_ = v_reuseFailAlloc_373_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
lean_object* v___x_372_; 
v___x_372_ = lean_array_push(v___x_368_, v___x_371_);
v___y_330_ = v___x_372_;
goto v___jp_329_;
}
}
}
}
else
{
return v_b_328_;
}
v___jp_329_:
{
size_t v___x_331_; size_t v___x_332_; 
v___x_331_ = ((size_t)1ULL);
v___x_332_ = lean_usize_add(v_i_326_, v___x_331_);
v_i_326_ = v___x_332_;
v_b_328_ = v___y_330_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg___boxed(lean_object* v_as_375_, lean_object* v_i_376_, lean_object* v_stop_377_, lean_object* v_b_378_){
_start:
{
size_t v_i_boxed_379_; size_t v_stop_boxed_380_; lean_object* v_res_381_; 
v_i_boxed_379_ = lean_unbox_usize(v_i_376_);
lean_dec(v_i_376_);
v_stop_boxed_380_ = lean_unbox_usize(v_stop_377_);
lean_dec(v_stop_377_);
v_res_381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_as_375_, v_i_boxed_379_, v_stop_boxed_380_, v_b_378_);
lean_dec_ref(v_as_375_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(lean_object* v_ds_384_){
_start:
{
lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v___x_385_ = lean_unsigned_to_nat(0u);
v___x_386_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg___closed__0));
v___x_387_ = lean_array_get_size(v_ds_384_);
v___x_388_ = lean_nat_dec_lt(v___x_385_, v___x_387_);
if (v___x_388_ == 0)
{
return v___x_386_;
}
else
{
size_t v___x_389_; size_t v___x_390_; lean_object* v___x_391_; 
v___x_389_ = ((size_t)0ULL);
v___x_390_ = lean_usize_of_nat(v___x_387_);
v___x_391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_ds_384_, v___x_389_, v___x_390_, v___x_386_);
return v___x_391_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg___boxed(lean_object* v_ds_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_ds_392_);
lean_dec_ref(v_ds_392_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits(lean_object* v_00_u03b1_394_, lean_object* v_ds_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_ds_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___boxed(lean_object* v_00_u03b1_397_, lean_object* v_ds_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits(v_00_u03b1_397_, v_ds_398_);
lean_dec_ref(v_ds_398_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0(lean_object* v_00_u03b1_400_, lean_object* v_as_401_, size_t v_i_402_, size_t v_stop_403_, lean_object* v_b_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_as_401_, v_i_402_, v_stop_403_, v_b_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___boxed(lean_object* v_00_u03b1_406_, lean_object* v_as_407_, lean_object* v_i_408_, lean_object* v_stop_409_, lean_object* v_b_410_){
_start:
{
size_t v_i_boxed_411_; size_t v_stop_boxed_412_; lean_object* v_res_413_; 
v_i_boxed_411_ = lean_unbox_usize(v_i_408_);
lean_dec(v_i_408_);
v_stop_boxed_412_ = lean_unbox_usize(v_stop_409_);
lean_dec(v_stop_409_);
v_res_413_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0(v_00_u03b1_406_, v_as_407_, v_i_boxed_411_, v_stop_boxed_412_, v_b_410_);
lean_dec_ref(v_as_407_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(size_t v_sz_414_, size_t v_i_415_, lean_object* v_bs_416_){
_start:
{
uint8_t v___x_417_; 
v___x_417_ = lean_usize_dec_lt(v_i_415_, v_sz_414_);
if (v___x_417_ == 0)
{
return v_bs_416_;
}
else
{
lean_object* v_v_418_; lean_object* v_fst_419_; lean_object* v_snd_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_435_; 
v_v_418_ = lean_array_uget(v_bs_416_, v_i_415_);
v_fst_419_ = lean_ctor_get(v_v_418_, 0);
v_snd_420_ = lean_ctor_get(v_v_418_, 1);
v_isSharedCheck_435_ = !lean_is_exclusive(v_v_418_);
if (v_isSharedCheck_435_ == 0)
{
v___x_422_ = v_v_418_;
v_isShared_423_ = v_isSharedCheck_435_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_snd_420_);
lean_inc(v_fst_419_);
lean_dec(v_v_418_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_435_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v_bs_x27_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_424_ = lean_unsigned_to_nat(0u);
v_bs_x27_425_ = lean_array_uset(v_bs_416_, v_i_415_, v___x_424_);
v___x_426_ = lean_array_to_list(v_snd_420_);
v___x_427_ = lean_string_mk(v___x_426_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 1, v___x_427_);
v___x_429_ = v___x_422_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_fst_419_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v___x_427_);
v___x_429_ = v_reuseFailAlloc_434_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
size_t v___x_430_; size_t v___x_431_; lean_object* v___x_432_; 
v___x_430_ = ((size_t)1ULL);
v___x_431_ = lean_usize_add(v_i_415_, v___x_430_);
v___x_432_ = lean_array_uset(v_bs_x27_425_, v_i_415_, v___x_429_);
v_i_415_ = v___x_431_;
v_bs_416_ = v___x_432_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0___boxed(lean_object* v_sz_436_, lean_object* v_i_437_, lean_object* v_bs_438_){
_start:
{
size_t v_sz_boxed_439_; size_t v_i_boxed_440_; lean_object* v_res_441_; 
v_sz_boxed_439_ = lean_unbox_usize(v_sz_436_);
lean_dec(v_sz_436_);
v_i_boxed_440_ = lean_unbox_usize(v_i_437_);
lean_dec(v_i_437_);
v_res_441_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_boxed_439_, v_i_boxed_440_, v_bs_438_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(lean_object* v_d_442_){
_start:
{
lean_object* v___x_443_; size_t v_sz_444_; size_t v___x_445_; lean_object* v___x_446_; 
v___x_443_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_d_442_);
v_sz_444_ = lean_array_size(v___x_443_);
v___x_445_ = ((size_t)0ULL);
v___x_446_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_444_, v___x_445_, v___x_443_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff___boxed(lean_object* v_d_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v_d_447_);
lean_dec_ref(v_d_447_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(size_t v_sz_449_, size_t v_i_450_, lean_object* v_bs_451_){
_start:
{
uint8_t v___x_452_; 
v___x_452_ = lean_usize_dec_lt(v_i_450_, v_sz_449_);
if (v___x_452_ == 0)
{
return v_bs_451_;
}
else
{
lean_object* v_v_453_; lean_object* v___x_454_; lean_object* v_bs_x27_455_; uint8_t v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; size_t v___x_459_; size_t v___x_460_; lean_object* v___x_461_; 
v_v_453_ = lean_array_uget(v_bs_451_, v_i_450_);
v___x_454_ = lean_unsigned_to_nat(0u);
v_bs_x27_455_ = lean_array_uset(v_bs_451_, v_i_450_, v___x_454_);
v___x_456_ = 0;
v___x_457_ = lean_box(v___x_456_);
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v_v_453_);
v___x_459_ = ((size_t)1ULL);
v___x_460_ = lean_usize_add(v_i_450_, v___x_459_);
v___x_461_ = lean_array_uset(v_bs_x27_455_, v_i_450_, v___x_458_);
v_i_450_ = v___x_460_;
v_bs_451_ = v___x_461_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9___boxed(lean_object* v_sz_463_, lean_object* v_i_464_, lean_object* v_bs_465_){
_start:
{
size_t v_sz_boxed_466_; size_t v_i_boxed_467_; lean_object* v_res_468_; 
v_sz_boxed_466_ = lean_unbox_usize(v_sz_463_);
lean_dec(v_sz_463_);
v_i_boxed_467_ = lean_unbox_usize(v_i_464_);
lean_dec(v_i_464_);
v_res_468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(v_sz_boxed_466_, v_i_boxed_467_, v_bs_465_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(lean_object* v___x_469_, lean_object* v_original_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_fst_472_; lean_object* v_snd_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_492_; 
v_fst_472_ = lean_ctor_get(v_a_471_, 0);
v_snd_473_ = lean_ctor_get(v_a_471_, 1);
v_isSharedCheck_492_ = !lean_is_exclusive(v_a_471_);
if (v_isSharedCheck_492_ == 0)
{
v___x_475_ = v_a_471_;
v_isShared_476_ = v_isSharedCheck_492_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_snd_473_);
lean_inc(v_fst_472_);
lean_dec(v_a_471_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_492_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
uint8_t v___x_477_; 
v___x_477_ = lean_nat_dec_lt(v_snd_473_, v___x_469_);
if (v___x_477_ == 0)
{
lean_object* v___x_479_; 
if (v_isShared_476_ == 0)
{
v___x_479_ = v___x_475_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_fst_472_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_snd_473_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
else
{
uint8_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_481_ = 1;
v___x_482_ = lean_array_fget_borrowed(v_original_470_, v_snd_473_);
v___x_483_ = lean_box(v___x_481_);
lean_inc(v___x_482_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 1, v___x_482_);
lean_ctor_set(v___x_475_, 0, v___x_483_);
v___x_485_ = v___x_475_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v___x_482_);
v___x_485_ = v_reuseFailAlloc_491_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_486_ = lean_array_push(v_fst_472_, v___x_485_);
v___x_487_ = lean_unsigned_to_nat(1u);
v___x_488_ = lean_nat_add(v_snd_473_, v___x_487_);
lean_dec(v_snd_473_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_486_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v_a_471_ = v___x_489_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg___boxed(lean_object* v___x_493_, lean_object* v_original_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_493_, v_original_494_, v_a_495_);
lean_dec_ref(v_original_494_);
lean_dec(v___x_493_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg(uint32_t v_a_497_, lean_object* v_x_498_){
_start:
{
if (lean_obj_tag(v_x_498_) == 0)
{
lean_object* v___x_499_; 
v___x_499_ = lean_box(0);
return v___x_499_;
}
else
{
lean_object* v_key_500_; lean_object* v_value_501_; lean_object* v_tail_502_; uint32_t v___x_503_; uint8_t v___x_504_; 
v_key_500_ = lean_ctor_get(v_x_498_, 0);
v_value_501_ = lean_ctor_get(v_x_498_, 1);
v_tail_502_ = lean_ctor_get(v_x_498_, 2);
v___x_503_ = lean_unbox_uint32(v_key_500_);
v___x_504_ = lean_uint32_dec_eq(v___x_503_, v_a_497_);
if (v___x_504_ == 0)
{
v_x_498_ = v_tail_502_;
goto _start;
}
else
{
lean_object* v___x_506_; 
lean_inc(v_value_501_);
v___x_506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_506_, 0, v_value_501_);
return v___x_506_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg___boxed(lean_object* v_a_507_, lean_object* v_x_508_){
_start:
{
uint32_t v_a_boxed_509_; lean_object* v_res_510_; 
v_a_boxed_509_ = lean_unbox_uint32(v_a_507_);
lean_dec(v_a_507_);
v_res_510_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg(v_a_boxed_509_, v_x_508_);
lean_dec(v_x_508_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(lean_object* v_m_511_, uint32_t v_a_512_){
_start:
{
lean_object* v_buckets_513_; lean_object* v___x_514_; uint64_t v___x_515_; uint64_t v___x_516_; uint64_t v___x_517_; uint64_t v_fold_518_; uint64_t v___x_519_; uint64_t v___x_520_; uint64_t v___x_521_; size_t v___x_522_; size_t v___x_523_; size_t v___x_524_; size_t v___x_525_; size_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v_buckets_513_ = lean_ctor_get(v_m_511_, 1);
v___x_514_ = lean_array_get_size(v_buckets_513_);
v___x_515_ = lean_uint32_to_uint64(v_a_512_);
v___x_516_ = 32ULL;
v___x_517_ = lean_uint64_shift_right(v___x_515_, v___x_516_);
v_fold_518_ = lean_uint64_xor(v___x_515_, v___x_517_);
v___x_519_ = 16ULL;
v___x_520_ = lean_uint64_shift_right(v_fold_518_, v___x_519_);
v___x_521_ = lean_uint64_xor(v_fold_518_, v___x_520_);
v___x_522_ = lean_uint64_to_usize(v___x_521_);
v___x_523_ = lean_usize_of_nat(v___x_514_);
v___x_524_ = ((size_t)1ULL);
v___x_525_ = lean_usize_sub(v___x_523_, v___x_524_);
v___x_526_ = lean_usize_land(v___x_522_, v___x_525_);
v___x_527_ = lean_array_uget_borrowed(v_buckets_513_, v___x_526_);
v___x_528_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg(v_a_512_, v___x_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg___boxed(lean_object* v_m_529_, lean_object* v_a_530_){
_start:
{
uint32_t v_a_boxed_531_; lean_object* v_res_532_; 
v_a_boxed_531_ = lean_unbox_uint32(v_a_530_);
lean_dec(v_a_530_);
v_res_532_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_m_529_, v_a_boxed_531_);
lean_dec_ref(v_m_529_);
return v_res_532_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(uint32_t v_a_533_, lean_object* v_x_534_){
_start:
{
if (lean_obj_tag(v_x_534_) == 0)
{
uint8_t v___x_535_; 
v___x_535_ = 0;
return v___x_535_;
}
else
{
lean_object* v_key_536_; lean_object* v_tail_537_; uint32_t v___x_538_; uint8_t v___x_539_; 
v_key_536_ = lean_ctor_get(v_x_534_, 0);
v_tail_537_ = lean_ctor_get(v_x_534_, 2);
v___x_538_ = lean_unbox_uint32(v_key_536_);
v___x_539_ = lean_uint32_dec_eq(v___x_538_, v_a_533_);
if (v___x_539_ == 0)
{
v_x_534_ = v_tail_537_;
goto _start;
}
else
{
return v___x_539_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg___boxed(lean_object* v_a_541_, lean_object* v_x_542_){
_start:
{
uint32_t v_a_boxed_543_; uint8_t v_res_544_; lean_object* v_r_545_; 
v_a_boxed_543_ = lean_unbox_uint32(v_a_541_);
lean_dec(v_a_541_);
v_res_544_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(v_a_boxed_543_, v_x_542_);
lean_dec(v_x_542_);
v_r_545_ = lean_box(v_res_544_);
return v_r_545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(uint32_t v_a_546_, lean_object* v_b_547_, lean_object* v_x_548_){
_start:
{
if (lean_obj_tag(v_x_548_) == 0)
{
lean_dec(v_b_547_);
return v_x_548_;
}
else
{
lean_object* v_key_549_; lean_object* v_value_550_; lean_object* v_tail_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_565_; 
v_key_549_ = lean_ctor_get(v_x_548_, 0);
v_value_550_ = lean_ctor_get(v_x_548_, 1);
v_tail_551_ = lean_ctor_get(v_x_548_, 2);
v_isSharedCheck_565_ = !lean_is_exclusive(v_x_548_);
if (v_isSharedCheck_565_ == 0)
{
v___x_553_ = v_x_548_;
v_isShared_554_ = v_isSharedCheck_565_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_tail_551_);
lean_inc(v_value_550_);
lean_inc(v_key_549_);
lean_dec(v_x_548_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_565_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
uint32_t v___x_555_; uint8_t v___x_556_; 
v___x_555_ = lean_unbox_uint32(v_key_549_);
v___x_556_ = lean_uint32_dec_eq(v___x_555_, v_a_546_);
if (v___x_556_ == 0)
{
lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_557_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(v_a_546_, v_b_547_, v_tail_551_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 2, v___x_557_);
v___x_559_ = v___x_553_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v_key_549_);
lean_ctor_set(v_reuseFailAlloc_560_, 1, v_value_550_);
lean_ctor_set(v_reuseFailAlloc_560_, 2, v___x_557_);
v___x_559_ = v_reuseFailAlloc_560_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
return v___x_559_;
}
}
else
{
lean_object* v___x_561_; lean_object* v___x_563_; 
lean_dec(v_value_550_);
lean_dec(v_key_549_);
v___x_561_ = lean_box_uint32(v_a_546_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 1, v_b_547_);
lean_ctor_set(v___x_553_, 0, v___x_561_);
v___x_563_ = v___x_553_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_b_547_);
lean_ctor_set(v_reuseFailAlloc_564_, 2, v_tail_551_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg___boxed(lean_object* v_a_566_, lean_object* v_b_567_, lean_object* v_x_568_){
_start:
{
uint32_t v_a_boxed_569_; lean_object* v_res_570_; 
v_a_boxed_569_ = lean_unbox_uint32(v_a_566_);
lean_dec(v_a_566_);
v_res_570_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(v_a_boxed_569_, v_b_567_, v_x_568_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29___redArg(lean_object* v_x_571_, lean_object* v_x_572_){
_start:
{
if (lean_obj_tag(v_x_572_) == 0)
{
return v_x_571_;
}
else
{
lean_object* v_key_573_; lean_object* v_value_574_; lean_object* v_tail_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_599_; 
v_key_573_ = lean_ctor_get(v_x_572_, 0);
v_value_574_ = lean_ctor_get(v_x_572_, 1);
v_tail_575_ = lean_ctor_get(v_x_572_, 2);
v_isSharedCheck_599_ = !lean_is_exclusive(v_x_572_);
if (v_isSharedCheck_599_ == 0)
{
v___x_577_ = v_x_572_;
v_isShared_578_ = v_isSharedCheck_599_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_tail_575_);
lean_inc(v_value_574_);
lean_inc(v_key_573_);
lean_dec(v_x_572_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_599_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; uint32_t v___x_580_; uint64_t v___x_581_; uint64_t v___x_582_; uint64_t v___x_583_; uint64_t v_fold_584_; uint64_t v___x_585_; uint64_t v___x_586_; uint64_t v___x_587_; size_t v___x_588_; size_t v___x_589_; size_t v___x_590_; size_t v___x_591_; size_t v___x_592_; lean_object* v___x_593_; lean_object* v___x_595_; 
v___x_579_ = lean_array_get_size(v_x_571_);
v___x_580_ = lean_unbox_uint32(v_key_573_);
v___x_581_ = lean_uint32_to_uint64(v___x_580_);
v___x_582_ = 32ULL;
v___x_583_ = lean_uint64_shift_right(v___x_581_, v___x_582_);
v_fold_584_ = lean_uint64_xor(v___x_581_, v___x_583_);
v___x_585_ = 16ULL;
v___x_586_ = lean_uint64_shift_right(v_fold_584_, v___x_585_);
v___x_587_ = lean_uint64_xor(v_fold_584_, v___x_586_);
v___x_588_ = lean_uint64_to_usize(v___x_587_);
v___x_589_ = lean_usize_of_nat(v___x_579_);
v___x_590_ = ((size_t)1ULL);
v___x_591_ = lean_usize_sub(v___x_589_, v___x_590_);
v___x_592_ = lean_usize_land(v___x_588_, v___x_591_);
v___x_593_ = lean_array_uget_borrowed(v_x_571_, v___x_592_);
lean_inc(v___x_593_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 2, v___x_593_);
v___x_595_ = v___x_577_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_key_573_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_value_574_);
lean_ctor_set(v_reuseFailAlloc_598_, 2, v___x_593_);
v___x_595_ = v_reuseFailAlloc_598_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; 
v___x_596_ = lean_array_uset(v_x_571_, v___x_592_, v___x_595_);
v_x_571_ = v___x_596_;
v_x_572_ = v_tail_575_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28___redArg(lean_object* v_i_600_, lean_object* v_source_601_, lean_object* v_target_602_){
_start:
{
lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_603_ = lean_array_get_size(v_source_601_);
v___x_604_ = lean_nat_dec_lt(v_i_600_, v___x_603_);
if (v___x_604_ == 0)
{
lean_dec_ref(v_source_601_);
lean_dec(v_i_600_);
return v_target_602_;
}
else
{
lean_object* v_es_605_; lean_object* v___x_606_; lean_object* v_source_607_; lean_object* v_target_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v_es_605_ = lean_array_fget(v_source_601_, v_i_600_);
v___x_606_ = lean_box(0);
v_source_607_ = lean_array_fset(v_source_601_, v_i_600_, v___x_606_);
v_target_608_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29___redArg(v_target_602_, v_es_605_);
v___x_609_ = lean_unsigned_to_nat(1u);
v___x_610_ = lean_nat_add(v_i_600_, v___x_609_);
lean_dec(v_i_600_);
v_i_600_ = v___x_610_;
v_source_601_ = v_source_607_;
v_target_602_ = v_target_608_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23___redArg(lean_object* v_data_612_){
_start:
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v_nbuckets_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_613_ = lean_array_get_size(v_data_612_);
v___x_614_ = lean_unsigned_to_nat(2u);
v_nbuckets_615_ = lean_nat_mul(v___x_613_, v___x_614_);
v___x_616_ = lean_unsigned_to_nat(0u);
v___x_617_ = lean_box(0);
v___x_618_ = lean_mk_array(v_nbuckets_615_, v___x_617_);
v___x_619_ = lean_array_propagate_mark(v_data_612_, v___x_618_);
v___x_620_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28___redArg(v___x_616_, v_data_612_, v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(lean_object* v_m_621_, uint32_t v_a_622_, lean_object* v_b_623_){
_start:
{
lean_object* v_size_624_; lean_object* v_buckets_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_669_; 
v_size_624_ = lean_ctor_get(v_m_621_, 0);
v_buckets_625_ = lean_ctor_get(v_m_621_, 1);
v_isSharedCheck_669_ = !lean_is_exclusive(v_m_621_);
if (v_isSharedCheck_669_ == 0)
{
v___x_627_ = v_m_621_;
v_isShared_628_ = v_isSharedCheck_669_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_buckets_625_);
lean_inc(v_size_624_);
lean_dec(v_m_621_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_669_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; uint64_t v___x_630_; uint64_t v___x_631_; uint64_t v___x_632_; uint64_t v_fold_633_; uint64_t v___x_634_; uint64_t v___x_635_; uint64_t v___x_636_; size_t v___x_637_; size_t v___x_638_; size_t v___x_639_; size_t v___x_640_; size_t v___x_641_; lean_object* v_bkt_642_; uint8_t v___x_643_; 
v___x_629_ = lean_array_get_size(v_buckets_625_);
v___x_630_ = lean_uint32_to_uint64(v_a_622_);
v___x_631_ = 32ULL;
v___x_632_ = lean_uint64_shift_right(v___x_630_, v___x_631_);
v_fold_633_ = lean_uint64_xor(v___x_630_, v___x_632_);
v___x_634_ = 16ULL;
v___x_635_ = lean_uint64_shift_right(v_fold_633_, v___x_634_);
v___x_636_ = lean_uint64_xor(v_fold_633_, v___x_635_);
v___x_637_ = lean_uint64_to_usize(v___x_636_);
v___x_638_ = lean_usize_of_nat(v___x_629_);
v___x_639_ = ((size_t)1ULL);
v___x_640_ = lean_usize_sub(v___x_638_, v___x_639_);
v___x_641_ = lean_usize_land(v___x_637_, v___x_640_);
v_bkt_642_ = lean_array_uget_borrowed(v_buckets_625_, v___x_641_);
v___x_643_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(v_a_622_, v_bkt_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; lean_object* v_size_x27_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v_buckets_x27_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v___x_644_ = lean_unsigned_to_nat(1u);
v_size_x27_645_ = lean_nat_add(v_size_624_, v___x_644_);
lean_dec(v_size_624_);
v___x_646_ = lean_box_uint32(v_a_622_);
lean_inc(v_bkt_642_);
v___x_647_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_647_, 0, v___x_646_);
lean_ctor_set(v___x_647_, 1, v_b_623_);
lean_ctor_set(v___x_647_, 2, v_bkt_642_);
v_buckets_x27_648_ = lean_array_uset(v_buckets_625_, v___x_641_, v___x_647_);
v___x_649_ = lean_unsigned_to_nat(4u);
v___x_650_ = lean_nat_mul(v_size_x27_645_, v___x_649_);
v___x_651_ = lean_unsigned_to_nat(3u);
v___x_652_ = lean_nat_div(v___x_650_, v___x_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_array_get_size(v_buckets_x27_648_);
v___x_654_ = lean_nat_dec_le(v___x_652_, v___x_653_);
lean_dec(v___x_652_);
if (v___x_654_ == 0)
{
lean_object* v_val_655_; lean_object* v___x_657_; 
v_val_655_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23___redArg(v_buckets_x27_648_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v_val_655_);
lean_ctor_set(v___x_627_, 0, v_size_x27_645_);
v___x_657_ = v___x_627_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_size_x27_645_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_val_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
else
{
lean_object* v___x_660_; 
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v_buckets_x27_648_);
lean_ctor_set(v___x_627_, 0, v_size_x27_645_);
v___x_660_ = v___x_627_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_661_; 
v_reuseFailAlloc_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_661_, 0, v_size_x27_645_);
lean_ctor_set(v_reuseFailAlloc_661_, 1, v_buckets_x27_648_);
v___x_660_ = v_reuseFailAlloc_661_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
return v___x_660_;
}
}
}
else
{
lean_object* v___x_662_; lean_object* v_buckets_x27_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
lean_inc(v_bkt_642_);
v___x_662_ = lean_box(0);
v_buckets_x27_663_ = lean_array_uset(v_buckets_625_, v___x_641_, v___x_662_);
v___x_664_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(v_a_622_, v_b_623_, v_bkt_642_);
v___x_665_ = lean_array_uset(v_buckets_x27_663_, v___x_641_, v___x_664_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 1, v___x_665_);
v___x_667_ = v___x_627_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_size_624_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg___boxed(lean_object* v_m_670_, lean_object* v_a_671_, lean_object* v_b_672_){
_start:
{
uint32_t v_a_boxed_673_; lean_object* v_res_674_; 
v_a_boxed_673_ = lean_unbox_uint32(v_a_671_);
lean_dec(v_a_671_);
v_res_674_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_m_670_, v_a_boxed_673_, v_b_672_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(lean_object* v_histogram_675_, lean_object* v_index_676_, uint32_t v_val_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_histogram_675_, v_val_677_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = lean_box(0);
v___x_681_ = lean_unsigned_to_nat(1u);
v___x_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_682_, 0, v_index_676_);
v___x_683_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_683_, 0, v___x_679_);
lean_ctor_set(v___x_683_, 1, v___x_680_);
lean_ctor_set(v___x_683_, 2, v___x_681_);
lean_ctor_set(v___x_683_, 3, v___x_682_);
v___x_684_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_675_, v_val_677_, v___x_683_);
return v___x_684_;
}
else
{
lean_object* v_val_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_706_; 
v_val_685_ = lean_ctor_get(v___x_678_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v___x_678_);
if (v_isSharedCheck_706_ == 0)
{
v___x_687_ = v___x_678_;
v_isShared_688_ = v_isSharedCheck_706_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_val_685_);
lean_dec(v___x_678_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_706_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v_leftCount_689_; lean_object* v_leftIndex_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_703_; 
v_leftCount_689_ = lean_ctor_get(v_val_685_, 0);
v_leftIndex_690_ = lean_ctor_get(v_val_685_, 1);
v_isSharedCheck_703_ = !lean_is_exclusive(v_val_685_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; lean_object* v_unused_705_; 
v_unused_704_ = lean_ctor_get(v_val_685_, 3);
lean_dec(v_unused_704_);
v_unused_705_ = lean_ctor_get(v_val_685_, 2);
lean_dec(v_unused_705_);
v___x_692_ = v_val_685_;
v_isShared_693_ = v_isSharedCheck_703_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_leftIndex_690_);
lean_inc(v_leftCount_689_);
lean_dec(v_val_685_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_703_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_697_; 
v___x_694_ = lean_unsigned_to_nat(1u);
v___x_695_ = lean_nat_add(v_leftCount_689_, v___x_694_);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v_index_676_);
v___x_697_ = v___x_687_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_index_676_);
v___x_697_ = v_reuseFailAlloc_702_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_699_; 
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 3, v___x_697_);
lean_ctor_set(v___x_692_, 2, v___x_695_);
v___x_699_ = v___x_692_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_leftCount_689_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_leftIndex_690_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v___x_697_);
v___x_699_ = v_reuseFailAlloc_701_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_700_; 
v___x_700_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_675_, v_val_677_, v___x_699_);
return v___x_700_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_histogram_707_, lean_object* v_index_708_, lean_object* v_val_709_){
_start:
{
uint32_t v_val_boxed_710_; lean_object* v_res_711_; 
v_val_boxed_710_ = lean_unbox_uint32(v_val_709_);
lean_dec(v_val_709_);
v_res_711_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(v_histogram_707_, v_index_708_, v_val_boxed_710_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(lean_object* v_upperBound_712_, lean_object* v___x_713_, lean_object* v_fst_714_, lean_object* v___x_715_, lean_object* v_a_716_, lean_object* v_b_717_){
_start:
{
uint8_t v___x_718_; 
v___x_718_ = lean_nat_dec_lt(v_a_716_, v_upperBound_712_);
if (v___x_718_ == 0)
{
lean_dec(v_a_716_);
return v_b_717_;
}
else
{
lean_object* v___x_719_; uint32_t v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_719_ = l_Subarray_get___redArg(v_fst_714_, v_a_716_);
v___x_720_ = lean_unbox_uint32(v___x_719_);
lean_dec(v___x_719_);
lean_inc(v_a_716_);
v___x_721_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(v_b_717_, v_a_716_, v___x_720_);
v___x_722_ = lean_unsigned_to_nat(1u);
v___x_723_ = lean_nat_add(v_a_716_, v___x_722_);
lean_dec(v_a_716_);
v_a_716_ = v___x_723_;
v_b_717_ = v___x_721_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg___boxed(lean_object* v_upperBound_725_, lean_object* v___x_726_, lean_object* v_fst_727_, lean_object* v___x_728_, lean_object* v_a_729_, lean_object* v_b_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(v_upperBound_725_, v___x_726_, v_fst_727_, v___x_728_, v_a_729_, v_b_730_);
lean_dec(v___x_728_);
lean_dec_ref(v_fst_727_);
lean_dec(v___x_726_);
lean_dec(v_upperBound_725_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(lean_object* v_as_x27_732_, lean_object* v_b_733_){
_start:
{
if (lean_obj_tag(v_as_x27_732_) == 0)
{
return v_b_733_;
}
else
{
lean_object* v_head_734_; lean_object* v_snd_735_; lean_object* v_leftIndex_736_; 
v_head_734_ = lean_ctor_get(v_as_x27_732_, 0);
v_snd_735_ = lean_ctor_get(v_head_734_, 1);
v_leftIndex_736_ = lean_ctor_get(v_snd_735_, 1);
if (lean_obj_tag(v_leftIndex_736_) == 1)
{
lean_object* v_rightIndex_737_; 
v_rightIndex_737_ = lean_ctor_get(v_snd_735_, 3);
if (lean_obj_tag(v_rightIndex_737_) == 1)
{
if (lean_obj_tag(v_b_733_) == 0)
{
lean_object* v_tail_738_; lean_object* v_fst_739_; lean_object* v_leftCount_740_; lean_object* v_rightCount_741_; lean_object* v_val_742_; lean_object* v_val_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_tail_738_ = lean_ctor_get(v_as_x27_732_, 1);
v_fst_739_ = lean_ctor_get(v_head_734_, 0);
v_leftCount_740_ = lean_ctor_get(v_snd_735_, 0);
v_rightCount_741_ = lean_ctor_get(v_snd_735_, 2);
v_val_742_ = lean_ctor_get(v_leftIndex_736_, 0);
v_val_743_ = lean_ctor_get(v_rightIndex_737_, 0);
v___x_744_ = lean_nat_add(v_leftCount_740_, v_rightCount_741_);
lean_inc(v_val_743_);
lean_inc(v_val_742_);
v___x_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_745_, 0, v_val_742_);
lean_ctor_set(v___x_745_, 1, v_val_743_);
lean_inc(v_fst_739_);
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v_fst_739_);
lean_ctor_set(v___x_746_, 1, v___x_745_);
v___x_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_744_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
v___x_748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
v_as_x27_732_ = v_tail_738_;
v_b_733_ = v___x_748_;
goto _start;
}
else
{
lean_object* v_val_750_; lean_object* v_tail_751_; lean_object* v_fst_752_; lean_object* v_leftCount_753_; lean_object* v_rightCount_754_; lean_object* v_val_755_; lean_object* v_val_756_; lean_object* v_fst_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_778_; 
v_val_750_ = lean_ctor_get(v_b_733_, 0);
lean_inc(v_val_750_);
v_tail_751_ = lean_ctor_get(v_as_x27_732_, 1);
v_fst_752_ = lean_ctor_get(v_head_734_, 0);
v_leftCount_753_ = lean_ctor_get(v_snd_735_, 0);
v_rightCount_754_ = lean_ctor_get(v_snd_735_, 2);
v_val_755_ = lean_ctor_get(v_leftIndex_736_, 0);
v_val_756_ = lean_ctor_get(v_rightIndex_737_, 0);
v_fst_757_ = lean_ctor_get(v_val_750_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v_val_750_);
if (v_isSharedCheck_778_ == 0)
{
lean_object* v_unused_779_; 
v_unused_779_ = lean_ctor_get(v_val_750_, 1);
lean_dec(v_unused_779_);
v___x_759_ = v_val_750_;
v_isShared_760_ = v_isSharedCheck_778_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_fst_757_);
lean_dec(v_val_750_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_778_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_761_ = lean_nat_add(v_leftCount_753_, v_rightCount_754_);
v___x_762_ = lean_nat_dec_lt(v___x_761_, v_fst_757_);
lean_dec(v_fst_757_);
if (v___x_762_ == 0)
{
lean_dec(v___x_761_);
lean_del_object(v___x_759_);
v_as_x27_732_ = v_tail_751_;
goto _start;
}
else
{
lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_776_; 
v_isSharedCheck_776_ = !lean_is_exclusive(v_b_733_);
if (v_isSharedCheck_776_ == 0)
{
lean_object* v_unused_777_; 
v_unused_777_ = lean_ctor_get(v_b_733_, 0);
lean_dec(v_unused_777_);
v___x_765_ = v_b_733_;
v_isShared_766_ = v_isSharedCheck_776_;
goto v_resetjp_764_;
}
else
{
lean_dec(v_b_733_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_776_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
lean_inc(v_val_756_);
lean_inc(v_val_755_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 1, v_val_756_);
lean_ctor_set(v___x_759_, 0, v_val_755_);
v___x_768_ = v___x_759_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_val_755_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_val_756_);
v___x_768_ = v_reuseFailAlloc_775_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_772_; 
lean_inc(v_fst_752_);
v___x_769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_769_, 0, v_fst_752_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_761_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_770_);
v___x_772_ = v___x_765_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v___x_770_);
v___x_772_ = v_reuseFailAlloc_774_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
v_as_x27_732_ = v_tail_751_;
v_b_733_ = v___x_772_;
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
lean_object* v_tail_780_; 
v_tail_780_ = lean_ctor_get(v_as_x27_732_, 1);
v_as_x27_732_ = v_tail_780_;
goto _start;
}
}
else
{
lean_object* v_tail_782_; 
v_tail_782_ = lean_ctor_get(v_as_x27_732_, 1);
v_as_x27_732_ = v_tail_782_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_as_x27_784_, lean_object* v_b_785_){
_start:
{
lean_object* v_res_786_; 
v_res_786_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(v_as_x27_784_, v_b_785_);
lean_dec(v_as_x27_784_);
return v_res_786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(lean_object* v_a_787_, lean_object* v_b_788_){
_start:
{
lean_object* v_array_789_; lean_object* v_start_790_; lean_object* v_stop_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_804_; 
v_array_789_ = lean_ctor_get(v_a_787_, 0);
v_start_790_ = lean_ctor_get(v_a_787_, 1);
v_stop_791_ = lean_ctor_get(v_a_787_, 2);
v_isSharedCheck_804_ = !lean_is_exclusive(v_a_787_);
if (v_isSharedCheck_804_ == 0)
{
v___x_793_ = v_a_787_;
v_isShared_794_ = v_isSharedCheck_804_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_stop_791_);
lean_inc(v_start_790_);
lean_inc(v_array_789_);
lean_dec(v_a_787_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_804_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
uint8_t v___x_795_; 
v___x_795_ = lean_nat_dec_lt(v_start_790_, v_stop_791_);
if (v___x_795_ == 0)
{
lean_del_object(v___x_793_);
lean_dec(v_stop_791_);
lean_dec(v_start_790_);
lean_dec_ref(v_array_789_);
return v_b_788_;
}
else
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_796_ = lean_unsigned_to_nat(1u);
v___x_797_ = lean_nat_add(v_start_790_, v___x_796_);
lean_inc_ref(v_array_789_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 1, v___x_797_);
v___x_799_ = v___x_793_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_array_789_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v___x_797_);
lean_ctor_set(v_reuseFailAlloc_803_, 2, v_stop_791_);
v___x_799_ = v_reuseFailAlloc_803_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_array_fget(v_array_789_, v_start_790_);
lean_dec(v_start_790_);
lean_dec_ref(v_array_789_);
v___x_801_ = lean_array_push(v_b_788_, v___x_800_);
v_a_787_ = v___x_799_;
v_b_788_ = v___x_801_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8(lean_object* v_left_805_, lean_object* v_right_806_, lean_object* v_i_807_){
_start:
{
lean_object* v_start_808_; lean_object* v_stop_809_; lean_object* v___x_810_; uint8_t v___x_824_; 
v_start_808_ = lean_ctor_get(v_left_805_, 1);
v_stop_809_ = lean_ctor_get(v_left_805_, 2);
v___x_810_ = lean_nat_sub(v_stop_809_, v_start_808_);
v___x_824_ = lean_nat_dec_lt(v_i_807_, v___x_810_);
if (v___x_824_ == 0)
{
goto v___jp_811_;
}
else
{
lean_object* v_start_825_; lean_object* v_stop_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v_start_825_ = lean_ctor_get(v_right_806_, 1);
v_stop_826_ = lean_ctor_get(v_right_806_, 2);
v___x_827_ = lean_nat_sub(v_stop_826_, v_start_825_);
v___x_828_ = lean_nat_dec_lt(v_i_807_, v___x_827_);
if (v___x_828_ == 0)
{
lean_dec(v___x_827_);
goto v___jp_811_;
}
else
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; uint32_t v___x_836_; uint32_t v___x_837_; uint8_t v___x_838_; 
v___x_829_ = lean_nat_sub(v___x_810_, v_i_807_);
lean_dec(v___x_810_);
v___x_830_ = lean_unsigned_to_nat(1u);
v___x_831_ = lean_nat_sub(v___x_829_, v___x_830_);
v___x_832_ = l_Subarray_get___redArg(v_left_805_, v___x_831_);
lean_dec(v___x_831_);
v___x_833_ = lean_nat_sub(v___x_827_, v_i_807_);
lean_dec(v___x_827_);
v___x_834_ = lean_nat_sub(v___x_833_, v___x_830_);
v___x_835_ = l_Subarray_get___redArg(v_right_806_, v___x_834_);
lean_dec(v___x_834_);
v___x_836_ = lean_unbox_uint32(v___x_832_);
lean_dec(v___x_832_);
v___x_837_ = lean_unbox_uint32(v___x_835_);
lean_dec(v___x_835_);
v___x_838_ = lean_uint32_dec_eq(v___x_836_, v___x_837_);
if (v___x_838_ == 0)
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
lean_dec(v_i_807_);
lean_inc_ref(v_left_805_);
v___x_839_ = l_Subarray_take___redArg(v_left_805_, v___x_829_);
v___x_840_ = l_Subarray_take___redArg(v_right_806_, v___x_833_);
lean_dec(v___x_833_);
v___x_841_ = l_Subarray_drop___redArg(v_left_805_, v___x_829_);
lean_dec(v___x_829_);
v___x_842_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_843_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(v___x_841_, v___x_842_);
v___x_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_844_, 0, v___x_840_);
lean_ctor_set(v___x_844_, 1, v___x_843_);
v___x_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_839_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
return v___x_845_;
}
else
{
lean_object* v___x_846_; 
lean_dec(v___x_833_);
lean_dec(v___x_829_);
v___x_846_ = lean_nat_add(v_i_807_, v___x_830_);
lean_dec(v_i_807_);
v_i_807_ = v___x_846_;
goto _start;
}
}
}
v___jp_811_:
{
lean_object* v_start_812_; lean_object* v_stop_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
v_start_812_ = lean_ctor_get(v_right_806_, 1);
v_stop_813_ = lean_ctor_get(v_right_806_, 2);
v___x_814_ = lean_nat_sub(v___x_810_, v_i_807_);
lean_dec(v___x_810_);
lean_inc_ref(v_left_805_);
v___x_815_ = l_Subarray_take___redArg(v_left_805_, v___x_814_);
v___x_816_ = lean_nat_sub(v_stop_813_, v_start_812_);
v___x_817_ = lean_nat_sub(v___x_816_, v_i_807_);
lean_dec(v_i_807_);
lean_dec(v___x_816_);
v___x_818_ = l_Subarray_take___redArg(v_right_806_, v___x_817_);
lean_dec(v___x_817_);
v___x_819_ = l_Subarray_drop___redArg(v_left_805_, v___x_814_);
lean_dec(v___x_814_);
v___x_820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_821_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(v___x_819_, v___x_820_);
v___x_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_818_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_815_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
return v___x_823_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6(lean_object* v_left_848_, lean_object* v_right_849_){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_850_ = lean_unsigned_to_nat(0u);
v___x_851_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8(v_left_848_, v_right_849_, v___x_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(lean_object* v_x_852_, lean_object* v_x_853_){
_start:
{
if (lean_obj_tag(v_x_853_) == 0)
{
lean_inc(v_x_852_);
return v_x_852_;
}
else
{
lean_object* v_key_854_; lean_object* v_value_855_; lean_object* v_tail_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v_key_854_ = lean_ctor_get(v_x_853_, 0);
v_value_855_ = lean_ctor_get(v_x_853_, 1);
v_tail_856_ = lean_ctor_get(v_x_853_, 2);
v___x_857_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(v_x_852_, v_tail_856_);
lean_inc(v_value_855_);
lean_inc(v_key_854_);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v_key_854_);
lean_ctor_set(v___x_858_, 1, v_value_855_);
v___x_859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
lean_ctor_set(v___x_859_, 1, v___x_857_);
return v___x_859_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8___boxed(lean_object* v_x_860_, lean_object* v_x_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(v_x_860_, v_x_861_);
lean_dec(v_x_861_);
lean_dec(v_x_860_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9(lean_object* v_as_863_, size_t v_i_864_, size_t v_stop_865_, lean_object* v_b_866_){
_start:
{
uint8_t v___x_867_; 
v___x_867_ = lean_usize_dec_eq(v_i_864_, v_stop_865_);
if (v___x_867_ == 0)
{
size_t v___x_868_; size_t v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_868_ = ((size_t)1ULL);
v___x_869_ = lean_usize_sub(v_i_864_, v___x_868_);
v___x_870_ = lean_array_uget_borrowed(v_as_863_, v___x_869_);
v___x_871_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(v_b_866_, v___x_870_);
lean_dec(v_b_866_);
v_i_864_ = v___x_869_;
v_b_866_ = v___x_871_;
goto _start;
}
else
{
return v_b_866_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9___boxed(lean_object* v_as_873_, lean_object* v_i_874_, lean_object* v_stop_875_, lean_object* v_b_876_){
_start:
{
size_t v_i_boxed_877_; size_t v_stop_boxed_878_; lean_object* v_res_879_; 
v_i_boxed_877_ = lean_unbox_usize(v_i_874_);
lean_dec(v_i_874_);
v_stop_boxed_878_ = lean_unbox_usize(v_stop_875_);
lean_dec(v_stop_875_);
v_res_879_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9(v_as_873_, v_i_boxed_877_, v_stop_boxed_878_, v_b_876_);
lean_dec_ref(v_as_873_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5_spec__6(lean_object* v_left_880_, lean_object* v_right_881_, lean_object* v_pref_882_){
_start:
{
lean_object* v_start_883_; lean_object* v_stop_884_; lean_object* v_i_885_; lean_object* v___x_891_; uint8_t v___x_892_; 
v_start_883_ = lean_ctor_get(v_left_880_, 1);
v_stop_884_ = lean_ctor_get(v_left_880_, 2);
v_i_885_ = lean_array_get_size(v_pref_882_);
v___x_891_ = lean_nat_sub(v_stop_884_, v_start_883_);
v___x_892_ = lean_nat_dec_lt(v_i_885_, v___x_891_);
lean_dec(v___x_891_);
if (v___x_892_ == 0)
{
goto v___jp_886_;
}
else
{
lean_object* v_start_893_; lean_object* v_stop_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v_start_893_ = lean_ctor_get(v_right_881_, 1);
v_stop_894_ = lean_ctor_get(v_right_881_, 2);
v___x_895_ = lean_nat_sub(v_stop_894_, v_start_893_);
v___x_896_ = lean_nat_dec_lt(v_i_885_, v___x_895_);
lean_dec(v___x_895_);
if (v___x_896_ == 0)
{
goto v___jp_886_;
}
else
{
lean_object* v___x_897_; lean_object* v___x_898_; uint32_t v___x_899_; uint32_t v___x_900_; uint8_t v___x_901_; 
v___x_897_ = l_Subarray_get___redArg(v_left_880_, v_i_885_);
v___x_898_ = l_Subarray_get___redArg(v_right_881_, v_i_885_);
v___x_899_ = lean_unbox_uint32(v___x_897_);
v___x_900_ = lean_unbox_uint32(v___x_898_);
lean_dec(v___x_898_);
v___x_901_ = lean_uint32_dec_eq(v___x_899_, v___x_900_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
lean_dec(v___x_897_);
v___x_902_ = l_Subarray_drop___redArg(v_left_880_, v_i_885_);
v___x_903_ = l_Subarray_drop___redArg(v_right_881_, v_i_885_);
v___x_904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_902_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_905_, 0, v_pref_882_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
return v___x_905_;
}
else
{
lean_object* v___x_906_; 
v___x_906_ = lean_array_push(v_pref_882_, v___x_897_);
v_pref_882_ = v___x_906_;
goto _start;
}
}
}
v___jp_886_:
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_887_ = l_Subarray_drop___redArg(v_left_880_, v_i_885_);
v___x_888_ = l_Subarray_drop___redArg(v_right_881_, v_i_885_);
v___x_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_889_, 0, v___x_887_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v_pref_882_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
return v___x_890_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5(lean_object* v_left_908_, lean_object* v_right_909_){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_911_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5_spec__6(v_left_908_, v_right_909_, v___x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(lean_object* v_histogram_912_, lean_object* v_index_913_, uint32_t v_val_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_histogram_912_, v_val_914_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_916_ = lean_unsigned_to_nat(1u);
v___x_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_917_, 0, v_index_913_);
v___x_918_ = lean_unsigned_to_nat(0u);
v___x_919_ = lean_box(0);
v___x_920_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_920_, 0, v___x_916_);
lean_ctor_set(v___x_920_, 1, v___x_917_);
lean_ctor_set(v___x_920_, 2, v___x_918_);
lean_ctor_set(v___x_920_, 3, v___x_919_);
v___x_921_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_912_, v_val_914_, v___x_920_);
return v___x_921_;
}
else
{
lean_object* v_val_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_943_; 
v_val_922_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_943_ == 0)
{
v___x_924_ = v___x_915_;
v_isShared_925_ = v_isSharedCheck_943_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_val_922_);
lean_dec(v___x_915_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_943_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v_leftCount_926_; lean_object* v_rightCount_927_; lean_object* v_rightIndex_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_941_; 
v_leftCount_926_ = lean_ctor_get(v_val_922_, 0);
v_rightCount_927_ = lean_ctor_get(v_val_922_, 2);
v_rightIndex_928_ = lean_ctor_get(v_val_922_, 3);
v_isSharedCheck_941_ = !lean_is_exclusive(v_val_922_);
if (v_isSharedCheck_941_ == 0)
{
lean_object* v_unused_942_; 
v_unused_942_ = lean_ctor_get(v_val_922_, 1);
lean_dec(v_unused_942_);
v___x_930_ = v_val_922_;
v_isShared_931_ = v_isSharedCheck_941_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_rightIndex_928_);
lean_inc(v_rightCount_927_);
lean_inc(v_leftCount_926_);
lean_dec(v_val_922_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_941_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_932_ = lean_unsigned_to_nat(1u);
v___x_933_ = lean_nat_add(v_leftCount_926_, v___x_932_);
lean_dec(v_leftCount_926_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 0, v_index_913_);
v___x_935_ = v___x_924_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_index_913_);
v___x_935_ = v_reuseFailAlloc_940_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_937_; 
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 1, v___x_935_);
lean_ctor_set(v___x_930_, 0, v___x_933_);
v___x_937_ = v___x_930_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_933_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_939_, 2, v_rightCount_927_);
lean_ctor_set(v_reuseFailAlloc_939_, 3, v_rightIndex_928_);
v___x_937_ = v_reuseFailAlloc_939_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_938_; 
v___x_938_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_912_, v_val_914_, v___x_937_);
return v___x_938_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg___boxed(lean_object* v_histogram_944_, lean_object* v_index_945_, lean_object* v_val_946_){
_start:
{
uint32_t v_val_boxed_947_; lean_object* v_res_948_; 
v_val_boxed_947_ = lean_unbox_uint32(v_val_946_);
lean_dec(v_val_946_);
v_res_948_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(v_histogram_944_, v_index_945_, v_val_boxed_947_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(lean_object* v_upperBound_949_, lean_object* v_fst_950_, lean_object* v___x_951_, lean_object* v_fst_952_, lean_object* v_a_953_, lean_object* v_b_954_){
_start:
{
uint8_t v___x_955_; 
v___x_955_ = lean_nat_dec_lt(v_a_953_, v_upperBound_949_);
if (v___x_955_ == 0)
{
lean_dec(v_a_953_);
return v_b_954_;
}
else
{
lean_object* v___x_956_; uint32_t v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_956_ = l_Subarray_get___redArg(v_fst_952_, v_a_953_);
v___x_957_ = lean_unbox_uint32(v___x_956_);
lean_dec(v___x_956_);
lean_inc(v_a_953_);
v___x_958_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(v_b_954_, v_a_953_, v___x_957_);
v___x_959_ = lean_unsigned_to_nat(1u);
v___x_960_ = lean_nat_add(v_a_953_, v___x_959_);
lean_dec(v_a_953_);
v_a_953_ = v___x_960_;
v_b_954_ = v___x_958_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg___boxed(lean_object* v_upperBound_962_, lean_object* v_fst_963_, lean_object* v___x_964_, lean_object* v_fst_965_, lean_object* v_a_966_, lean_object* v_b_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(v_upperBound_962_, v_fst_963_, v___x_964_, v_fst_965_, v_a_966_, v_b_967_);
lean_dec_ref(v_fst_965_);
lean_dec(v___x_964_);
lean_dec_ref(v_fst_963_);
lean_dec(v_upperBound_962_);
return v_res_968_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v___x_969_ = lean_box(0);
v___x_970_ = lean_unsigned_to_nat(16u);
v___x_971_ = lean_mk_array(v___x_970_, v___x_969_);
return v___x_971_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1(void){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v_hist_974_; 
v___x_972_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0);
v___x_973_ = lean_unsigned_to_nat(0u);
v_hist_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_974_, 0, v___x_973_);
lean_ctor_set(v_hist_974_, 1, v___x_972_);
return v_hist_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(lean_object* v_left_975_, lean_object* v_right_976_){
_start:
{
lean_object* v___x_977_; lean_object* v_snd_978_; lean_object* v_fst_979_; lean_object* v_fst_980_; lean_object* v_snd_981_; lean_object* v___x_982_; lean_object* v_snd_983_; lean_object* v_fst_984_; lean_object* v_fst_985_; lean_object* v_snd_986_; lean_object* v_start_987_; lean_object* v_stop_988_; lean_object* v___x_989_; lean_object* v_hist_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v_start_993_; lean_object* v_stop_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v_buckets_997_; lean_object* v___x_998_; lean_object* v___y_1000_; lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v___x_977_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5(v_left_975_, v_right_976_);
v_snd_978_ = lean_ctor_get(v___x_977_, 1);
lean_inc(v_snd_978_);
v_fst_979_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_fst_979_);
lean_dec_ref(v___x_977_);
v_fst_980_ = lean_ctor_get(v_snd_978_, 0);
lean_inc(v_fst_980_);
v_snd_981_ = lean_ctor_get(v_snd_978_, 1);
lean_inc(v_snd_981_);
lean_dec(v_snd_978_);
v___x_982_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6(v_fst_980_, v_snd_981_);
v_snd_983_ = lean_ctor_get(v___x_982_, 1);
lean_inc(v_snd_983_);
v_fst_984_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_fst_984_);
lean_dec_ref(v___x_982_);
v_fst_985_ = lean_ctor_get(v_snd_983_, 0);
lean_inc(v_fst_985_);
v_snd_986_ = lean_ctor_get(v_snd_983_, 1);
lean_inc(v_snd_986_);
lean_dec(v_snd_983_);
v_start_987_ = lean_ctor_get(v_fst_984_, 1);
v_stop_988_ = lean_ctor_get(v_fst_984_, 2);
v___x_989_ = lean_unsigned_to_nat(0u);
v_hist_990_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1);
v___x_991_ = lean_nat_sub(v_stop_988_, v_start_987_);
v___x_992_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(v___x_991_, v_fst_985_, v___x_991_, v_fst_984_, v___x_989_, v_hist_990_);
v_start_993_ = lean_ctor_get(v_fst_985_, 1);
v_stop_994_ = lean_ctor_get(v_fst_985_, 2);
v___x_995_ = lean_nat_sub(v_stop_994_, v_start_993_);
v___x_996_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(v___x_995_, v___x_995_, v_fst_985_, v___x_991_, v___x_989_, v___x_992_);
lean_dec(v___x_991_);
lean_dec(v___x_995_);
v_buckets_997_ = lean_ctor_get(v___x_996_, 1);
lean_inc_ref(v_buckets_997_);
lean_dec_ref(v___x_996_);
v___x_998_ = lean_box(0);
v___x_1026_ = lean_box(0);
v___x_1027_ = lean_array_get_size(v_buckets_997_);
v___x_1028_ = lean_nat_dec_lt(v___x_989_, v___x_1027_);
if (v___x_1028_ == 0)
{
lean_dec_ref(v_buckets_997_);
v___y_1000_ = v___x_1026_;
goto v___jp_999_;
}
else
{
size_t v___x_1029_; size_t v___x_1030_; lean_object* v___x_1031_; 
v___x_1029_ = lean_usize_of_nat(v___x_1027_);
v___x_1030_ = ((size_t)0ULL);
v___x_1031_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9(v_buckets_997_, v___x_1029_, v___x_1030_, v___x_1026_);
lean_dec_ref(v_buckets_997_);
v___y_1000_ = v___x_1031_;
goto v___jp_999_;
}
v___jp_999_:
{
lean_object* v___x_1001_; 
v___x_1001_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(v___y_1000_, v___x_998_);
lean_dec(v___y_1000_);
if (lean_obj_tag(v___x_1001_) == 1)
{
lean_object* v_val_1002_; lean_object* v_snd_1003_; lean_object* v_snd_1004_; lean_object* v_fst_1005_; lean_object* v_fst_1006_; lean_object* v_snd_1007_; lean_object* v___x_1008_; lean_object* v_fst_1009_; lean_object* v_snd_1010_; lean_object* v___x_1011_; lean_object* v_fst_1012_; lean_object* v_snd_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
v_val_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_val_1002_);
lean_dec_ref_known(v___x_1001_, 1);
v_snd_1003_ = lean_ctor_get(v_val_1002_, 1);
lean_inc(v_snd_1003_);
lean_dec(v_val_1002_);
v_snd_1004_ = lean_ctor_get(v_snd_1003_, 1);
lean_inc(v_snd_1004_);
v_fst_1005_ = lean_ctor_get(v_snd_1003_, 0);
lean_inc(v_fst_1005_);
lean_dec(v_snd_1003_);
v_fst_1006_ = lean_ctor_get(v_snd_1004_, 0);
lean_inc(v_fst_1006_);
v_snd_1007_ = lean_ctor_get(v_snd_1004_, 1);
lean_inc(v_snd_1007_);
lean_dec(v_snd_1004_);
v___x_1008_ = l_Subarray_split___redArg(v_fst_984_, v_fst_1006_);
lean_dec(v_fst_1006_);
v_fst_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_fst_1009_);
v_snd_1010_ = lean_ctor_get(v___x_1008_, 1);
lean_inc(v_snd_1010_);
lean_dec_ref(v___x_1008_);
v___x_1011_ = l_Subarray_split___redArg(v_fst_985_, v_snd_1007_);
lean_dec(v_snd_1007_);
v_fst_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_fst_1012_);
v_snd_1013_ = lean_ctor_get(v___x_1011_, 1);
lean_inc(v_snd_1013_);
lean_dec_ref(v___x_1011_);
v___x_1014_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v_fst_1009_, v_fst_1012_);
v___x_1015_ = l_Array_append___redArg(v_fst_979_, v___x_1014_);
lean_dec_ref(v___x_1014_);
v___x_1016_ = lean_unsigned_to_nat(1u);
v___x_1017_ = lean_mk_empty_array_with_capacity(v___x_1016_);
v___x_1018_ = lean_array_push(v___x_1017_, v_fst_1005_);
v___x_1019_ = l_Array_append___redArg(v___x_1015_, v___x_1018_);
lean_dec_ref(v___x_1018_);
v___x_1020_ = l_Subarray_drop___redArg(v_snd_1010_, v___x_1016_);
v___x_1021_ = l_Subarray_drop___redArg(v_snd_1013_, v___x_1016_);
v___x_1022_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v___x_1020_, v___x_1021_);
v___x_1023_ = l_Array_append___redArg(v___x_1019_, v___x_1022_);
lean_dec_ref(v___x_1022_);
v___x_1024_ = l_Array_append___redArg(v___x_1023_, v_snd_986_);
lean_dec(v_snd_986_);
return v___x_1024_;
}
else
{
lean_object* v___x_1025_; 
lean_dec(v___x_1001_);
lean_dec(v_fst_985_);
lean_dec(v_fst_984_);
v___x_1025_ = l_Array_append___redArg(v_fst_979_, v_snd_986_);
lean_dec(v_snd_986_);
return v___x_1025_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(lean_object* v___x_1032_, lean_object* v_edited_1033_, lean_object* v_a_1034_){
_start:
{
lean_object* v_fst_1035_; lean_object* v_snd_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1055_; 
v_fst_1035_ = lean_ctor_get(v_a_1034_, 0);
v_snd_1036_ = lean_ctor_get(v_a_1034_, 1);
v_isSharedCheck_1055_ = !lean_is_exclusive(v_a_1034_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1038_ = v_a_1034_;
v_isShared_1039_ = v_isSharedCheck_1055_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_snd_1036_);
lean_inc(v_fst_1035_);
lean_dec(v_a_1034_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1055_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
uint8_t v___x_1040_; 
v___x_1040_ = lean_nat_dec_lt(v_snd_1036_, v___x_1032_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1042_; 
if (v_isShared_1039_ == 0)
{
v___x_1042_ = v___x_1038_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_fst_1035_);
lean_ctor_set(v_reuseFailAlloc_1043_, 1, v_snd_1036_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
else
{
uint8_t v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1048_; 
v___x_1044_ = 0;
v___x_1045_ = lean_array_fget_borrowed(v_edited_1033_, v_snd_1036_);
v___x_1046_ = lean_box(v___x_1044_);
lean_inc(v___x_1045_);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 1, v___x_1045_);
lean_ctor_set(v___x_1038_, 0, v___x_1046_);
v___x_1048_ = v___x_1038_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v___x_1046_);
lean_ctor_set(v_reuseFailAlloc_1054_, 1, v___x_1045_);
v___x_1048_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1049_ = lean_array_push(v_fst_1035_, v___x_1048_);
v___x_1050_ = lean_unsigned_to_nat(1u);
v___x_1051_ = lean_nat_add(v_snd_1036_, v___x_1050_);
lean_dec(v_snd_1036_);
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1049_);
lean_ctor_set(v___x_1052_, 1, v___x_1051_);
v_a_1034_ = v___x_1052_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg___boxed(lean_object* v___x_1056_, lean_object* v_edited_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1056_, v_edited_1057_, v_a_1058_);
lean_dec_ref(v_edited_1057_);
lean_dec(v___x_1056_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(size_t v_sz_1060_, size_t v_i_1061_, lean_object* v_bs_1062_){
_start:
{
uint8_t v___x_1063_; 
v___x_1063_ = lean_usize_dec_lt(v_i_1061_, v_sz_1060_);
if (v___x_1063_ == 0)
{
return v_bs_1062_;
}
else
{
lean_object* v_v_1064_; lean_object* v___x_1065_; lean_object* v_bs_x27_1066_; uint8_t v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; size_t v___x_1070_; size_t v___x_1071_; lean_object* v___x_1072_; 
v_v_1064_ = lean_array_uget(v_bs_1062_, v_i_1061_);
v___x_1065_ = lean_unsigned_to_nat(0u);
v_bs_x27_1066_ = lean_array_uset(v_bs_1062_, v_i_1061_, v___x_1065_);
v___x_1067_ = 1;
v___x_1068_ = lean_box(v___x_1067_);
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v_v_1064_);
v___x_1070_ = ((size_t)1ULL);
v___x_1071_ = lean_usize_add(v_i_1061_, v___x_1070_);
v___x_1072_ = lean_array_uset(v_bs_x27_1066_, v_i_1061_, v___x_1069_);
v_i_1061_ = v___x_1071_;
v_bs_1062_ = v___x_1072_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8___boxed(lean_object* v_sz_1074_, lean_object* v_i_1075_, lean_object* v_bs_1076_){
_start:
{
size_t v_sz_boxed_1077_; size_t v_i_boxed_1078_; lean_object* v_res_1079_; 
v_sz_boxed_1077_ = lean_unbox_usize(v_sz_1074_);
lean_dec(v_sz_1074_);
v_i_boxed_1078_ = lean_unbox_usize(v_i_1075_);
lean_dec(v_i_1075_);
v_res_1079_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(v_sz_boxed_1077_, v_i_boxed_1078_, v_bs_1076_);
return v_res_1079_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = 65;
v___x_1081_ = lean_box_uint32(v___x_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(lean_object* v___x_1082_, lean_object* v_original_1083_, uint32_t v_a_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v_fst_1086_; lean_object* v_snd_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1112_; 
v_fst_1086_ = lean_ctor_get(v_a_1085_, 0);
v_snd_1087_ = lean_ctor_get(v_a_1085_, 1);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_a_1085_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1089_ = v_a_1085_;
v_isShared_1090_ = v_isSharedCheck_1112_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_snd_1087_);
lean_inc(v_fst_1086_);
lean_dec(v_a_1085_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1112_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
uint8_t v___x_1091_; 
v___x_1091_ = lean_nat_dec_lt(v_snd_1087_, v___x_1082_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1093_; 
if (v_isShared_1090_ == 0)
{
v___x_1093_ = v___x_1089_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_fst_1086_);
lean_ctor_set(v_reuseFailAlloc_1094_, 1, v_snd_1087_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
else
{
lean_object* v___x_1095_; lean_object* v___x_1096_; uint32_t v___x_1097_; uint8_t v___x_1098_; 
v___x_1095_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed__const__1;
v___x_1096_ = lean_array_get_borrowed(v___x_1095_, v_original_1083_, v_snd_1087_);
v___x_1097_ = lean_unbox_uint32(v___x_1096_);
v___x_1098_ = lean_uint32_dec_eq(v___x_1097_, v_a_1084_);
if (v___x_1098_ == 0)
{
uint8_t v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1102_; 
v___x_1099_ = 1;
v___x_1100_ = lean_box(v___x_1099_);
lean_inc(v___x_1096_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 1, v___x_1096_);
lean_ctor_set(v___x_1089_, 0, v___x_1100_);
v___x_1102_ = v___x_1089_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v___x_1100_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v___x_1096_);
v___x_1102_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1103_ = lean_array_push(v_fst_1086_, v___x_1102_);
v___x_1104_ = lean_unsigned_to_nat(1u);
v___x_1105_ = lean_nat_add(v_snd_1087_, v___x_1104_);
lean_dec(v_snd_1087_);
v___x_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1103_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v_a_1085_ = v___x_1106_;
goto _start;
}
}
else
{
lean_object* v___x_1110_; 
if (v_isShared_1090_ == 0)
{
v___x_1110_ = v___x_1089_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_fst_1086_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_snd_1087_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed(lean_object* v___x_1113_, lean_object* v_original_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_){
_start:
{
uint32_t v_a_boxed_1117_; lean_object* v_res_1118_; 
v_a_boxed_1117_ = lean_unbox_uint32(v_a_1115_);
lean_dec(v_a_1115_);
v_res_1118_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1113_, v_original_1114_, v_a_boxed_1117_, v_a_1116_);
lean_dec_ref(v_original_1114_);
lean_dec(v___x_1113_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(lean_object* v___x_1119_, lean_object* v_edited_1120_, uint32_t v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v_fst_1123_; lean_object* v_snd_1124_; lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1149_; 
v_fst_1123_ = lean_ctor_get(v_a_1122_, 0);
v_snd_1124_ = lean_ctor_get(v_a_1122_, 1);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_a_1122_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1126_ = v_a_1122_;
v_isShared_1127_ = v_isSharedCheck_1149_;
goto v_resetjp_1125_;
}
else
{
lean_inc(v_snd_1124_);
lean_inc(v_fst_1123_);
lean_dec(v_a_1122_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1149_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
uint8_t v___x_1128_; 
v___x_1128_ = lean_nat_dec_lt(v_snd_1124_, v___x_1119_);
if (v___x_1128_ == 0)
{
lean_object* v___x_1130_; 
if (v_isShared_1127_ == 0)
{
v___x_1130_ = v___x_1126_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_fst_1123_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_snd_1124_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1133_; uint32_t v___x_1134_; uint8_t v___x_1135_; 
v___x_1132_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed__const__1;
v___x_1133_ = lean_array_get_borrowed(v___x_1132_, v_edited_1120_, v_snd_1124_);
v___x_1134_ = lean_unbox_uint32(v___x_1133_);
v___x_1135_ = lean_uint32_dec_eq(v___x_1134_, v_a_1121_);
if (v___x_1135_ == 0)
{
uint8_t v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1136_ = 0;
v___x_1137_ = lean_box(v___x_1136_);
lean_inc(v___x_1133_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 1, v___x_1133_);
lean_ctor_set(v___x_1126_, 0, v___x_1137_);
v___x_1139_ = v___x_1126_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v___x_1133_);
v___x_1139_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; 
v___x_1140_ = lean_array_push(v_fst_1123_, v___x_1139_);
v___x_1141_ = lean_unsigned_to_nat(1u);
v___x_1142_ = lean_nat_add(v_snd_1124_, v___x_1141_);
lean_dec(v_snd_1124_);
v___x_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1140_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v_a_1122_ = v___x_1143_;
goto _start;
}
}
else
{
lean_object* v___x_1147_; 
if (v_isShared_1127_ == 0)
{
v___x_1147_ = v___x_1126_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_fst_1123_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_snd_1124_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg___boxed(lean_object* v___x_1150_, lean_object* v_edited_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_){
_start:
{
uint32_t v_a_boxed_1154_; lean_object* v_res_1155_; 
v_a_boxed_1154_ = lean_unbox_uint32(v_a_1152_);
lean_dec(v_a_1152_);
v_res_1155_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1150_, v_edited_1151_, v_a_boxed_1154_, v_a_1153_);
lean_dec_ref(v_edited_1151_);
lean_dec(v___x_1150_);
return v_res_1155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(lean_object* v___x_1156_, lean_object* v_original_1157_, lean_object* v___x_1158_, lean_object* v_edited_1159_, lean_object* v_as_1160_, size_t v_sz_1161_, size_t v_i_1162_, lean_object* v_b_1163_){
_start:
{
uint8_t v___x_1164_; 
v___x_1164_ = lean_usize_dec_lt(v_i_1162_, v_sz_1161_);
if (v___x_1164_ == 0)
{
return v_b_1163_;
}
else
{
lean_object* v_snd_1165_; lean_object* v_fst_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1215_; 
v_snd_1165_ = lean_ctor_get(v_b_1163_, 1);
v_fst_1166_ = lean_ctor_get(v_b_1163_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_b_1163_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1168_ = v_b_1163_;
v_isShared_1169_ = v_isSharedCheck_1215_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_snd_1165_);
lean_inc(v_fst_1166_);
lean_dec(v_b_1163_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1215_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v_fst_1170_; lean_object* v_snd_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1214_; 
v_fst_1170_ = lean_ctor_get(v_snd_1165_, 0);
v_snd_1171_ = lean_ctor_get(v_snd_1165_, 1);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_snd_1165_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1173_ = v_snd_1165_;
v_isShared_1174_ = v_isSharedCheck_1214_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_snd_1171_);
lean_inc(v_fst_1170_);
lean_dec(v_snd_1165_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1214_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v_a_1175_; lean_object* v___x_1177_; 
v_a_1175_ = lean_array_uget_borrowed(v_as_1160_, v_i_1162_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 1, v_fst_1170_);
lean_ctor_set(v___x_1173_, 0, v_fst_1166_);
v___x_1177_ = v___x_1173_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_fst_1166_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_fst_1170_);
v___x_1177_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
uint32_t v___x_1178_; lean_object* v___x_1179_; lean_object* v_fst_1180_; lean_object* v_snd_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1212_; 
v___x_1178_ = lean_unbox_uint32(v_a_1175_);
v___x_1179_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1156_, v_original_1157_, v___x_1178_, v___x_1177_);
v_fst_1180_ = lean_ctor_get(v___x_1179_, 0);
v_snd_1181_ = lean_ctor_get(v___x_1179_, 1);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1179_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1183_ = v___x_1179_;
v_isShared_1184_ = v_isSharedCheck_1212_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_snd_1181_);
lean_inc(v_fst_1180_);
lean_dec(v___x_1179_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1212_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 1, v_snd_1171_);
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_fst_1180_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_snd_1171_);
v___x_1186_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
uint32_t v___x_1187_; lean_object* v___x_1188_; lean_object* v_fst_1189_; lean_object* v_snd_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1210_; 
v___x_1187_ = lean_unbox_uint32(v_a_1175_);
v___x_1188_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1158_, v_edited_1159_, v___x_1187_, v___x_1186_);
v_fst_1189_ = lean_ctor_get(v___x_1188_, 0);
v_snd_1190_ = lean_ctor_get(v___x_1188_, 1);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1192_ = v___x_1188_;
v_isShared_1193_ = v_isSharedCheck_1210_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_snd_1190_);
lean_inc(v_fst_1189_);
lean_dec(v___x_1188_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1210_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
uint8_t v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1197_; 
v___x_1194_ = 2;
v___x_1195_ = lean_box(v___x_1194_);
lean_inc(v_a_1175_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 1, v_a_1175_);
lean_ctor_set(v___x_1192_, 0, v___x_1195_);
v___x_1197_ = v___x_1192_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_a_1175_);
v___x_1197_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1198_ = lean_array_push(v_fst_1189_, v___x_1197_);
v___x_1199_ = lean_unsigned_to_nat(1u);
v___x_1200_ = lean_nat_add(v_snd_1181_, v___x_1199_);
lean_dec(v_snd_1181_);
v___x_1201_ = lean_nat_add(v_snd_1190_, v___x_1199_);
lean_dec(v_snd_1190_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set(v___x_1168_, 1, v___x_1201_);
lean_ctor_set(v___x_1168_, 0, v___x_1200_);
v___x_1203_ = v___x_1168_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1204_; size_t v___x_1205_; size_t v___x_1206_; 
v___x_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___x_1198_);
lean_ctor_set(v___x_1204_, 1, v___x_1203_);
v___x_1205_ = ((size_t)1ULL);
v___x_1206_ = lean_usize_add(v_i_1162_, v___x_1205_);
v_i_1162_ = v___x_1206_;
v_b_1163_ = v___x_1204_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15___boxed(lean_object* v___x_1216_, lean_object* v_original_1217_, lean_object* v___x_1218_, lean_object* v_edited_1219_, lean_object* v_as_1220_, lean_object* v_sz_1221_, lean_object* v_i_1222_, lean_object* v_b_1223_){
_start:
{
size_t v_sz_boxed_1224_; size_t v_i_boxed_1225_; lean_object* v_res_1226_; 
v_sz_boxed_1224_ = lean_unbox_usize(v_sz_1221_);
lean_dec(v_sz_1221_);
v_i_boxed_1225_ = lean_unbox_usize(v_i_1222_);
lean_dec(v_i_1222_);
v_res_1226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(v___x_1216_, v_original_1217_, v___x_1218_, v_edited_1219_, v_as_1220_, v_sz_boxed_1224_, v_i_boxed_1225_, v_b_1223_);
lean_dec_ref(v_as_1220_);
lean_dec_ref(v_edited_1219_);
lean_dec(v___x_1218_);
lean_dec_ref(v_original_1217_);
lean_dec(v___x_1216_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(lean_object* v___x_1227_, lean_object* v_edited_1228_, lean_object* v___x_1229_, lean_object* v_original_1230_, lean_object* v_as_1231_, size_t v_sz_1232_, size_t v_i_1233_, lean_object* v_b_1234_){
_start:
{
uint8_t v___x_1235_; 
v___x_1235_ = lean_usize_dec_lt(v_i_1233_, v_sz_1232_);
if (v___x_1235_ == 0)
{
return v_b_1234_;
}
else
{
lean_object* v_snd_1236_; lean_object* v_fst_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1286_; 
v_snd_1236_ = lean_ctor_get(v_b_1234_, 1);
v_fst_1237_ = lean_ctor_get(v_b_1234_, 0);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_b_1234_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1239_ = v_b_1234_;
v_isShared_1240_ = v_isSharedCheck_1286_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_snd_1236_);
lean_inc(v_fst_1237_);
lean_dec(v_b_1234_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1286_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v_fst_1241_; lean_object* v_snd_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1285_; 
v_fst_1241_ = lean_ctor_get(v_snd_1236_, 0);
v_snd_1242_ = lean_ctor_get(v_snd_1236_, 1);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_snd_1236_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1244_ = v_snd_1236_;
v_isShared_1245_ = v_isSharedCheck_1285_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_snd_1242_);
lean_inc(v_fst_1241_);
lean_dec(v_snd_1236_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1285_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
lean_object* v_a_1246_; lean_object* v___x_1248_; 
v_a_1246_ = lean_array_uget_borrowed(v_as_1231_, v_i_1233_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v_fst_1241_);
lean_ctor_set(v___x_1244_, 0, v_fst_1237_);
v___x_1248_ = v___x_1244_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_fst_1237_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v_fst_1241_);
v___x_1248_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
uint32_t v___x_1249_; lean_object* v___x_1250_; lean_object* v_fst_1251_; lean_object* v_snd_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1283_; 
v___x_1249_ = lean_unbox_uint32(v_a_1246_);
v___x_1250_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1229_, v_original_1230_, v___x_1249_, v___x_1248_);
v_fst_1251_ = lean_ctor_get(v___x_1250_, 0);
v_snd_1252_ = lean_ctor_get(v___x_1250_, 1);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1254_ = v___x_1250_;
v_isShared_1255_ = v_isSharedCheck_1283_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_snd_1252_);
lean_inc(v_fst_1251_);
lean_dec(v___x_1250_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1283_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 1, v_snd_1242_);
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_fst_1251_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_snd_1242_);
v___x_1257_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
uint32_t v___x_1258_; lean_object* v___x_1259_; lean_object* v_fst_1260_; lean_object* v_snd_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1281_; 
v___x_1258_ = lean_unbox_uint32(v_a_1246_);
v___x_1259_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1227_, v_edited_1228_, v___x_1258_, v___x_1257_);
v_fst_1260_ = lean_ctor_get(v___x_1259_, 0);
v_snd_1261_ = lean_ctor_get(v___x_1259_, 1);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1259_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1263_ = v___x_1259_;
v_isShared_1264_ = v_isSharedCheck_1281_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_snd_1261_);
lean_inc(v_fst_1260_);
lean_dec(v___x_1259_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1281_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
uint8_t v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1268_; 
v___x_1265_ = 2;
v___x_1266_ = lean_box(v___x_1265_);
lean_inc(v_a_1246_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 1, v_a_1246_);
lean_ctor_set(v___x_1263_, 0, v___x_1266_);
v___x_1268_ = v___x_1263_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1266_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_a_1246_);
v___x_1268_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1274_; 
v___x_1269_ = lean_array_push(v_fst_1260_, v___x_1268_);
v___x_1270_ = lean_unsigned_to_nat(1u);
v___x_1271_ = lean_nat_add(v_snd_1252_, v___x_1270_);
lean_dec(v_snd_1252_);
v___x_1272_ = lean_nat_add(v_snd_1261_, v___x_1270_);
lean_dec(v_snd_1261_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 1, v___x_1272_);
lean_ctor_set(v___x_1239_, 0, v___x_1271_);
v___x_1274_ = v___x_1239_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1271_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v___x_1272_);
v___x_1274_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
lean_object* v___x_1275_; size_t v___x_1276_; size_t v___x_1277_; lean_object* v___x_1278_; 
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1269_);
lean_ctor_set(v___x_1275_, 1, v___x_1274_);
v___x_1276_ = ((size_t)1ULL);
v___x_1277_ = lean_usize_add(v_i_1233_, v___x_1276_);
v___x_1278_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(v___x_1229_, v_original_1230_, v___x_1227_, v_edited_1228_, v_as_1231_, v_sz_1232_, v___x_1277_, v___x_1275_);
return v___x_1278_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5___boxed(lean_object* v___x_1287_, lean_object* v_edited_1288_, lean_object* v___x_1289_, lean_object* v_original_1290_, lean_object* v_as_1291_, lean_object* v_sz_1292_, lean_object* v_i_1293_, lean_object* v_b_1294_){
_start:
{
size_t v_sz_boxed_1295_; size_t v_i_boxed_1296_; lean_object* v_res_1297_; 
v_sz_boxed_1295_ = lean_unbox_usize(v_sz_1292_);
lean_dec(v_sz_1292_);
v_i_boxed_1296_ = lean_unbox_usize(v_i_1293_);
lean_dec(v_i_1293_);
v_res_1297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v___x_1287_, v_edited_1288_, v___x_1289_, v_original_1290_, v_as_1291_, v_sz_boxed_1295_, v_i_boxed_1296_, v_b_1294_);
lean_dec_ref(v_as_1291_);
lean_dec_ref(v_original_1290_);
lean_dec(v___x_1289_);
lean_dec_ref(v_edited_1288_);
lean_dec(v___x_1287_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(lean_object* v_original_1305_, lean_object* v_edited_1306_){
_start:
{
lean_object* v_i_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v_i_1307_ = lean_unsigned_to_nat(0u);
v___x_1308_ = lean_array_get_size(v_original_1305_);
v___x_1309_ = lean_nat_dec_lt(v_i_1307_, v___x_1308_);
if (v___x_1309_ == 0)
{
size_t v_sz_1310_; size_t v___x_1311_; lean_object* v___x_1312_; 
lean_dec_ref(v_original_1305_);
v_sz_1310_ = lean_array_size(v_edited_1306_);
v___x_1311_ = ((size_t)0ULL);
v___x_1312_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(v_sz_1310_, v___x_1311_, v_edited_1306_);
return v___x_1312_;
}
else
{
lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1313_ = lean_array_get_size(v_edited_1306_);
v___x_1314_ = lean_nat_dec_lt(v_i_1307_, v___x_1313_);
if (v___x_1314_ == 0)
{
size_t v_sz_1315_; size_t v___x_1316_; lean_object* v___x_1317_; 
lean_dec_ref(v_edited_1306_);
v_sz_1315_ = lean_array_size(v_original_1305_);
v___x_1316_ = ((size_t)0ULL);
v___x_1317_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(v_sz_1315_, v___x_1316_, v_original_1305_);
return v___x_1317_;
}
else
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v_ds_1320_; lean_object* v___x_1321_; size_t v_sz_1322_; size_t v___x_1323_; lean_object* v___x_1324_; lean_object* v_snd_1325_; lean_object* v_fst_1326_; lean_object* v_fst_1327_; lean_object* v_snd_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1347_; 
lean_inc_ref(v_original_1305_);
v___x_1318_ = l_Array_toSubarray___redArg(v_original_1305_, v_i_1307_, v___x_1308_);
lean_inc_ref(v_edited_1306_);
v___x_1319_ = l_Array_toSubarray___redArg(v_edited_1306_, v_i_1307_, v___x_1313_);
v_ds_1320_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v___x_1318_, v___x_1319_);
v___x_1321_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__2));
v_sz_1322_ = lean_array_size(v_ds_1320_);
v___x_1323_ = ((size_t)0ULL);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v___x_1313_, v_edited_1306_, v___x_1308_, v_original_1305_, v_ds_1320_, v_sz_1322_, v___x_1323_, v___x_1321_);
lean_dec_ref(v_ds_1320_);
v_snd_1325_ = lean_ctor_get(v___x_1324_, 1);
lean_inc(v_snd_1325_);
v_fst_1326_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_fst_1326_);
lean_dec_ref(v___x_1324_);
v_fst_1327_ = lean_ctor_get(v_snd_1325_, 0);
v_snd_1328_ = lean_ctor_get(v_snd_1325_, 1);
v_isSharedCheck_1347_ = !lean_is_exclusive(v_snd_1325_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1330_ = v_snd_1325_;
v_isShared_1331_ = v_isSharedCheck_1347_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_snd_1328_);
lean_inc(v_fst_1327_);
lean_dec(v_snd_1325_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1347_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 1, v_fst_1327_);
lean_ctor_set(v___x_1330_, 0, v_fst_1326_);
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_fst_1326_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_fst_1327_);
v___x_1333_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
lean_object* v___x_1334_; lean_object* v_fst_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1344_; 
v___x_1334_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_1308_, v_original_1305_, v___x_1333_);
lean_dec_ref(v_original_1305_);
v_fst_1335_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1344_ == 0)
{
lean_object* v_unused_1345_; 
v_unused_1345_ = lean_ctor_get(v___x_1334_, 1);
lean_dec(v_unused_1345_);
v___x_1337_ = v___x_1334_;
v_isShared_1338_ = v_isSharedCheck_1344_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_fst_1335_);
lean_dec(v___x_1334_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1344_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
lean_ctor_set(v___x_1337_, 1, v_snd_1328_);
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_fst_1335_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_snd_1328_);
v___x_1340_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1341_; lean_object* v_fst_1342_; 
v___x_1341_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1313_, v_edited_1306_, v___x_1340_);
lean_dec_ref(v_edited_1306_);
v_fst_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_fst_1342_);
lean_dec_ref(v___x_1341_);
return v_fst_1342_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(lean_object* v_s_1348_, lean_object* v_a_1349_, uint8_t v_b_1350_){
_start:
{
lean_object* v_str_1351_; lean_object* v_startInclusive_1352_; lean_object* v_endExclusive_1353_; lean_object* v___x_1354_; uint8_t v_decide_1355_; 
v_str_1351_ = lean_ctor_get(v_s_1348_, 0);
v_startInclusive_1352_ = lean_ctor_get(v_s_1348_, 1);
v_endExclusive_1353_ = lean_ctor_get(v_s_1348_, 2);
v___x_1354_ = lean_nat_sub(v_endExclusive_1353_, v_startInclusive_1352_);
v_decide_1355_ = lean_nat_dec_eq(v_a_1349_, v___x_1354_);
lean_dec(v___x_1354_);
if (v_decide_1355_ == 0)
{
lean_object* v___x_1356_; uint32_t v___x_1357_; uint32_t v___x_1358_; uint8_t v___x_1359_; 
v___x_1356_ = lean_nat_add(v_startInclusive_1352_, v_a_1349_);
lean_dec(v_a_1349_);
v___x_1357_ = lean_string_utf8_get_fast(v_str_1351_, v___x_1356_);
v___x_1358_ = 10;
v___x_1359_ = lean_uint32_dec_eq(v___x_1357_, v___x_1358_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = lean_string_utf8_next_fast(v_str_1351_, v___x_1356_);
lean_dec(v___x_1356_);
v___x_1361_ = lean_nat_sub(v___x_1360_, v_startInclusive_1352_);
v_a_1349_ = v___x_1361_;
v_b_1350_ = v___x_1359_;
goto _start;
}
else
{
lean_dec(v___x_1356_);
return v___x_1359_;
}
}
else
{
lean_dec(v_a_1349_);
return v_b_1350_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg___boxed(lean_object* v_s_1363_, lean_object* v_a_1364_, lean_object* v_b_1365_){
_start:
{
uint8_t v_b_boxed_1366_; uint8_t v_res_1367_; lean_object* v_r_1368_; 
v_b_boxed_1366_ = lean_unbox(v_b_1365_);
v_res_1367_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1363_, v_a_1364_, v_b_boxed_1366_);
lean_dec_ref(v_s_1363_);
v_r_1368_ = lean_box(v_res_1367_);
return v_r_1368_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(lean_object* v_s_1369_){
_start:
{
lean_object* v_searcher_1370_; uint8_t v___x_1371_; uint8_t v___x_1372_; 
v_searcher_1370_ = lean_unsigned_to_nat(0u);
v___x_1371_ = 0;
v___x_1372_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1369_, v_searcher_1370_, v___x_1371_);
return v___x_1372_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0___boxed(lean_object* v_s_1373_){
_start:
{
uint8_t v_res_1374_; lean_object* v_r_1375_; 
v_res_1374_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v_s_1373_);
lean_dec_ref(v_s_1373_);
v_r_1375_ = lean_box(v_res_1374_);
return v_r_1375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(lean_object* v_oldWs_1376_, lean_object* v_newWs_1377_){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1378_ = lean_unsigned_to_nat(0u);
v___x_1379_ = lean_string_utf8_byte_size(v_oldWs_1376_);
lean_inc_ref(v_oldWs_1376_);
v___x_1380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1380_, 0, v_oldWs_1376_);
lean_ctor_set(v___x_1380_, 1, v___x_1378_);
lean_ctor_set(v___x_1380_, 2, v___x_1379_);
v___x_1381_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_1380_);
lean_dec_ref_known(v___x_1380_, 3);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1382_ = l_String_toListImpl(v_oldWs_1376_);
v___x_1383_ = lean_array_mk(v___x_1382_);
v___x_1384_ = l_String_toListImpl(v_newWs_1377_);
v___x_1385_ = lean_array_mk(v___x_1384_);
v___x_1386_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_1383_, v___x_1385_);
v___x_1387_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_1386_);
lean_dec_ref(v___x_1386_);
return v___x_1387_;
}
else
{
uint8_t v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; 
lean_dec_ref(v_oldWs_1376_);
v___x_1388_ = 2;
v___x_1389_ = lean_box(v___x_1388_);
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
lean_ctor_set(v___x_1390_, 1, v_newWs_1377_);
v___x_1391_ = lean_unsigned_to_nat(1u);
v___x_1392_ = lean_mk_empty_array_with_capacity(v___x_1391_);
v___x_1393_ = lean_array_push(v___x_1392_, v___x_1390_);
return v___x_1393_;
}
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(lean_object* v_s_1394_, lean_object* v_inst_1395_, lean_object* v_R_1396_, lean_object* v_a_1397_, uint8_t v_b_1398_, lean_object* v_c_1399_){
_start:
{
uint8_t v___x_1400_; 
v___x_1400_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1394_, v_a_1397_, v_b_1398_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___boxed(lean_object* v_s_1401_, lean_object* v_inst_1402_, lean_object* v_R_1403_, lean_object* v_a_1404_, lean_object* v_b_1405_, lean_object* v_c_1406_){
_start:
{
uint8_t v_b_boxed_1407_; uint8_t v_res_1408_; lean_object* v_r_1409_; 
v_b_boxed_1407_ = lean_unbox(v_b_1405_);
v_res_1408_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(v_s_1401_, v_inst_1402_, v_R_1403_, v_a_1404_, v_b_boxed_1407_, v_c_1406_);
lean_dec_ref(v_s_1401_);
v_r_1409_ = lean_box(v_res_1408_);
return v_r_1409_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(lean_object* v___x_1410_, lean_object* v_original_1411_, uint32_t v_a_1412_, lean_object* v_inst_1413_, lean_object* v_a_1414_){
_start:
{
lean_object* v___x_1415_; 
v___x_1415_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1410_, v_original_1411_, v_a_1412_, v_a_1414_);
return v___x_1415_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___boxed(lean_object* v___x_1416_, lean_object* v_original_1417_, lean_object* v_a_1418_, lean_object* v_inst_1419_, lean_object* v_a_1420_){
_start:
{
uint32_t v_a_boxed_1421_; lean_object* v_res_1422_; 
v_a_boxed_1421_ = lean_unbox_uint32(v_a_1418_);
lean_dec(v_a_1418_);
v_res_1422_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v___x_1416_, v_original_1417_, v_a_boxed_1421_, v_inst_1419_, v_a_1420_);
lean_dec_ref(v_original_1417_);
lean_dec(v___x_1416_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(lean_object* v___x_1423_, lean_object* v_edited_1424_, uint32_t v_a_1425_, lean_object* v_inst_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1423_, v_edited_1424_, v_a_1425_, v_a_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___boxed(lean_object* v___x_1429_, lean_object* v_edited_1430_, lean_object* v_a_1431_, lean_object* v_inst_1432_, lean_object* v_a_1433_){
_start:
{
uint32_t v_a_boxed_1434_; lean_object* v_res_1435_; 
v_a_boxed_1434_ = lean_unbox_uint32(v_a_1431_);
lean_dec(v_a_1431_);
v_res_1435_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(v___x_1429_, v_edited_1430_, v_a_boxed_1434_, v_inst_1432_, v_a_1433_);
lean_dec_ref(v_edited_1430_);
lean_dec(v___x_1429_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(lean_object* v___x_1436_, lean_object* v_original_1437_, lean_object* v_inst_1438_, lean_object* v_a_1439_){
_start:
{
lean_object* v___x_1440_; 
v___x_1440_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_1436_, v_original_1437_, v_a_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___boxed(lean_object* v___x_1441_, lean_object* v_original_1442_, lean_object* v_inst_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(v___x_1441_, v_original_1442_, v_inst_1443_, v_a_1444_);
lean_dec_ref(v_original_1442_);
lean_dec(v___x_1441_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(lean_object* v___x_1446_, lean_object* v_edited_1447_, lean_object* v_inst_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1446_, v_edited_1447_, v_a_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___boxed(lean_object* v___x_1451_, lean_object* v_edited_1452_, lean_object* v_inst_1453_, lean_object* v_a_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(v___x_1451_, v_edited_1452_, v_inst_1453_, v_a_1454_);
lean_dec_ref(v_edited_1452_);
lean_dec(v___x_1451_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7(lean_object* v_as_1456_, lean_object* v_as_x27_1457_, lean_object* v_b_1458_, lean_object* v_a_1459_){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(v_as_x27_1457_, v_b_1458_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___boxed(lean_object* v_as_1461_, lean_object* v_as_x27_1462_, lean_object* v_b_1463_, lean_object* v_a_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7(v_as_1461_, v_as_x27_1462_, v_b_1463_, v_a_1464_);
lean_dec(v_as_x27_1462_);
lean_dec(v_as_1461_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10(lean_object* v_lsize_1466_, lean_object* v_rsize_1467_, lean_object* v_histogram_1468_, lean_object* v_index_1469_, uint32_t v_val_1470_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(v_histogram_1468_, v_index_1469_, v_val_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___boxed(lean_object* v_lsize_1472_, lean_object* v_rsize_1473_, lean_object* v_histogram_1474_, lean_object* v_index_1475_, lean_object* v_val_1476_){
_start:
{
uint32_t v_val_boxed_1477_; lean_object* v_res_1478_; 
v_val_boxed_1477_ = lean_unbox_uint32(v_val_1476_);
lean_dec(v_val_1476_);
v_res_1478_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10(v_lsize_1472_, v_rsize_1473_, v_histogram_1474_, v_index_1475_, v_val_boxed_1477_);
lean_dec(v_rsize_1473_);
lean_dec(v_lsize_1472_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11(lean_object* v_upperBound_1479_, lean_object* v___x_1480_, lean_object* v_fst_1481_, lean_object* v___x_1482_, lean_object* v_inst_1483_, lean_object* v_R_1484_, lean_object* v_a_1485_, lean_object* v_b_1486_, lean_object* v_c_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(v_upperBound_1479_, v___x_1480_, v_fst_1481_, v___x_1482_, v_a_1485_, v_b_1486_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___boxed(lean_object* v_upperBound_1489_, lean_object* v___x_1490_, lean_object* v_fst_1491_, lean_object* v___x_1492_, lean_object* v_inst_1493_, lean_object* v_R_1494_, lean_object* v_a_1495_, lean_object* v_b_1496_, lean_object* v_c_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11(v_upperBound_1489_, v___x_1490_, v_fst_1491_, v___x_1492_, v_inst_1493_, v_R_1494_, v_a_1495_, v_b_1496_, v_c_1497_);
lean_dec(v___x_1492_);
lean_dec_ref(v_fst_1491_);
lean_dec(v___x_1490_);
lean_dec(v_upperBound_1489_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12(lean_object* v_lsize_1499_, lean_object* v_rsize_1500_, lean_object* v_histogram_1501_, lean_object* v_index_1502_, uint32_t v_val_1503_){
_start:
{
lean_object* v___x_1504_; 
v___x_1504_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(v_histogram_1501_, v_index_1502_, v_val_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___boxed(lean_object* v_lsize_1505_, lean_object* v_rsize_1506_, lean_object* v_histogram_1507_, lean_object* v_index_1508_, lean_object* v_val_1509_){
_start:
{
uint32_t v_val_boxed_1510_; lean_object* v_res_1511_; 
v_val_boxed_1510_ = lean_unbox_uint32(v_val_1509_);
lean_dec(v_val_1509_);
v_res_1511_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12(v_lsize_1505_, v_rsize_1506_, v_histogram_1507_, v_index_1508_, v_val_boxed_1510_);
lean_dec(v_rsize_1506_);
lean_dec(v_lsize_1505_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13(lean_object* v_upperBound_1512_, lean_object* v_fst_1513_, lean_object* v___x_1514_, lean_object* v_fst_1515_, lean_object* v_inst_1516_, lean_object* v_R_1517_, lean_object* v_a_1518_, lean_object* v_b_1519_, lean_object* v_c_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(v_upperBound_1512_, v_fst_1513_, v___x_1514_, v_fst_1515_, v_a_1518_, v_b_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___boxed(lean_object* v_upperBound_1522_, lean_object* v_fst_1523_, lean_object* v___x_1524_, lean_object* v_fst_1525_, lean_object* v_inst_1526_, lean_object* v_R_1527_, lean_object* v_a_1528_, lean_object* v_b_1529_, lean_object* v_c_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13(v_upperBound_1522_, v_fst_1523_, v___x_1524_, v_fst_1525_, v_inst_1526_, v_R_1527_, v_a_1528_, v_b_1529_, v_c_1530_);
lean_dec_ref(v_fst_1525_);
lean_dec(v___x_1524_);
lean_dec_ref(v_fst_1523_);
lean_dec(v_upperBound_1522_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13(lean_object* v_00_u03b2_1532_, lean_object* v_m_1533_, uint32_t v_a_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_m_1533_, v_a_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___boxed(lean_object* v_00_u03b2_1536_, lean_object* v_m_1537_, lean_object* v_a_1538_){
_start:
{
uint32_t v_a_boxed_1539_; lean_object* v_res_1540_; 
v_a_boxed_1539_ = lean_unbox_uint32(v_a_1538_);
lean_dec(v_a_1538_);
v_res_1540_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13(v_00_u03b2_1536_, v_m_1537_, v_a_boxed_1539_);
lean_dec_ref(v_m_1537_);
return v_res_1540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14(lean_object* v_00_u03b2_1541_, lean_object* v_m_1542_, uint32_t v_a_1543_, lean_object* v_b_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_m_1542_, v_a_1543_, v_b_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___boxed(lean_object* v_00_u03b2_1546_, lean_object* v_m_1547_, lean_object* v_a_1548_, lean_object* v_b_1549_){
_start:
{
uint32_t v_a_boxed_1550_; lean_object* v_res_1551_; 
v_a_boxed_1550_ = lean_unbox_uint32(v_a_1548_);
lean_dec(v_a_1548_);
v_res_1551_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14(v_00_u03b2_1546_, v_m_1547_, v_a_boxed_1550_, v_b_1549_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14(lean_object* v_inst_1552_, lean_object* v_R_1553_, lean_object* v_a_1554_, lean_object* v_b_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(v_a_1554_, v_b_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20(lean_object* v_00_u03b2_1557_, uint32_t v_a_1558_, lean_object* v_x_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg(v_a_1558_, v_x_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___boxed(lean_object* v_00_u03b2_1561_, lean_object* v_a_1562_, lean_object* v_x_1563_){
_start:
{
uint32_t v_a_boxed_1564_; lean_object* v_res_1565_; 
v_a_boxed_1564_ = lean_unbox_uint32(v_a_1562_);
lean_dec(v_a_1562_);
v_res_1565_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20(v_00_u03b2_1561_, v_a_boxed_1564_, v_x_1563_);
lean_dec(v_x_1563_);
return v_res_1565_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22(lean_object* v_00_u03b2_1566_, uint32_t v_a_1567_, lean_object* v_x_1568_){
_start:
{
uint8_t v___x_1569_; 
v___x_1569_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(v_a_1567_, v_x_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___boxed(lean_object* v_00_u03b2_1570_, lean_object* v_a_1571_, lean_object* v_x_1572_){
_start:
{
uint32_t v_a_boxed_1573_; uint8_t v_res_1574_; lean_object* v_r_1575_; 
v_a_boxed_1573_ = lean_unbox_uint32(v_a_1571_);
lean_dec(v_a_1571_);
v_res_1574_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22(v_00_u03b2_1570_, v_a_boxed_1573_, v_x_1572_);
lean_dec(v_x_1572_);
v_r_1575_ = lean_box(v_res_1574_);
return v_r_1575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23(lean_object* v_00_u03b2_1576_, lean_object* v_data_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23___redArg(v_data_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24(lean_object* v_00_u03b2_1579_, uint32_t v_a_1580_, lean_object* v_b_1581_, lean_object* v_x_1582_){
_start:
{
lean_object* v___x_1583_; 
v___x_1583_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(v_a_1580_, v_b_1581_, v_x_1582_);
return v___x_1583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___boxed(lean_object* v_00_u03b2_1584_, lean_object* v_a_1585_, lean_object* v_b_1586_, lean_object* v_x_1587_){
_start:
{
uint32_t v_a_boxed_1588_; lean_object* v_res_1589_; 
v_a_boxed_1588_ = lean_unbox_uint32(v_a_1585_);
lean_dec(v_a_1585_);
v_res_1589_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24(v_00_u03b2_1584_, v_a_boxed_1588_, v_b_1586_, v_x_1587_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28(lean_object* v_00_u03b2_1590_, lean_object* v_i_1591_, lean_object* v_source_1592_, lean_object* v_target_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28___redArg(v_i_1591_, v_source_1592_, v_target_1593_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_1595_, lean_object* v_x_1596_, lean_object* v_x_1597_){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29___redArg(v_x_1596_, v_x_1597_);
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(lean_object* v_s_1599_, lean_object* v_stopPos_1600_, lean_object* v_i_1601_){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1605_ = lean_unsigned_to_nat(1u);
v___x_1606_ = lean_nat_add(v_i_1601_, v___x_1605_);
v___x_1607_ = lean_nat_dec_le(v___x_1606_, v_stopPos_1600_);
lean_dec(v___x_1606_);
if (v___x_1607_ == 0)
{
return v_i_1601_;
}
else
{
uint32_t v___x_1608_; uint32_t v___x_1609_; uint8_t v___x_1610_; 
v___x_1608_ = lean_string_utf8_get(v_s_1599_, v_i_1601_);
v___x_1609_ = 32;
v___x_1610_ = lean_uint32_dec_eq(v___x_1608_, v___x_1609_);
if (v___x_1610_ == 0)
{
uint32_t v___x_1611_; uint8_t v___x_1612_; 
v___x_1611_ = 9;
v___x_1612_ = lean_uint32_dec_eq(v___x_1608_, v___x_1611_);
if (v___x_1612_ == 0)
{
uint32_t v___x_1613_; uint8_t v___x_1614_; 
v___x_1613_ = 13;
v___x_1614_ = lean_uint32_dec_eq(v___x_1608_, v___x_1613_);
if (v___x_1614_ == 0)
{
uint32_t v___x_1615_; uint8_t v___x_1616_; 
v___x_1615_ = 10;
v___x_1616_ = lean_uint32_dec_eq(v___x_1608_, v___x_1615_);
if (v___x_1616_ == 0)
{
return v_i_1601_;
}
else
{
goto v___jp_1602_;
}
}
else
{
goto v___jp_1602_;
}
}
else
{
goto v___jp_1602_;
}
}
else
{
goto v___jp_1602_;
}
}
v___jp_1602_:
{
lean_object* v___x_1603_; 
v___x_1603_ = lean_string_utf8_next(v_s_1599_, v_i_1601_);
lean_dec(v_i_1601_);
v_i_1601_ = v___x_1603_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0___boxed(lean_object* v_s_1617_, lean_object* v_stopPos_1618_, lean_object* v_i_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1617_, v_stopPos_1618_, v_i_1619_);
lean_dec(v_stopPos_1618_);
lean_dec_ref(v_s_1617_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(lean_object* v_s_1621_, lean_object* v_b_1622_, lean_object* v_i_1623_, lean_object* v_r_1624_, lean_object* v_ws_1625_){
_start:
{
uint8_t v___x_1634_; 
v___x_1634_ = lean_string_utf8_at_end(v_s_1621_, v_i_1623_);
if (v___x_1634_ == 0)
{
uint32_t v___x_1635_; uint32_t v___x_1636_; uint8_t v___x_1637_; 
v___x_1635_ = lean_string_utf8_get(v_s_1621_, v_i_1623_);
v___x_1636_ = 32;
v___x_1637_ = lean_uint32_dec_eq(v___x_1635_, v___x_1636_);
if (v___x_1637_ == 0)
{
uint32_t v___x_1638_; uint8_t v___x_1639_; 
v___x_1638_ = 9;
v___x_1639_ = lean_uint32_dec_eq(v___x_1635_, v___x_1638_);
if (v___x_1639_ == 0)
{
uint32_t v___x_1640_; uint8_t v___x_1641_; 
v___x_1640_ = 13;
v___x_1641_ = lean_uint32_dec_eq(v___x_1635_, v___x_1640_);
if (v___x_1641_ == 0)
{
uint32_t v___x_1642_; uint8_t v___x_1643_; 
v___x_1642_ = 10;
v___x_1643_ = lean_uint32_dec_eq(v___x_1635_, v___x_1642_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; 
v___x_1644_ = lean_string_utf8_next(v_s_1621_, v_i_1623_);
lean_dec(v_i_1623_);
v_i_1623_ = v___x_1644_;
goto _start;
}
else
{
goto v___jp_1626_;
}
}
else
{
goto v___jp_1626_;
}
}
else
{
goto v___jp_1626_;
}
}
else
{
goto v___jp_1626_;
}
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v___x_1646_ = lean_string_utf8_extract(v_s_1621_, v_b_1622_, v_i_1623_);
lean_dec(v_i_1623_);
lean_dec(v_b_1622_);
v___x_1647_ = lean_array_push(v_r_1624_, v___x_1646_);
v___x_1648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1647_);
lean_ctor_set(v___x_1648_, 1, v_ws_1625_);
return v___x_1648_;
}
v___jp_1626_:
{
lean_object* v___x_1627_; lean_object* v_e_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v___x_1627_ = lean_string_utf8_byte_size(v_s_1621_);
lean_inc(v_i_1623_);
v_e_1628_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1621_, v___x_1627_, v_i_1623_);
v___x_1629_ = lean_string_utf8_extract(v_s_1621_, v_b_1622_, v_i_1623_);
lean_dec(v_b_1622_);
v___x_1630_ = lean_array_push(v_r_1624_, v___x_1629_);
v___x_1631_ = lean_string_utf8_extract(v_s_1621_, v_i_1623_, v_e_1628_);
lean_dec(v_i_1623_);
v___x_1632_ = lean_array_push(v_ws_1625_, v___x_1631_);
lean_inc(v_e_1628_);
v_b_1622_ = v_e_1628_;
v_i_1623_ = v_e_1628_;
v_r_1624_ = v___x_1630_;
v_ws_1625_ = v___x_1632_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux___boxed(lean_object* v_s_1649_, lean_object* v_b_1650_, lean_object* v_i_1651_, lean_object* v_r_1652_, lean_object* v_ws_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1649_, v_b_1650_, v_i_1651_, v_r_1652_, v_ws_1653_);
lean_dec_ref(v_s_1649_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(lean_object* v_s_1657_){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v___x_1658_ = lean_unsigned_to_nat(0u);
v___x_1659_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_1660_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1657_, v___x_1658_, v___x_1658_, v___x_1659_, v___x_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___boxed(lean_object* v_s_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_1661_);
lean_dec_ref(v_s_1661_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(size_t v_sz_1663_, size_t v_i_1664_, lean_object* v_bs_1665_){
_start:
{
uint8_t v___x_1666_; 
v___x_1666_ = lean_usize_dec_lt(v_i_1664_, v_sz_1663_);
if (v___x_1666_ == 0)
{
return v_bs_1665_;
}
else
{
lean_object* v_v_1667_; lean_object* v_fst_1668_; lean_object* v_snd_1669_; lean_object* v___x_1671_; uint8_t v_isShared_1672_; uint8_t v_isSharedCheck_1693_; 
v_v_1667_ = lean_array_uget(v_bs_1665_, v_i_1664_);
v_fst_1668_ = lean_ctor_get(v_v_1667_, 0);
v_snd_1669_ = lean_ctor_get(v_v_1667_, 1);
v_isSharedCheck_1693_ = !lean_is_exclusive(v_v_1667_);
if (v_isSharedCheck_1693_ == 0)
{
v___x_1671_ = v_v_1667_;
v_isShared_1672_ = v_isSharedCheck_1693_;
goto v_resetjp_1670_;
}
else
{
lean_inc(v_snd_1669_);
lean_inc(v_fst_1668_);
lean_dec(v_v_1667_);
v___x_1671_ = lean_box(0);
v_isShared_1672_ = v_isSharedCheck_1693_;
goto v_resetjp_1670_;
}
v_resetjp_1670_:
{
lean_object* v___x_1673_; lean_object* v_bs_x27_1674_; lean_object* v___y_1676_; lean_object* v___x_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v___x_1673_ = lean_unsigned_to_nat(0u);
v_bs_x27_1674_ = lean_array_uset(v_bs_1665_, v_i_1664_, v___x_1673_);
v___x_1681_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_1682_ = lean_array_get_size(v_snd_1669_);
v___x_1683_ = lean_nat_dec_lt(v___x_1673_, v___x_1682_);
if (v___x_1683_ == 0)
{
lean_object* v___x_1685_; 
lean_dec(v_snd_1669_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 1, v___x_1681_);
v___x_1685_ = v___x_1671_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_fst_1668_);
lean_ctor_set(v_reuseFailAlloc_1686_, 1, v___x_1681_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
v___y_1676_ = v___x_1685_;
goto v___jp_1675_;
}
}
else
{
size_t v___x_1687_; size_t v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1687_ = ((size_t)0ULL);
v___x_1688_ = lean_usize_of_nat(v___x_1682_);
v___x_1689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_1669_, v___x_1687_, v___x_1688_, v___x_1681_);
lean_dec(v_snd_1669_);
if (v_isShared_1672_ == 0)
{
lean_ctor_set(v___x_1671_, 1, v___x_1689_);
v___x_1691_ = v___x_1671_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1692_; 
v_reuseFailAlloc_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1692_, 0, v_fst_1668_);
lean_ctor_set(v_reuseFailAlloc_1692_, 1, v___x_1689_);
v___x_1691_ = v_reuseFailAlloc_1692_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
v___y_1676_ = v___x_1691_;
goto v___jp_1675_;
}
}
v___jp_1675_:
{
size_t v___x_1677_; size_t v___x_1678_; lean_object* v___x_1679_; 
v___x_1677_ = ((size_t)1ULL);
v___x_1678_ = lean_usize_add(v_i_1664_, v___x_1677_);
v___x_1679_ = lean_array_uset(v_bs_x27_1674_, v_i_1664_, v___y_1676_);
v_i_1664_ = v___x_1678_;
v_bs_1665_ = v___x_1679_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0___boxed(lean_object* v_sz_1694_, lean_object* v_i_1695_, lean_object* v_bs_1696_){
_start:
{
size_t v_sz_boxed_1697_; size_t v_i_boxed_1698_; lean_object* v_res_1699_; 
v_sz_boxed_1697_ = lean_unbox_usize(v_sz_1694_);
lean_dec(v_sz_1694_);
v_i_boxed_1698_ = lean_unbox_usize(v_i_1695_);
lean_dec(v_i_1695_);
v_res_1699_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_boxed_1697_, v_i_boxed_1698_, v_bs_1696_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(size_t v_sz_1700_, size_t v_i_1701_, lean_object* v_bs_1702_){
_start:
{
uint8_t v___x_1703_; 
v___x_1703_ = lean_usize_dec_lt(v_i_1701_, v_sz_1700_);
if (v___x_1703_ == 0)
{
return v_bs_1702_;
}
else
{
lean_object* v_v_1704_; lean_object* v___x_1705_; lean_object* v_bs_x27_1706_; uint8_t v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; size_t v___x_1710_; size_t v___x_1711_; lean_object* v___x_1712_; 
v_v_1704_ = lean_array_uget(v_bs_1702_, v_i_1701_);
v___x_1705_ = lean_unsigned_to_nat(0u);
v_bs_x27_1706_ = lean_array_uset(v_bs_1702_, v_i_1701_, v___x_1705_);
v___x_1707_ = 0;
v___x_1708_ = lean_box(v___x_1707_);
v___x_1709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1709_, 0, v___x_1708_);
lean_ctor_set(v___x_1709_, 1, v_v_1704_);
v___x_1710_ = ((size_t)1ULL);
v___x_1711_ = lean_usize_add(v_i_1701_, v___x_1710_);
v___x_1712_ = lean_array_uset(v_bs_x27_1706_, v_i_1701_, v___x_1709_);
v_i_1701_ = v___x_1711_;
v_bs_1702_ = v___x_1712_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8___boxed(lean_object* v_sz_1714_, lean_object* v_i_1715_, lean_object* v_bs_1716_){
_start:
{
size_t v_sz_boxed_1717_; size_t v_i_boxed_1718_; lean_object* v_res_1719_; 
v_sz_boxed_1717_ = lean_unbox_usize(v_sz_1714_);
lean_dec(v_sz_1714_);
v_i_boxed_1718_ = lean_unbox_usize(v_i_1715_);
lean_dec(v_i_1715_);
v_res_1719_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_boxed_1717_, v_i_boxed_1718_, v_bs_1716_);
return v_res_1719_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(lean_object* v_x_1720_, lean_object* v_x_1721_){
_start:
{
if (lean_obj_tag(v_x_1721_) == 0)
{
lean_inc(v_x_1720_);
return v_x_1720_;
}
else
{
lean_object* v_key_1722_; lean_object* v_value_1723_; lean_object* v_tail_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v_key_1722_ = lean_ctor_get(v_x_1721_, 0);
v_value_1723_ = lean_ctor_get(v_x_1721_, 1);
v_tail_1724_ = lean_ctor_get(v_x_1721_, 2);
v___x_1725_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(v_x_1720_, v_tail_1724_);
lean_inc(v_value_1723_);
lean_inc(v_key_1722_);
v___x_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1726_, 0, v_key_1722_);
lean_ctor_set(v___x_1726_, 1, v_value_1723_);
v___x_1727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
lean_ctor_set(v___x_1727_, 1, v___x_1725_);
return v___x_1727_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7___boxed(lean_object* v_x_1728_, lean_object* v_x_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(v_x_1728_, v_x_1729_);
lean_dec(v_x_1729_);
lean_dec(v_x_1728_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8(lean_object* v_as_1731_, size_t v_i_1732_, size_t v_stop_1733_, lean_object* v_b_1734_){
_start:
{
uint8_t v___x_1735_; 
v___x_1735_ = lean_usize_dec_eq(v_i_1732_, v_stop_1733_);
if (v___x_1735_ == 0)
{
size_t v___x_1736_; size_t v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1736_ = ((size_t)1ULL);
v___x_1737_ = lean_usize_sub(v_i_1732_, v___x_1736_);
v___x_1738_ = lean_array_uget_borrowed(v_as_1731_, v___x_1737_);
v___x_1739_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(v_b_1734_, v___x_1738_);
lean_dec(v_b_1734_);
v_i_1732_ = v___x_1737_;
v_b_1734_ = v___x_1739_;
goto _start;
}
else
{
return v_b_1734_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8___boxed(lean_object* v_as_1741_, lean_object* v_i_1742_, lean_object* v_stop_1743_, lean_object* v_b_1744_){
_start:
{
size_t v_i_boxed_1745_; size_t v_stop_boxed_1746_; lean_object* v_res_1747_; 
v_i_boxed_1745_ = lean_unbox_usize(v_i_1742_);
lean_dec(v_i_1742_);
v_stop_boxed_1746_ = lean_unbox_usize(v_stop_1743_);
lean_dec(v_stop_1743_);
v_res_1747_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8(v_as_1741_, v_i_boxed_1745_, v_stop_boxed_1746_, v_b_1744_);
lean_dec_ref(v_as_1741_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4_spec__6(lean_object* v_left_1748_, lean_object* v_right_1749_, lean_object* v_pref_1750_){
_start:
{
lean_object* v_start_1751_; lean_object* v_stop_1752_; lean_object* v_i_1753_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v_start_1751_ = lean_ctor_get(v_left_1748_, 1);
v_stop_1752_ = lean_ctor_get(v_left_1748_, 2);
v_i_1753_ = lean_array_get_size(v_pref_1750_);
v___x_1759_ = lean_nat_sub(v_stop_1752_, v_start_1751_);
v___x_1760_ = lean_nat_dec_lt(v_i_1753_, v___x_1759_);
lean_dec(v___x_1759_);
if (v___x_1760_ == 0)
{
goto v___jp_1754_;
}
else
{
lean_object* v_start_1761_; lean_object* v_stop_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v_start_1761_ = lean_ctor_get(v_right_1749_, 1);
v_stop_1762_ = lean_ctor_get(v_right_1749_, 2);
v___x_1763_ = lean_nat_sub(v_stop_1762_, v_start_1761_);
v___x_1764_ = lean_nat_dec_lt(v_i_1753_, v___x_1763_);
lean_dec(v___x_1763_);
if (v___x_1764_ == 0)
{
goto v___jp_1754_;
}
else
{
lean_object* v___x_1765_; lean_object* v___x_1766_; uint8_t v___x_1767_; 
v___x_1765_ = l_Subarray_get___redArg(v_left_1748_, v_i_1753_);
v___x_1766_ = l_Subarray_get___redArg(v_right_1749_, v_i_1753_);
v___x_1767_ = lean_string_dec_eq(v___x_1765_, v___x_1766_);
lean_dec(v___x_1766_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
lean_dec(v___x_1765_);
v___x_1768_ = l_Subarray_drop___redArg(v_left_1748_, v_i_1753_);
v___x_1769_ = l_Subarray_drop___redArg(v_right_1749_, v_i_1753_);
v___x_1770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1770_, 0, v___x_1768_);
lean_ctor_set(v___x_1770_, 1, v___x_1769_);
v___x_1771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1771_, 0, v_pref_1750_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
return v___x_1771_;
}
else
{
lean_object* v___x_1772_; 
v___x_1772_ = lean_array_push(v_pref_1750_, v___x_1765_);
v_pref_1750_ = v___x_1772_;
goto _start;
}
}
}
v___jp_1754_:
{
lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1755_ = l_Subarray_drop___redArg(v_left_1748_, v_i_1753_);
v___x_1756_ = l_Subarray_drop___redArg(v_right_1749_, v_i_1753_);
v___x_1757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1757_, 0, v___x_1755_);
lean_ctor_set(v___x_1757_, 1, v___x_1756_);
v___x_1758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1758_, 0, v_pref_1750_);
lean_ctor_set(v___x_1758_, 1, v___x_1757_);
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4(lean_object* v_left_1774_, lean_object* v_right_1775_){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1776_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_1777_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4_spec__6(v_left_1774_, v_right_1775_, v___x_1776_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(lean_object* v_a_1778_, lean_object* v_x_1779_){
_start:
{
if (lean_obj_tag(v_x_1779_) == 0)
{
lean_object* v___x_1780_; 
v___x_1780_ = lean_box(0);
return v___x_1780_;
}
else
{
lean_object* v_key_1781_; lean_object* v_value_1782_; lean_object* v_tail_1783_; uint8_t v___x_1784_; 
v_key_1781_ = lean_ctor_get(v_x_1779_, 0);
v_value_1782_ = lean_ctor_get(v_x_1779_, 1);
v_tail_1783_ = lean_ctor_get(v_x_1779_, 2);
v___x_1784_ = lean_string_dec_eq(v_key_1781_, v_a_1778_);
if (v___x_1784_ == 0)
{
v_x_1779_ = v_tail_1783_;
goto _start;
}
else
{
lean_object* v___x_1786_; 
lean_inc(v_value_1782_);
v___x_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1786_, 0, v_value_1782_);
return v___x_1786_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg___boxed(lean_object* v_a_1787_, lean_object* v_x_1788_){
_start:
{
lean_object* v_res_1789_; 
v_res_1789_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(v_a_1787_, v_x_1788_);
lean_dec(v_x_1788_);
lean_dec_ref(v_a_1787_);
return v_res_1789_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(lean_object* v_m_1790_, lean_object* v_a_1791_){
_start:
{
lean_object* v_buckets_1792_; lean_object* v___x_1793_; uint64_t v___x_1794_; uint64_t v___x_1795_; uint64_t v___x_1796_; uint64_t v_fold_1797_; uint64_t v___x_1798_; uint64_t v___x_1799_; uint64_t v___x_1800_; size_t v___x_1801_; size_t v___x_1802_; size_t v___x_1803_; size_t v___x_1804_; size_t v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v_buckets_1792_ = lean_ctor_get(v_m_1790_, 1);
v___x_1793_ = lean_array_get_size(v_buckets_1792_);
v___x_1794_ = lean_string_hash(v_a_1791_);
v___x_1795_ = 32ULL;
v___x_1796_ = lean_uint64_shift_right(v___x_1794_, v___x_1795_);
v_fold_1797_ = lean_uint64_xor(v___x_1794_, v___x_1796_);
v___x_1798_ = 16ULL;
v___x_1799_ = lean_uint64_shift_right(v_fold_1797_, v___x_1798_);
v___x_1800_ = lean_uint64_xor(v_fold_1797_, v___x_1799_);
v___x_1801_ = lean_uint64_to_usize(v___x_1800_);
v___x_1802_ = lean_usize_of_nat(v___x_1793_);
v___x_1803_ = ((size_t)1ULL);
v___x_1804_ = lean_usize_sub(v___x_1802_, v___x_1803_);
v___x_1805_ = lean_usize_land(v___x_1801_, v___x_1804_);
v___x_1806_ = lean_array_uget_borrowed(v_buckets_1792_, v___x_1805_);
v___x_1807_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(v_a_1791_, v___x_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg___boxed(lean_object* v_m_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_m_1808_, v_a_1809_);
lean_dec_ref(v_a_1809_);
lean_dec_ref(v_m_1808_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29___redArg(lean_object* v_x_1811_, lean_object* v_x_1812_){
_start:
{
if (lean_obj_tag(v_x_1812_) == 0)
{
return v_x_1811_;
}
else
{
lean_object* v_key_1813_; lean_object* v_value_1814_; lean_object* v_tail_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1838_; 
v_key_1813_ = lean_ctor_get(v_x_1812_, 0);
v_value_1814_ = lean_ctor_get(v_x_1812_, 1);
v_tail_1815_ = lean_ctor_get(v_x_1812_, 2);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_x_1812_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1817_ = v_x_1812_;
v_isShared_1818_ = v_isSharedCheck_1838_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_tail_1815_);
lean_inc(v_value_1814_);
lean_inc(v_key_1813_);
lean_dec(v_x_1812_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1838_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; uint64_t v___x_1820_; uint64_t v___x_1821_; uint64_t v___x_1822_; uint64_t v_fold_1823_; uint64_t v___x_1824_; uint64_t v___x_1825_; uint64_t v___x_1826_; size_t v___x_1827_; size_t v___x_1828_; size_t v___x_1829_; size_t v___x_1830_; size_t v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1834_; 
v___x_1819_ = lean_array_get_size(v_x_1811_);
v___x_1820_ = lean_string_hash(v_key_1813_);
v___x_1821_ = 32ULL;
v___x_1822_ = lean_uint64_shift_right(v___x_1820_, v___x_1821_);
v_fold_1823_ = lean_uint64_xor(v___x_1820_, v___x_1822_);
v___x_1824_ = 16ULL;
v___x_1825_ = lean_uint64_shift_right(v_fold_1823_, v___x_1824_);
v___x_1826_ = lean_uint64_xor(v_fold_1823_, v___x_1825_);
v___x_1827_ = lean_uint64_to_usize(v___x_1826_);
v___x_1828_ = lean_usize_of_nat(v___x_1819_);
v___x_1829_ = ((size_t)1ULL);
v___x_1830_ = lean_usize_sub(v___x_1828_, v___x_1829_);
v___x_1831_ = lean_usize_land(v___x_1827_, v___x_1830_);
v___x_1832_ = lean_array_uget_borrowed(v_x_1811_, v___x_1831_);
lean_inc(v___x_1832_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 2, v___x_1832_);
v___x_1834_ = v___x_1817_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_key_1813_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_value_1814_);
lean_ctor_set(v_reuseFailAlloc_1837_, 2, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
lean_object* v___x_1835_; 
v___x_1835_ = lean_array_uset(v_x_1811_, v___x_1831_, v___x_1834_);
v_x_1811_ = v___x_1835_;
v_x_1812_ = v_tail_1815_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28___redArg(lean_object* v_i_1839_, lean_object* v_source_1840_, lean_object* v_target_1841_){
_start:
{
lean_object* v___x_1842_; uint8_t v___x_1843_; 
v___x_1842_ = lean_array_get_size(v_source_1840_);
v___x_1843_ = lean_nat_dec_lt(v_i_1839_, v___x_1842_);
if (v___x_1843_ == 0)
{
lean_dec_ref(v_source_1840_);
lean_dec(v_i_1839_);
return v_target_1841_;
}
else
{
lean_object* v_es_1844_; lean_object* v___x_1845_; lean_object* v_source_1846_; lean_object* v_target_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v_es_1844_ = lean_array_fget(v_source_1840_, v_i_1839_);
v___x_1845_ = lean_box(0);
v_source_1846_ = lean_array_fset(v_source_1840_, v_i_1839_, v___x_1845_);
v_target_1847_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29___redArg(v_target_1841_, v_es_1844_);
v___x_1848_ = lean_unsigned_to_nat(1u);
v___x_1849_ = lean_nat_add(v_i_1839_, v___x_1848_);
lean_dec(v_i_1839_);
v_i_1839_ = v___x_1849_;
v_source_1840_ = v_source_1846_;
v_target_1841_ = v_target_1847_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23___redArg(lean_object* v_data_1851_){
_start:
{
lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v_nbuckets_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1852_ = lean_array_get_size(v_data_1851_);
v___x_1853_ = lean_unsigned_to_nat(2u);
v_nbuckets_1854_ = lean_nat_mul(v___x_1852_, v___x_1853_);
v___x_1855_ = lean_unsigned_to_nat(0u);
v___x_1856_ = lean_box(0);
v___x_1857_ = lean_mk_array(v_nbuckets_1854_, v___x_1856_);
v___x_1858_ = lean_array_propagate_mark(v_data_1851_, v___x_1857_);
v___x_1859_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28___redArg(v___x_1855_, v_data_1851_, v___x_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(lean_object* v_a_1860_, lean_object* v_b_1861_, lean_object* v_x_1862_){
_start:
{
if (lean_obj_tag(v_x_1862_) == 0)
{
lean_dec(v_b_1861_);
lean_dec_ref(v_a_1860_);
return v_x_1862_;
}
else
{
lean_object* v_key_1863_; lean_object* v_value_1864_; lean_object* v_tail_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1877_; 
v_key_1863_ = lean_ctor_get(v_x_1862_, 0);
v_value_1864_ = lean_ctor_get(v_x_1862_, 1);
v_tail_1865_ = lean_ctor_get(v_x_1862_, 2);
v_isSharedCheck_1877_ = !lean_is_exclusive(v_x_1862_);
if (v_isSharedCheck_1877_ == 0)
{
v___x_1867_ = v_x_1862_;
v_isShared_1868_ = v_isSharedCheck_1877_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_tail_1865_);
lean_inc(v_value_1864_);
lean_inc(v_key_1863_);
lean_dec(v_x_1862_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1877_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
uint8_t v___x_1869_; 
v___x_1869_ = lean_string_dec_eq(v_key_1863_, v_a_1860_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; lean_object* v___x_1872_; 
v___x_1870_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(v_a_1860_, v_b_1861_, v_tail_1865_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 2, v___x_1870_);
v___x_1872_ = v___x_1867_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_key_1863_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v_value_1864_);
lean_ctor_set(v_reuseFailAlloc_1873_, 2, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
else
{
lean_object* v___x_1875_; 
lean_dec(v_value_1864_);
lean_dec(v_key_1863_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 1, v_b_1861_);
lean_ctor_set(v___x_1867_, 0, v_a_1860_);
v___x_1875_ = v___x_1867_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_a_1860_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v_b_1861_);
lean_ctor_set(v_reuseFailAlloc_1876_, 2, v_tail_1865_);
v___x_1875_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
return v___x_1875_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(lean_object* v_a_1878_, lean_object* v_x_1879_){
_start:
{
if (lean_obj_tag(v_x_1879_) == 0)
{
uint8_t v___x_1880_; 
v___x_1880_ = 0;
return v___x_1880_;
}
else
{
lean_object* v_key_1881_; lean_object* v_tail_1882_; uint8_t v___x_1883_; 
v_key_1881_ = lean_ctor_get(v_x_1879_, 0);
v_tail_1882_ = lean_ctor_get(v_x_1879_, 2);
v___x_1883_ = lean_string_dec_eq(v_key_1881_, v_a_1878_);
if (v___x_1883_ == 0)
{
v_x_1879_ = v_tail_1882_;
goto _start;
}
else
{
return v___x_1883_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg___boxed(lean_object* v_a_1885_, lean_object* v_x_1886_){
_start:
{
uint8_t v_res_1887_; lean_object* v_r_1888_; 
v_res_1887_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(v_a_1885_, v_x_1886_);
lean_dec(v_x_1886_);
lean_dec_ref(v_a_1885_);
v_r_1888_ = lean_box(v_res_1887_);
return v_r_1888_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(lean_object* v_m_1889_, lean_object* v_a_1890_, lean_object* v_b_1891_){
_start:
{
lean_object* v_size_1892_; lean_object* v_buckets_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1936_; 
v_size_1892_ = lean_ctor_get(v_m_1889_, 0);
v_buckets_1893_ = lean_ctor_get(v_m_1889_, 1);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_m_1889_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1895_ = v_m_1889_;
v_isShared_1896_ = v_isSharedCheck_1936_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_buckets_1893_);
lean_inc(v_size_1892_);
lean_dec(v_m_1889_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1936_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1897_; uint64_t v___x_1898_; uint64_t v___x_1899_; uint64_t v___x_1900_; uint64_t v_fold_1901_; uint64_t v___x_1902_; uint64_t v___x_1903_; uint64_t v___x_1904_; size_t v___x_1905_; size_t v___x_1906_; size_t v___x_1907_; size_t v___x_1908_; size_t v___x_1909_; lean_object* v_bkt_1910_; uint8_t v___x_1911_; 
v___x_1897_ = lean_array_get_size(v_buckets_1893_);
v___x_1898_ = lean_string_hash(v_a_1890_);
v___x_1899_ = 32ULL;
v___x_1900_ = lean_uint64_shift_right(v___x_1898_, v___x_1899_);
v_fold_1901_ = lean_uint64_xor(v___x_1898_, v___x_1900_);
v___x_1902_ = 16ULL;
v___x_1903_ = lean_uint64_shift_right(v_fold_1901_, v___x_1902_);
v___x_1904_ = lean_uint64_xor(v_fold_1901_, v___x_1903_);
v___x_1905_ = lean_uint64_to_usize(v___x_1904_);
v___x_1906_ = lean_usize_of_nat(v___x_1897_);
v___x_1907_ = ((size_t)1ULL);
v___x_1908_ = lean_usize_sub(v___x_1906_, v___x_1907_);
v___x_1909_ = lean_usize_land(v___x_1905_, v___x_1908_);
v_bkt_1910_ = lean_array_uget_borrowed(v_buckets_1893_, v___x_1909_);
v___x_1911_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(v_a_1890_, v_bkt_1910_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; lean_object* v_size_x27_1913_; lean_object* v___x_1914_; lean_object* v_buckets_x27_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; 
v___x_1912_ = lean_unsigned_to_nat(1u);
v_size_x27_1913_ = lean_nat_add(v_size_1892_, v___x_1912_);
lean_dec(v_size_1892_);
lean_inc(v_bkt_1910_);
v___x_1914_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1914_, 0, v_a_1890_);
lean_ctor_set(v___x_1914_, 1, v_b_1891_);
lean_ctor_set(v___x_1914_, 2, v_bkt_1910_);
v_buckets_x27_1915_ = lean_array_uset(v_buckets_1893_, v___x_1909_, v___x_1914_);
v___x_1916_ = lean_unsigned_to_nat(4u);
v___x_1917_ = lean_nat_mul(v_size_x27_1913_, v___x_1916_);
v___x_1918_ = lean_unsigned_to_nat(3u);
v___x_1919_ = lean_nat_div(v___x_1917_, v___x_1918_);
lean_dec(v___x_1917_);
v___x_1920_ = lean_array_get_size(v_buckets_x27_1915_);
v___x_1921_ = lean_nat_dec_le(v___x_1919_, v___x_1920_);
lean_dec(v___x_1919_);
if (v___x_1921_ == 0)
{
lean_object* v_val_1922_; lean_object* v___x_1924_; 
v_val_1922_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23___redArg(v_buckets_x27_1915_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 1, v_val_1922_);
lean_ctor_set(v___x_1895_, 0, v_size_x27_1913_);
v___x_1924_ = v___x_1895_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_size_x27_1913_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_val_1922_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
else
{
lean_object* v___x_1927_; 
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 1, v_buckets_x27_1915_);
lean_ctor_set(v___x_1895_, 0, v_size_x27_1913_);
v___x_1927_ = v___x_1895_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_size_x27_1913_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_buckets_x27_1915_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
else
{
lean_object* v___x_1929_; lean_object* v_buckets_x27_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1934_; 
lean_inc(v_bkt_1910_);
v___x_1929_ = lean_box(0);
v_buckets_x27_1930_ = lean_array_uset(v_buckets_1893_, v___x_1909_, v___x_1929_);
v___x_1931_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(v_a_1890_, v_b_1891_, v_bkt_1910_);
v___x_1932_ = lean_array_uset(v_buckets_x27_1930_, v___x_1909_, v___x_1931_);
if (v_isShared_1896_ == 0)
{
lean_ctor_set(v___x_1895_, 1, v___x_1932_);
v___x_1934_ = v___x_1895_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_size_1892_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v___x_1932_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___redArg(lean_object* v_histogram_1937_, lean_object* v_index_1938_, lean_object* v_val_1939_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_histogram_1937_, v_val_1939_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = lean_box(0);
v___x_1943_ = lean_unsigned_to_nat(1u);
v___x_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1944_, 0, v_index_1938_);
v___x_1945_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1941_);
lean_ctor_set(v___x_1945_, 1, v___x_1942_);
lean_ctor_set(v___x_1945_, 2, v___x_1943_);
lean_ctor_set(v___x_1945_, 3, v___x_1944_);
v___x_1946_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_1937_, v_val_1939_, v___x_1945_);
return v___x_1946_;
}
else
{
lean_object* v_val_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1968_; 
v_val_1947_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1949_ = v___x_1940_;
v_isShared_1950_ = v_isSharedCheck_1968_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_val_1947_);
lean_dec(v___x_1940_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1968_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v_leftCount_1951_; lean_object* v_leftIndex_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1965_; 
v_leftCount_1951_ = lean_ctor_get(v_val_1947_, 0);
v_leftIndex_1952_ = lean_ctor_get(v_val_1947_, 1);
v_isSharedCheck_1965_ = !lean_is_exclusive(v_val_1947_);
if (v_isSharedCheck_1965_ == 0)
{
lean_object* v_unused_1966_; lean_object* v_unused_1967_; 
v_unused_1966_ = lean_ctor_get(v_val_1947_, 3);
lean_dec(v_unused_1966_);
v_unused_1967_ = lean_ctor_get(v_val_1947_, 2);
lean_dec(v_unused_1967_);
v___x_1954_ = v_val_1947_;
v_isShared_1955_ = v_isSharedCheck_1965_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_leftIndex_1952_);
lean_inc(v_leftCount_1951_);
lean_dec(v_val_1947_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1965_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1959_; 
v___x_1956_ = lean_unsigned_to_nat(1u);
v___x_1957_ = lean_nat_add(v_leftCount_1951_, v___x_1956_);
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v_index_1938_);
v___x_1959_ = v___x_1949_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1964_; 
v_reuseFailAlloc_1964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_index_1938_);
v___x_1959_ = v_reuseFailAlloc_1964_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
lean_object* v___x_1961_; 
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 3, v___x_1959_);
lean_ctor_set(v___x_1954_, 2, v___x_1957_);
v___x_1961_ = v___x_1954_;
goto v_reusejp_1960_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_leftCount_1951_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_leftIndex_1952_);
lean_ctor_set(v_reuseFailAlloc_1963_, 2, v___x_1957_);
lean_ctor_set(v_reuseFailAlloc_1963_, 3, v___x_1959_);
v___x_1961_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1960_;
}
v_reusejp_1960_:
{
lean_object* v___x_1962_; 
v___x_1962_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_1937_, v_val_1939_, v___x_1961_);
return v___x_1962_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(lean_object* v_upperBound_1969_, lean_object* v___x_1970_, lean_object* v_fst_1971_, lean_object* v___x_1972_, lean_object* v_a_1973_, lean_object* v_b_1974_){
_start:
{
uint8_t v___x_1975_; 
v___x_1975_ = lean_nat_dec_lt(v_a_1973_, v_upperBound_1969_);
if (v___x_1975_ == 0)
{
lean_dec(v_a_1973_);
return v_b_1974_;
}
else
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1976_ = l_Subarray_get___redArg(v_fst_1971_, v_a_1973_);
lean_inc(v_a_1973_);
v___x_1977_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___redArg(v_b_1974_, v_a_1973_, v___x_1976_);
v___x_1978_ = lean_unsigned_to_nat(1u);
v___x_1979_ = lean_nat_add(v_a_1973_, v___x_1978_);
lean_dec(v_a_1973_);
v_a_1973_ = v___x_1979_;
v_b_1974_ = v___x_1977_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg___boxed(lean_object* v_upperBound_1981_, lean_object* v___x_1982_, lean_object* v_fst_1983_, lean_object* v___x_1984_, lean_object* v_a_1985_, lean_object* v_b_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(v_upperBound_1981_, v___x_1982_, v_fst_1983_, v___x_1984_, v_a_1985_, v_b_1986_);
lean_dec(v___x_1984_);
lean_dec_ref(v_fst_1983_);
lean_dec(v___x_1982_);
lean_dec(v_upperBound_1981_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(lean_object* v_as_x27_1988_, lean_object* v_b_1989_){
_start:
{
if (lean_obj_tag(v_as_x27_1988_) == 0)
{
return v_b_1989_;
}
else
{
lean_object* v_head_1990_; lean_object* v_snd_1991_; lean_object* v_leftIndex_1992_; 
v_head_1990_ = lean_ctor_get(v_as_x27_1988_, 0);
v_snd_1991_ = lean_ctor_get(v_head_1990_, 1);
v_leftIndex_1992_ = lean_ctor_get(v_snd_1991_, 1);
if (lean_obj_tag(v_leftIndex_1992_) == 1)
{
lean_object* v_rightIndex_1993_; 
v_rightIndex_1993_ = lean_ctor_get(v_snd_1991_, 3);
if (lean_obj_tag(v_rightIndex_1993_) == 1)
{
if (lean_obj_tag(v_b_1989_) == 0)
{
lean_object* v_tail_1994_; lean_object* v_fst_1995_; lean_object* v_leftCount_1996_; lean_object* v_rightCount_1997_; lean_object* v_val_1998_; lean_object* v_val_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v_tail_1994_ = lean_ctor_get(v_as_x27_1988_, 1);
v_fst_1995_ = lean_ctor_get(v_head_1990_, 0);
v_leftCount_1996_ = lean_ctor_get(v_snd_1991_, 0);
v_rightCount_1997_ = lean_ctor_get(v_snd_1991_, 2);
v_val_1998_ = lean_ctor_get(v_leftIndex_1992_, 0);
v_val_1999_ = lean_ctor_get(v_rightIndex_1993_, 0);
v___x_2000_ = lean_nat_add(v_leftCount_1996_, v_rightCount_1997_);
lean_inc(v_val_1999_);
lean_inc(v_val_1998_);
v___x_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2001_, 0, v_val_1998_);
lean_ctor_set(v___x_2001_, 1, v_val_1999_);
lean_inc(v_fst_1995_);
v___x_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2002_, 0, v_fst_1995_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
v___x_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2000_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
v___x_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
v_as_x27_1988_ = v_tail_1994_;
v_b_1989_ = v___x_2004_;
goto _start;
}
else
{
lean_object* v_val_2006_; lean_object* v_tail_2007_; lean_object* v_fst_2008_; lean_object* v_leftCount_2009_; lean_object* v_rightCount_2010_; lean_object* v_val_2011_; lean_object* v_val_2012_; lean_object* v_fst_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2034_; 
v_val_2006_ = lean_ctor_get(v_b_1989_, 0);
lean_inc(v_val_2006_);
v_tail_2007_ = lean_ctor_get(v_as_x27_1988_, 1);
v_fst_2008_ = lean_ctor_get(v_head_1990_, 0);
v_leftCount_2009_ = lean_ctor_get(v_snd_1991_, 0);
v_rightCount_2010_ = lean_ctor_get(v_snd_1991_, 2);
v_val_2011_ = lean_ctor_get(v_leftIndex_1992_, 0);
v_val_2012_ = lean_ctor_get(v_rightIndex_1993_, 0);
v_fst_2013_ = lean_ctor_get(v_val_2006_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v_val_2006_);
if (v_isSharedCheck_2034_ == 0)
{
lean_object* v_unused_2035_; 
v_unused_2035_ = lean_ctor_get(v_val_2006_, 1);
lean_dec(v_unused_2035_);
v___x_2015_ = v_val_2006_;
v_isShared_2016_ = v_isSharedCheck_2034_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_fst_2013_);
lean_dec(v_val_2006_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2034_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = lean_nat_add(v_leftCount_2009_, v_rightCount_2010_);
v___x_2018_ = lean_nat_dec_lt(v___x_2017_, v_fst_2013_);
lean_dec(v_fst_2013_);
if (v___x_2018_ == 0)
{
lean_dec(v___x_2017_);
lean_del_object(v___x_2015_);
v_as_x27_1988_ = v_tail_2007_;
goto _start;
}
else
{
lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2032_; 
v_isSharedCheck_2032_ = !lean_is_exclusive(v_b_1989_);
if (v_isSharedCheck_2032_ == 0)
{
lean_object* v_unused_2033_; 
v_unused_2033_ = lean_ctor_get(v_b_1989_, 0);
lean_dec(v_unused_2033_);
v___x_2021_ = v_b_1989_;
v_isShared_2022_ = v_isSharedCheck_2032_;
goto v_resetjp_2020_;
}
else
{
lean_dec(v_b_1989_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2032_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2024_; 
lean_inc(v_val_2012_);
lean_inc(v_val_2011_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 1, v_val_2012_);
lean_ctor_set(v___x_2015_, 0, v_val_2011_);
v___x_2024_ = v___x_2015_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_val_2011_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v_val_2012_);
v___x_2024_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2028_; 
lean_inc(v_fst_2008_);
v___x_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2025_, 0, v_fst_2008_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
v___x_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2017_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set(v___x_2021_, 0, v___x_2026_);
v___x_2028_ = v___x_2021_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
v_as_x27_1988_ = v_tail_2007_;
v_b_1989_ = v___x_2028_;
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
lean_object* v_tail_2036_; 
v_tail_2036_ = lean_ctor_get(v_as_x27_1988_, 1);
v_as_x27_1988_ = v_tail_2036_;
goto _start;
}
}
else
{
lean_object* v_tail_2038_; 
v_tail_2038_ = lean_ctor_get(v_as_x27_1988_, 1);
v_as_x27_1988_ = v_tail_2038_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_as_x27_2040_, lean_object* v_b_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(v_as_x27_2040_, v_b_2041_);
lean_dec(v_as_x27_2040_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(lean_object* v_a_2043_, lean_object* v_b_2044_){
_start:
{
lean_object* v_array_2045_; lean_object* v_start_2046_; lean_object* v_stop_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2060_; 
v_array_2045_ = lean_ctor_get(v_a_2043_, 0);
v_start_2046_ = lean_ctor_get(v_a_2043_, 1);
v_stop_2047_ = lean_ctor_get(v_a_2043_, 2);
v_isSharedCheck_2060_ = !lean_is_exclusive(v_a_2043_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2049_ = v_a_2043_;
v_isShared_2050_ = v_isSharedCheck_2060_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_stop_2047_);
lean_inc(v_start_2046_);
lean_inc(v_array_2045_);
lean_dec(v_a_2043_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2060_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
uint8_t v___x_2051_; 
v___x_2051_ = lean_nat_dec_lt(v_start_2046_, v_stop_2047_);
if (v___x_2051_ == 0)
{
lean_del_object(v___x_2049_);
lean_dec(v_stop_2047_);
lean_dec(v_start_2046_);
lean_dec_ref(v_array_2045_);
return v_b_2044_;
}
else
{
lean_object* v___x_2052_; lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2052_ = lean_unsigned_to_nat(1u);
v___x_2053_ = lean_nat_add(v_start_2046_, v___x_2052_);
lean_inc_ref(v_array_2045_);
if (v_isShared_2050_ == 0)
{
lean_ctor_set(v___x_2049_, 1, v___x_2053_);
v___x_2055_ = v___x_2049_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_array_2045_);
lean_ctor_set(v_reuseFailAlloc_2059_, 1, v___x_2053_);
lean_ctor_set(v_reuseFailAlloc_2059_, 2, v_stop_2047_);
v___x_2055_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = lean_array_fget(v_array_2045_, v_start_2046_);
lean_dec(v_start_2046_);
lean_dec_ref(v_array_2045_);
v___x_2057_ = lean_array_push(v_b_2044_, v___x_2056_);
v_a_2043_ = v___x_2055_;
v_b_2044_ = v___x_2057_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8(lean_object* v_left_2061_, lean_object* v_right_2062_, lean_object* v_i_2063_){
_start:
{
lean_object* v_start_2064_; lean_object* v_stop_2065_; lean_object* v___x_2066_; uint8_t v___x_2080_; 
v_start_2064_ = lean_ctor_get(v_left_2061_, 1);
v_stop_2065_ = lean_ctor_get(v_left_2061_, 2);
v___x_2066_ = lean_nat_sub(v_stop_2065_, v_start_2064_);
v___x_2080_ = lean_nat_dec_lt(v_i_2063_, v___x_2066_);
if (v___x_2080_ == 0)
{
goto v___jp_2067_;
}
else
{
lean_object* v_start_2081_; lean_object* v_stop_2082_; lean_object* v___x_2083_; uint8_t v___x_2084_; 
v_start_2081_ = lean_ctor_get(v_right_2062_, 1);
v_stop_2082_ = lean_ctor_get(v_right_2062_, 2);
v___x_2083_ = lean_nat_sub(v_stop_2082_, v_start_2081_);
v___x_2084_ = lean_nat_dec_lt(v_i_2063_, v___x_2083_);
if (v___x_2084_ == 0)
{
lean_dec(v___x_2083_);
goto v___jp_2067_;
}
else
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2085_ = lean_nat_sub(v___x_2066_, v_i_2063_);
lean_dec(v___x_2066_);
v___x_2086_ = lean_unsigned_to_nat(1u);
v___x_2087_ = lean_nat_sub(v___x_2085_, v___x_2086_);
v___x_2088_ = l_Subarray_get___redArg(v_left_2061_, v___x_2087_);
lean_dec(v___x_2087_);
v___x_2089_ = lean_nat_sub(v___x_2083_, v_i_2063_);
lean_dec(v___x_2083_);
v___x_2090_ = lean_nat_sub(v___x_2089_, v___x_2086_);
v___x_2091_ = l_Subarray_get___redArg(v_right_2062_, v___x_2090_);
lean_dec(v___x_2090_);
v___x_2092_ = lean_string_dec_eq(v___x_2088_, v___x_2091_);
lean_dec(v___x_2091_);
lean_dec(v___x_2088_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
lean_dec(v_i_2063_);
lean_inc_ref(v_left_2061_);
v___x_2093_ = l_Subarray_take___redArg(v_left_2061_, v___x_2085_);
v___x_2094_ = l_Subarray_take___redArg(v_right_2062_, v___x_2089_);
lean_dec(v___x_2089_);
v___x_2095_ = l_Subarray_drop___redArg(v_left_2061_, v___x_2085_);
lean_dec(v___x_2085_);
v___x_2096_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2097_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(v___x_2095_, v___x_2096_);
v___x_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2098_, 0, v___x_2094_);
lean_ctor_set(v___x_2098_, 1, v___x_2097_);
v___x_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2093_);
lean_ctor_set(v___x_2099_, 1, v___x_2098_);
return v___x_2099_;
}
else
{
lean_object* v___x_2100_; 
lean_dec(v___x_2089_);
lean_dec(v___x_2085_);
v___x_2100_ = lean_nat_add(v_i_2063_, v___x_2086_);
lean_dec(v_i_2063_);
v_i_2063_ = v___x_2100_;
goto _start;
}
}
}
v___jp_2067_:
{
lean_object* v_start_2068_; lean_object* v_stop_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v_start_2068_ = lean_ctor_get(v_right_2062_, 1);
v_stop_2069_ = lean_ctor_get(v_right_2062_, 2);
v___x_2070_ = lean_nat_sub(v___x_2066_, v_i_2063_);
lean_dec(v___x_2066_);
lean_inc_ref(v_left_2061_);
v___x_2071_ = l_Subarray_take___redArg(v_left_2061_, v___x_2070_);
v___x_2072_ = lean_nat_sub(v_stop_2069_, v_start_2068_);
v___x_2073_ = lean_nat_sub(v___x_2072_, v_i_2063_);
lean_dec(v_i_2063_);
lean_dec(v___x_2072_);
v___x_2074_ = l_Subarray_take___redArg(v_right_2062_, v___x_2073_);
lean_dec(v___x_2073_);
v___x_2075_ = l_Subarray_drop___redArg(v_left_2061_, v___x_2070_);
lean_dec(v___x_2070_);
v___x_2076_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2077_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(v___x_2075_, v___x_2076_);
v___x_2078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2078_, 0, v___x_2074_);
lean_ctor_set(v___x_2078_, 1, v___x_2077_);
v___x_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2071_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
return v___x_2079_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5(lean_object* v_left_2102_, lean_object* v_right_2103_){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2104_ = lean_unsigned_to_nat(0u);
v___x_2105_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8(v_left_2102_, v_right_2103_, v___x_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___redArg(lean_object* v_histogram_2106_, lean_object* v_index_2107_, lean_object* v_val_2108_){
_start:
{
lean_object* v___x_2109_; 
v___x_2109_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_histogram_2106_, v_val_2108_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2110_ = lean_unsigned_to_nat(1u);
v___x_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2111_, 0, v_index_2107_);
v___x_2112_ = lean_unsigned_to_nat(0u);
v___x_2113_ = lean_box(0);
v___x_2114_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2110_);
lean_ctor_set(v___x_2114_, 1, v___x_2111_);
lean_ctor_set(v___x_2114_, 2, v___x_2112_);
lean_ctor_set(v___x_2114_, 3, v___x_2113_);
v___x_2115_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_2106_, v_val_2108_, v___x_2114_);
return v___x_2115_;
}
else
{
lean_object* v_val_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2137_; 
v_val_2116_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2118_ = v___x_2109_;
v_isShared_2119_ = v_isSharedCheck_2137_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_val_2116_);
lean_dec(v___x_2109_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2137_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v_leftCount_2120_; lean_object* v_rightCount_2121_; lean_object* v_rightIndex_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2135_; 
v_leftCount_2120_ = lean_ctor_get(v_val_2116_, 0);
v_rightCount_2121_ = lean_ctor_get(v_val_2116_, 2);
v_rightIndex_2122_ = lean_ctor_get(v_val_2116_, 3);
v_isSharedCheck_2135_ = !lean_is_exclusive(v_val_2116_);
if (v_isSharedCheck_2135_ == 0)
{
lean_object* v_unused_2136_; 
v_unused_2136_ = lean_ctor_get(v_val_2116_, 1);
lean_dec(v_unused_2136_);
v___x_2124_ = v_val_2116_;
v_isShared_2125_ = v_isSharedCheck_2135_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_rightIndex_2122_);
lean_inc(v_rightCount_2121_);
lean_inc(v_leftCount_2120_);
lean_dec(v_val_2116_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2135_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2126_ = lean_unsigned_to_nat(1u);
v___x_2127_ = lean_nat_add(v_leftCount_2120_, v___x_2126_);
lean_dec(v_leftCount_2120_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v_index_2107_);
v___x_2129_ = v___x_2118_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_index_2107_);
v___x_2129_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2131_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 1, v___x_2129_);
lean_ctor_set(v___x_2124_, 0, v___x_2127_);
v___x_2131_ = v___x_2124_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2127_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v___x_2129_);
lean_ctor_set(v_reuseFailAlloc_2133_, 2, v_rightCount_2121_);
lean_ctor_set(v_reuseFailAlloc_2133_, 3, v_rightIndex_2122_);
v___x_2131_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_2106_, v_val_2108_, v___x_2131_);
return v___x_2132_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(lean_object* v_upperBound_2138_, lean_object* v_fst_2139_, lean_object* v___x_2140_, lean_object* v_fst_2141_, lean_object* v_a_2142_, lean_object* v_b_2143_){
_start:
{
uint8_t v___x_2144_; 
v___x_2144_ = lean_nat_dec_lt(v_a_2142_, v_upperBound_2138_);
if (v___x_2144_ == 0)
{
lean_dec(v_a_2142_);
return v_b_2143_;
}
else
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2145_ = l_Subarray_get___redArg(v_fst_2141_, v_a_2142_);
lean_inc(v_a_2142_);
v___x_2146_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___redArg(v_b_2143_, v_a_2142_, v___x_2145_);
v___x_2147_ = lean_unsigned_to_nat(1u);
v___x_2148_ = lean_nat_add(v_a_2142_, v___x_2147_);
lean_dec(v_a_2142_);
v_a_2142_ = v___x_2148_;
v_b_2143_ = v___x_2146_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg___boxed(lean_object* v_upperBound_2150_, lean_object* v_fst_2151_, lean_object* v___x_2152_, lean_object* v_fst_2153_, lean_object* v_a_2154_, lean_object* v_b_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(v_upperBound_2150_, v_fst_2151_, v___x_2152_, v_fst_2153_, v_a_2154_, v_b_2155_);
lean_dec_ref(v_fst_2153_);
lean_dec(v___x_2152_);
lean_dec_ref(v_fst_2151_);
lean_dec(v_upperBound_2150_);
return v_res_2156_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2157_ = lean_box(0);
v___x_2158_ = lean_unsigned_to_nat(16u);
v___x_2159_ = lean_mk_array(v___x_2158_, v___x_2157_);
return v___x_2159_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v_hist_2162_; 
v___x_2160_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0);
v___x_2161_ = lean_unsigned_to_nat(0u);
v_hist_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_2162_, 0, v___x_2161_);
lean_ctor_set(v_hist_2162_, 1, v___x_2160_);
return v_hist_2162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(lean_object* v_left_2163_, lean_object* v_right_2164_){
_start:
{
lean_object* v___x_2165_; lean_object* v_snd_2166_; lean_object* v_fst_2167_; lean_object* v_fst_2168_; lean_object* v_snd_2169_; lean_object* v___x_2170_; lean_object* v_snd_2171_; lean_object* v_fst_2172_; lean_object* v_fst_2173_; lean_object* v_snd_2174_; lean_object* v_start_2175_; lean_object* v_stop_2176_; lean_object* v___x_2177_; lean_object* v_hist_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v_start_2181_; lean_object* v_stop_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v_buckets_2185_; lean_object* v___x_2186_; lean_object* v___y_2188_; lean_object* v___x_2214_; lean_object* v___x_2215_; uint8_t v___x_2216_; 
v___x_2165_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4(v_left_2163_, v_right_2164_);
v_snd_2166_ = lean_ctor_get(v___x_2165_, 1);
lean_inc(v_snd_2166_);
v_fst_2167_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_fst_2167_);
lean_dec_ref(v___x_2165_);
v_fst_2168_ = lean_ctor_get(v_snd_2166_, 0);
lean_inc(v_fst_2168_);
v_snd_2169_ = lean_ctor_get(v_snd_2166_, 1);
lean_inc(v_snd_2169_);
lean_dec(v_snd_2166_);
v___x_2170_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5(v_fst_2168_, v_snd_2169_);
v_snd_2171_ = lean_ctor_get(v___x_2170_, 1);
lean_inc(v_snd_2171_);
v_fst_2172_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_fst_2172_);
lean_dec_ref(v___x_2170_);
v_fst_2173_ = lean_ctor_get(v_snd_2171_, 0);
lean_inc(v_fst_2173_);
v_snd_2174_ = lean_ctor_get(v_snd_2171_, 1);
lean_inc(v_snd_2174_);
lean_dec(v_snd_2171_);
v_start_2175_ = lean_ctor_get(v_fst_2172_, 1);
v_stop_2176_ = lean_ctor_get(v_fst_2172_, 2);
v___x_2177_ = lean_unsigned_to_nat(0u);
v_hist_2178_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1);
v___x_2179_ = lean_nat_sub(v_stop_2176_, v_start_2175_);
v___x_2180_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(v___x_2179_, v_fst_2173_, v___x_2179_, v_fst_2172_, v___x_2177_, v_hist_2178_);
v_start_2181_ = lean_ctor_get(v_fst_2173_, 1);
v_stop_2182_ = lean_ctor_get(v_fst_2173_, 2);
v___x_2183_ = lean_nat_sub(v_stop_2182_, v_start_2181_);
v___x_2184_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(v___x_2183_, v___x_2183_, v_fst_2173_, v___x_2179_, v___x_2177_, v___x_2180_);
lean_dec(v___x_2179_);
lean_dec(v___x_2183_);
v_buckets_2185_ = lean_ctor_get(v___x_2184_, 1);
lean_inc_ref(v_buckets_2185_);
lean_dec_ref(v___x_2184_);
v___x_2186_ = lean_box(0);
v___x_2214_ = lean_box(0);
v___x_2215_ = lean_array_get_size(v_buckets_2185_);
v___x_2216_ = lean_nat_dec_lt(v___x_2177_, v___x_2215_);
if (v___x_2216_ == 0)
{
lean_dec_ref(v_buckets_2185_);
v___y_2188_ = v___x_2214_;
goto v___jp_2187_;
}
else
{
size_t v___x_2217_; size_t v___x_2218_; lean_object* v___x_2219_; 
v___x_2217_ = lean_usize_of_nat(v___x_2215_);
v___x_2218_ = ((size_t)0ULL);
v___x_2219_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8(v_buckets_2185_, v___x_2217_, v___x_2218_, v___x_2214_);
lean_dec_ref(v_buckets_2185_);
v___y_2188_ = v___x_2219_;
goto v___jp_2187_;
}
v___jp_2187_:
{
lean_object* v___x_2189_; 
v___x_2189_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(v___y_2188_, v___x_2186_);
lean_dec(v___y_2188_);
if (lean_obj_tag(v___x_2189_) == 1)
{
lean_object* v_val_2190_; lean_object* v_snd_2191_; lean_object* v_snd_2192_; lean_object* v_fst_2193_; lean_object* v_fst_2194_; lean_object* v_snd_2195_; lean_object* v___x_2196_; lean_object* v_fst_2197_; lean_object* v_snd_2198_; lean_object* v___x_2199_; lean_object* v_fst_2200_; lean_object* v_snd_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v_val_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_val_2190_);
lean_dec_ref_known(v___x_2189_, 1);
v_snd_2191_ = lean_ctor_get(v_val_2190_, 1);
lean_inc(v_snd_2191_);
lean_dec(v_val_2190_);
v_snd_2192_ = lean_ctor_get(v_snd_2191_, 1);
lean_inc(v_snd_2192_);
v_fst_2193_ = lean_ctor_get(v_snd_2191_, 0);
lean_inc(v_fst_2193_);
lean_dec(v_snd_2191_);
v_fst_2194_ = lean_ctor_get(v_snd_2192_, 0);
lean_inc(v_fst_2194_);
v_snd_2195_ = lean_ctor_get(v_snd_2192_, 1);
lean_inc(v_snd_2195_);
lean_dec(v_snd_2192_);
v___x_2196_ = l_Subarray_split___redArg(v_fst_2172_, v_fst_2194_);
lean_dec(v_fst_2194_);
v_fst_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_fst_2197_);
v_snd_2198_ = lean_ctor_get(v___x_2196_, 1);
lean_inc(v_snd_2198_);
lean_dec_ref(v___x_2196_);
v___x_2199_ = l_Subarray_split___redArg(v_fst_2173_, v_snd_2195_);
lean_dec(v_snd_2195_);
v_fst_2200_ = lean_ctor_get(v___x_2199_, 0);
lean_inc(v_fst_2200_);
v_snd_2201_ = lean_ctor_get(v___x_2199_, 1);
lean_inc(v_snd_2201_);
lean_dec_ref(v___x_2199_);
v___x_2202_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v_fst_2197_, v_fst_2200_);
v___x_2203_ = l_Array_append___redArg(v_fst_2167_, v___x_2202_);
lean_dec_ref(v___x_2202_);
v___x_2204_ = lean_unsigned_to_nat(1u);
v___x_2205_ = lean_mk_empty_array_with_capacity(v___x_2204_);
v___x_2206_ = lean_array_push(v___x_2205_, v_fst_2193_);
v___x_2207_ = l_Array_append___redArg(v___x_2203_, v___x_2206_);
lean_dec_ref(v___x_2206_);
v___x_2208_ = l_Subarray_drop___redArg(v_snd_2198_, v___x_2204_);
v___x_2209_ = l_Subarray_drop___redArg(v_snd_2201_, v___x_2204_);
v___x_2210_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v___x_2208_, v___x_2209_);
v___x_2211_ = l_Array_append___redArg(v___x_2207_, v___x_2210_);
lean_dec_ref(v___x_2210_);
v___x_2212_ = l_Array_append___redArg(v___x_2211_, v_snd_2174_);
lean_dec(v_snd_2174_);
return v___x_2212_;
}
else
{
lean_object* v___x_2213_; 
lean_dec(v___x_2189_);
lean_dec(v_fst_2173_);
lean_dec(v_fst_2172_);
v___x_2213_ = l_Array_append___redArg(v_fst_2167_, v_snd_2174_);
lean_dec(v_snd_2174_);
return v___x_2213_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(lean_object* v___x_2220_, lean_object* v_original_2221_, lean_object* v_a_2222_){
_start:
{
lean_object* v_fst_2223_; lean_object* v_snd_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2243_; 
v_fst_2223_ = lean_ctor_get(v_a_2222_, 0);
v_snd_2224_ = lean_ctor_get(v_a_2222_, 1);
v_isSharedCheck_2243_ = !lean_is_exclusive(v_a_2222_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2226_ = v_a_2222_;
v_isShared_2227_ = v_isSharedCheck_2243_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_snd_2224_);
lean_inc(v_fst_2223_);
lean_dec(v_a_2222_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2243_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
uint8_t v___x_2228_; 
v___x_2228_ = lean_nat_dec_lt(v_snd_2224_, v___x_2220_);
if (v___x_2228_ == 0)
{
lean_object* v___x_2230_; 
if (v_isShared_2227_ == 0)
{
v___x_2230_ = v___x_2226_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_fst_2223_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_snd_2224_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
else
{
uint8_t v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2232_ = 1;
v___x_2233_ = lean_array_fget_borrowed(v_original_2221_, v_snd_2224_);
v___x_2234_ = lean_box(v___x_2232_);
lean_inc(v___x_2233_);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 1, v___x_2233_);
lean_ctor_set(v___x_2226_, 0, v___x_2234_);
v___x_2236_ = v___x_2226_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v___x_2234_);
lean_ctor_set(v_reuseFailAlloc_2242_, 1, v___x_2233_);
v___x_2236_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2237_ = lean_array_push(v_fst_2223_, v___x_2236_);
v___x_2238_ = lean_unsigned_to_nat(1u);
v___x_2239_ = lean_nat_add(v_snd_2224_, v___x_2238_);
lean_dec(v_snd_2224_);
v___x_2240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2237_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v_a_2222_ = v___x_2240_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg___boxed(lean_object* v___x_2244_, lean_object* v_original_2245_, lean_object* v_a_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2244_, v_original_2245_, v_a_2246_);
lean_dec_ref(v_original_2245_);
lean_dec(v___x_2244_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(lean_object* v___x_2248_, lean_object* v_edited_2249_, lean_object* v_a_2250_){
_start:
{
lean_object* v_fst_2251_; lean_object* v_snd_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2271_; 
v_fst_2251_ = lean_ctor_get(v_a_2250_, 0);
v_snd_2252_ = lean_ctor_get(v_a_2250_, 1);
v_isSharedCheck_2271_ = !lean_is_exclusive(v_a_2250_);
if (v_isSharedCheck_2271_ == 0)
{
v___x_2254_ = v_a_2250_;
v_isShared_2255_ = v_isSharedCheck_2271_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_snd_2252_);
lean_inc(v_fst_2251_);
lean_dec(v_a_2250_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2271_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
uint8_t v___x_2256_; 
v___x_2256_ = lean_nat_dec_lt(v_snd_2252_, v___x_2248_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2258_; 
if (v_isShared_2255_ == 0)
{
v___x_2258_ = v___x_2254_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_fst_2251_);
lean_ctor_set(v_reuseFailAlloc_2259_, 1, v_snd_2252_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
else
{
uint8_t v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2264_; 
v___x_2260_ = 0;
v___x_2261_ = lean_array_fget_borrowed(v_edited_2249_, v_snd_2252_);
v___x_2262_ = lean_box(v___x_2260_);
lean_inc(v___x_2261_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 1, v___x_2261_);
lean_ctor_set(v___x_2254_, 0, v___x_2262_);
v___x_2264_ = v___x_2254_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2270_; 
v_reuseFailAlloc_2270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2270_, 0, v___x_2262_);
lean_ctor_set(v_reuseFailAlloc_2270_, 1, v___x_2261_);
v___x_2264_ = v_reuseFailAlloc_2270_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2265_ = lean_array_push(v_fst_2251_, v___x_2264_);
v___x_2266_ = lean_unsigned_to_nat(1u);
v___x_2267_ = lean_nat_add(v_snd_2252_, v___x_2266_);
lean_dec(v_snd_2252_);
v___x_2268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2265_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
v_a_2250_ = v___x_2268_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg___boxed(lean_object* v___x_2272_, lean_object* v_edited_2273_, lean_object* v_a_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2272_, v_edited_2273_, v_a_2274_);
lean_dec_ref(v_edited_2273_);
lean_dec(v___x_2272_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(lean_object* v___x_2276_, lean_object* v_original_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v_fst_2280_; lean_object* v_snd_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2305_; 
v_fst_2280_ = lean_ctor_get(v_a_2279_, 0);
v_snd_2281_ = lean_ctor_get(v_a_2279_, 1);
v_isSharedCheck_2305_ = !lean_is_exclusive(v_a_2279_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2283_ = v_a_2279_;
v_isShared_2284_ = v_isSharedCheck_2305_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_snd_2281_);
lean_inc(v_fst_2280_);
lean_dec(v_a_2279_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2305_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
uint8_t v___x_2285_; 
v___x_2285_ = lean_nat_dec_lt(v_snd_2281_, v___x_2276_);
if (v___x_2285_ == 0)
{
lean_object* v___x_2287_; 
if (v_isShared_2284_ == 0)
{
v___x_2287_ = v___x_2283_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_fst_2280_);
lean_ctor_set(v_reuseFailAlloc_2288_, 1, v_snd_2281_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
else
{
lean_object* v___x_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; 
v___x_2289_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2290_ = lean_array_get_borrowed(v___x_2289_, v_original_2277_, v_snd_2281_);
v___x_2291_ = lean_string_dec_eq(v___x_2290_, v_a_2278_);
if (v___x_2291_ == 0)
{
uint8_t v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2295_; 
v___x_2292_ = 1;
v___x_2293_ = lean_box(v___x_2292_);
lean_inc(v___x_2290_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 1, v___x_2290_);
lean_ctor_set(v___x_2283_, 0, v___x_2293_);
v___x_2295_ = v___x_2283_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2293_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v___x_2290_);
v___x_2295_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2296_ = lean_array_push(v_fst_2280_, v___x_2295_);
v___x_2297_ = lean_unsigned_to_nat(1u);
v___x_2298_ = lean_nat_add(v_snd_2281_, v___x_2297_);
lean_dec(v_snd_2281_);
v___x_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2296_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
v_a_2279_ = v___x_2299_;
goto _start;
}
}
else
{
lean_object* v___x_2303_; 
if (v_isShared_2284_ == 0)
{
v___x_2303_ = v___x_2283_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_fst_2280_);
lean_ctor_set(v_reuseFailAlloc_2304_, 1, v_snd_2281_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg___boxed(lean_object* v___x_2306_, lean_object* v_original_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2306_, v_original_2307_, v_a_2308_, v_a_2309_);
lean_dec_ref(v_a_2308_);
lean_dec_ref(v_original_2307_);
lean_dec(v___x_2306_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(lean_object* v___x_2311_, lean_object* v_edited_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_){
_start:
{
lean_object* v_fst_2315_; lean_object* v_snd_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2340_; 
v_fst_2315_ = lean_ctor_get(v_a_2314_, 0);
v_snd_2316_ = lean_ctor_get(v_a_2314_, 1);
v_isSharedCheck_2340_ = !lean_is_exclusive(v_a_2314_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2318_ = v_a_2314_;
v_isShared_2319_ = v_isSharedCheck_2340_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_snd_2316_);
lean_inc(v_fst_2315_);
lean_dec(v_a_2314_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2340_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
uint8_t v___x_2320_; 
v___x_2320_ = lean_nat_dec_lt(v_snd_2316_, v___x_2311_);
if (v___x_2320_ == 0)
{
lean_object* v___x_2322_; 
if (v_isShared_2319_ == 0)
{
v___x_2322_ = v___x_2318_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_fst_2315_);
lean_ctor_set(v_reuseFailAlloc_2323_, 1, v_snd_2316_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
else
{
lean_object* v___x_2324_; lean_object* v___x_2325_; uint8_t v___x_2326_; 
v___x_2324_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2325_ = lean_array_get_borrowed(v___x_2324_, v_edited_2312_, v_snd_2316_);
v___x_2326_ = lean_string_dec_eq(v___x_2325_, v_a_2313_);
if (v___x_2326_ == 0)
{
uint8_t v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2330_; 
v___x_2327_ = 0;
v___x_2328_ = lean_box(v___x_2327_);
lean_inc(v___x_2325_);
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 1, v___x_2325_);
lean_ctor_set(v___x_2318_, 0, v___x_2328_);
v___x_2330_ = v___x_2318_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v___x_2328_);
lean_ctor_set(v_reuseFailAlloc_2336_, 1, v___x_2325_);
v___x_2330_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2331_ = lean_array_push(v_fst_2315_, v___x_2330_);
v___x_2332_ = lean_unsigned_to_nat(1u);
v___x_2333_ = lean_nat_add(v_snd_2316_, v___x_2332_);
lean_dec(v_snd_2316_);
v___x_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2331_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v_a_2314_ = v___x_2334_;
goto _start;
}
}
else
{
lean_object* v___x_2338_; 
if (v_isShared_2319_ == 0)
{
v___x_2338_ = v___x_2318_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_fst_2315_);
lean_ctor_set(v_reuseFailAlloc_2339_, 1, v_snd_2316_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg___boxed(lean_object* v___x_2341_, lean_object* v_edited_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2341_, v_edited_2342_, v_a_2343_, v_a_2344_);
lean_dec_ref(v_a_2343_);
lean_dec_ref(v_edited_2342_);
lean_dec(v___x_2341_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(lean_object* v___x_2346_, lean_object* v_original_2347_, lean_object* v___x_2348_, lean_object* v_edited_2349_, lean_object* v_as_2350_, size_t v_sz_2351_, size_t v_i_2352_, lean_object* v_b_2353_){
_start:
{
uint8_t v___x_2354_; 
v___x_2354_ = lean_usize_dec_lt(v_i_2352_, v_sz_2351_);
if (v___x_2354_ == 0)
{
return v_b_2353_;
}
else
{
lean_object* v_snd_2355_; lean_object* v_fst_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2403_; 
v_snd_2355_ = lean_ctor_get(v_b_2353_, 1);
v_fst_2356_ = lean_ctor_get(v_b_2353_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v_b_2353_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2358_ = v_b_2353_;
v_isShared_2359_ = v_isSharedCheck_2403_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_snd_2355_);
lean_inc(v_fst_2356_);
lean_dec(v_b_2353_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2403_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v_fst_2360_; lean_object* v_snd_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2402_; 
v_fst_2360_ = lean_ctor_get(v_snd_2355_, 0);
v_snd_2361_ = lean_ctor_get(v_snd_2355_, 1);
v_isSharedCheck_2402_ = !lean_is_exclusive(v_snd_2355_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2363_ = v_snd_2355_;
v_isShared_2364_ = v_isSharedCheck_2402_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_snd_2361_);
lean_inc(v_fst_2360_);
lean_dec(v_snd_2355_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2402_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v_a_2365_; lean_object* v___x_2367_; 
v_a_2365_ = lean_array_uget_borrowed(v_as_2350_, v_i_2352_);
if (v_isShared_2364_ == 0)
{
lean_ctor_set(v___x_2363_, 1, v_fst_2360_);
lean_ctor_set(v___x_2363_, 0, v_fst_2356_);
v___x_2367_ = v___x_2363_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_fst_2356_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v_fst_2360_);
v___x_2367_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
lean_object* v___x_2368_; lean_object* v_fst_2369_; lean_object* v_snd_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2400_; 
v___x_2368_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2346_, v_original_2347_, v_a_2365_, v___x_2367_);
v_fst_2369_ = lean_ctor_get(v___x_2368_, 0);
v_snd_2370_ = lean_ctor_get(v___x_2368_, 1);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2372_ = v___x_2368_;
v_isShared_2373_ = v_isSharedCheck_2400_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_snd_2370_);
lean_inc(v_fst_2369_);
lean_dec(v___x_2368_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2400_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 1, v_snd_2361_);
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_fst_2369_);
lean_ctor_set(v_reuseFailAlloc_2399_, 1, v_snd_2361_);
v___x_2375_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
lean_object* v___x_2376_; lean_object* v_fst_2377_; lean_object* v_snd_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2398_; 
v___x_2376_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2348_, v_edited_2349_, v_a_2365_, v___x_2375_);
v_fst_2377_ = lean_ctor_get(v___x_2376_, 0);
v_snd_2378_ = lean_ctor_get(v___x_2376_, 1);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2380_ = v___x_2376_;
v_isShared_2381_ = v_isSharedCheck_2398_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_snd_2378_);
lean_inc(v_fst_2377_);
lean_dec(v___x_2376_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2398_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
uint8_t v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2385_; 
v___x_2382_ = 2;
v___x_2383_ = lean_box(v___x_2382_);
lean_inc(v_a_2365_);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 1, v_a_2365_);
lean_ctor_set(v___x_2380_, 0, v___x_2383_);
v___x_2385_ = v___x_2380_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v___x_2383_);
lean_ctor_set(v_reuseFailAlloc_2397_, 1, v_a_2365_);
v___x_2385_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2391_; 
v___x_2386_ = lean_array_push(v_fst_2377_, v___x_2385_);
v___x_2387_ = lean_unsigned_to_nat(1u);
v___x_2388_ = lean_nat_add(v_snd_2370_, v___x_2387_);
lean_dec(v_snd_2370_);
v___x_2389_ = lean_nat_add(v_snd_2378_, v___x_2387_);
lean_dec(v_snd_2378_);
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 1, v___x_2389_);
lean_ctor_set(v___x_2358_, 0, v___x_2388_);
v___x_2391_ = v___x_2358_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v___x_2388_);
lean_ctor_set(v_reuseFailAlloc_2396_, 1, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
lean_object* v___x_2392_; size_t v___x_2393_; size_t v___x_2394_; 
v___x_2392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2386_);
lean_ctor_set(v___x_2392_, 1, v___x_2391_);
v___x_2393_ = ((size_t)1ULL);
v___x_2394_ = lean_usize_add(v_i_2352_, v___x_2393_);
v_i_2352_ = v___x_2394_;
v_b_2353_ = v___x_2392_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14___boxed(lean_object* v___x_2404_, lean_object* v_original_2405_, lean_object* v___x_2406_, lean_object* v_edited_2407_, lean_object* v_as_2408_, lean_object* v_sz_2409_, lean_object* v_i_2410_, lean_object* v_b_2411_){
_start:
{
size_t v_sz_boxed_2412_; size_t v_i_boxed_2413_; lean_object* v_res_2414_; 
v_sz_boxed_2412_ = lean_unbox_usize(v_sz_2409_);
lean_dec(v_sz_2409_);
v_i_boxed_2413_ = lean_unbox_usize(v_i_2410_);
lean_dec(v_i_2410_);
v_res_2414_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v___x_2404_, v_original_2405_, v___x_2406_, v_edited_2407_, v_as_2408_, v_sz_boxed_2412_, v_i_boxed_2413_, v_b_2411_);
lean_dec_ref(v_as_2408_);
lean_dec_ref(v_edited_2407_);
lean_dec(v___x_2406_);
lean_dec_ref(v_original_2405_);
lean_dec(v___x_2404_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(lean_object* v___x_2415_, lean_object* v_edited_2416_, lean_object* v___x_2417_, lean_object* v_original_2418_, lean_object* v_as_2419_, size_t v_sz_2420_, size_t v_i_2421_, lean_object* v_b_2422_){
_start:
{
uint8_t v___x_2423_; 
v___x_2423_ = lean_usize_dec_lt(v_i_2421_, v_sz_2420_);
if (v___x_2423_ == 0)
{
return v_b_2422_;
}
else
{
lean_object* v_snd_2424_; lean_object* v_fst_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2472_; 
v_snd_2424_ = lean_ctor_get(v_b_2422_, 1);
v_fst_2425_ = lean_ctor_get(v_b_2422_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v_b_2422_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2427_ = v_b_2422_;
v_isShared_2428_ = v_isSharedCheck_2472_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_snd_2424_);
lean_inc(v_fst_2425_);
lean_dec(v_b_2422_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2472_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v_fst_2429_; lean_object* v_snd_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2471_; 
v_fst_2429_ = lean_ctor_get(v_snd_2424_, 0);
v_snd_2430_ = lean_ctor_get(v_snd_2424_, 1);
v_isSharedCheck_2471_ = !lean_is_exclusive(v_snd_2424_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2432_ = v_snd_2424_;
v_isShared_2433_ = v_isSharedCheck_2471_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_snd_2430_);
lean_inc(v_fst_2429_);
lean_dec(v_snd_2424_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2471_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v_a_2434_; lean_object* v___x_2436_; 
v_a_2434_ = lean_array_uget_borrowed(v_as_2419_, v_i_2421_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 1, v_fst_2429_);
lean_ctor_set(v___x_2432_, 0, v_fst_2425_);
v___x_2436_ = v___x_2432_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_fst_2425_);
lean_ctor_set(v_reuseFailAlloc_2470_, 1, v_fst_2429_);
v___x_2436_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2437_; lean_object* v_fst_2438_; lean_object* v_snd_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2469_; 
v___x_2437_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2417_, v_original_2418_, v_a_2434_, v___x_2436_);
v_fst_2438_ = lean_ctor_get(v___x_2437_, 0);
v_snd_2439_ = lean_ctor_get(v___x_2437_, 1);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2441_ = v___x_2437_;
v_isShared_2442_ = v_isSharedCheck_2469_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_snd_2439_);
lean_inc(v_fst_2438_);
lean_dec(v___x_2437_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2469_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2444_; 
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 1, v_snd_2430_);
v___x_2444_ = v___x_2441_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_fst_2438_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v_snd_2430_);
v___x_2444_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
lean_object* v___x_2445_; lean_object* v_fst_2446_; lean_object* v_snd_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2467_; 
v___x_2445_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2415_, v_edited_2416_, v_a_2434_, v___x_2444_);
v_fst_2446_ = lean_ctor_get(v___x_2445_, 0);
v_snd_2447_ = lean_ctor_get(v___x_2445_, 1);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2449_ = v___x_2445_;
v_isShared_2450_ = v_isSharedCheck_2467_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_snd_2447_);
lean_inc(v_fst_2446_);
lean_dec(v___x_2445_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2467_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
uint8_t v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2454_; 
v___x_2451_ = 2;
v___x_2452_ = lean_box(v___x_2451_);
lean_inc(v_a_2434_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 1, v_a_2434_);
lean_ctor_set(v___x_2449_, 0, v___x_2452_);
v___x_2454_ = v___x_2449_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2452_);
lean_ctor_set(v_reuseFailAlloc_2466_, 1, v_a_2434_);
v___x_2454_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2460_; 
v___x_2455_ = lean_array_push(v_fst_2446_, v___x_2454_);
v___x_2456_ = lean_unsigned_to_nat(1u);
v___x_2457_ = lean_nat_add(v_snd_2439_, v___x_2456_);
lean_dec(v_snd_2439_);
v___x_2458_ = lean_nat_add(v_snd_2447_, v___x_2456_);
lean_dec(v_snd_2447_);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 1, v___x_2458_);
lean_ctor_set(v___x_2427_, 0, v___x_2457_);
v___x_2460_ = v___x_2427_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2457_);
lean_ctor_set(v_reuseFailAlloc_2465_, 1, v___x_2458_);
v___x_2460_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
lean_object* v___x_2461_; size_t v___x_2462_; size_t v___x_2463_; lean_object* v___x_2464_; 
v___x_2461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2455_);
lean_ctor_set(v___x_2461_, 1, v___x_2460_);
v___x_2462_ = ((size_t)1ULL);
v___x_2463_ = lean_usize_add(v_i_2421_, v___x_2462_);
v___x_2464_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v___x_2417_, v_original_2418_, v___x_2415_, v_edited_2416_, v_as_2419_, v_sz_2420_, v___x_2463_, v___x_2461_);
return v___x_2464_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4___boxed(lean_object* v___x_2473_, lean_object* v_edited_2474_, lean_object* v___x_2475_, lean_object* v_original_2476_, lean_object* v_as_2477_, lean_object* v_sz_2478_, lean_object* v_i_2479_, lean_object* v_b_2480_){
_start:
{
size_t v_sz_boxed_2481_; size_t v_i_boxed_2482_; lean_object* v_res_2483_; 
v_sz_boxed_2481_ = lean_unbox_usize(v_sz_2478_);
lean_dec(v_sz_2478_);
v_i_boxed_2482_ = lean_unbox_usize(v_i_2479_);
lean_dec(v_i_2479_);
v_res_2483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v___x_2473_, v_edited_2474_, v___x_2475_, v_original_2476_, v_as_2477_, v_sz_boxed_2481_, v_i_boxed_2482_, v_b_2480_);
lean_dec_ref(v_as_2477_);
lean_dec_ref(v_original_2476_);
lean_dec(v___x_2475_);
lean_dec_ref(v_edited_2474_);
lean_dec(v___x_2473_);
return v_res_2483_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(size_t v_sz_2484_, size_t v_i_2485_, lean_object* v_bs_2486_){
_start:
{
uint8_t v___x_2487_; 
v___x_2487_ = lean_usize_dec_lt(v_i_2485_, v_sz_2484_);
if (v___x_2487_ == 0)
{
return v_bs_2486_;
}
else
{
lean_object* v_v_2488_; lean_object* v___x_2489_; lean_object* v_bs_x27_2490_; uint8_t v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; size_t v___x_2494_; size_t v___x_2495_; lean_object* v___x_2496_; 
v_v_2488_ = lean_array_uget(v_bs_2486_, v_i_2485_);
v___x_2489_ = lean_unsigned_to_nat(0u);
v_bs_x27_2490_ = lean_array_uset(v_bs_2486_, v_i_2485_, v___x_2489_);
v___x_2491_ = 1;
v___x_2492_ = lean_box(v___x_2491_);
v___x_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2492_);
lean_ctor_set(v___x_2493_, 1, v_v_2488_);
v___x_2494_ = ((size_t)1ULL);
v___x_2495_ = lean_usize_add(v_i_2485_, v___x_2494_);
v___x_2496_ = lean_array_uset(v_bs_x27_2490_, v_i_2485_, v___x_2493_);
v_i_2485_ = v___x_2495_;
v_bs_2486_ = v___x_2496_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7___boxed(lean_object* v_sz_2498_, lean_object* v_i_2499_, lean_object* v_bs_2500_){
_start:
{
size_t v_sz_boxed_2501_; size_t v_i_boxed_2502_; lean_object* v_res_2503_; 
v_sz_boxed_2501_ = lean_unbox_usize(v_sz_2498_);
lean_dec(v_sz_2498_);
v_i_boxed_2502_ = lean_unbox_usize(v_i_2499_);
lean_dec(v_i_2499_);
v_res_2503_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_boxed_2501_, v_i_boxed_2502_, v_bs_2500_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(lean_object* v_original_2509_, lean_object* v_edited_2510_){
_start:
{
lean_object* v_i_2511_; lean_object* v___x_2512_; uint8_t v___x_2513_; 
v_i_2511_ = lean_unsigned_to_nat(0u);
v___x_2512_ = lean_array_get_size(v_original_2509_);
v___x_2513_ = lean_nat_dec_lt(v_i_2511_, v___x_2512_);
if (v___x_2513_ == 0)
{
size_t v_sz_2514_; size_t v___x_2515_; lean_object* v___x_2516_; 
lean_dec_ref(v_original_2509_);
v_sz_2514_ = lean_array_size(v_edited_2510_);
v___x_2515_ = ((size_t)0ULL);
v___x_2516_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_2514_, v___x_2515_, v_edited_2510_);
return v___x_2516_;
}
else
{
lean_object* v___x_2517_; uint8_t v___x_2518_; 
v___x_2517_ = lean_array_get_size(v_edited_2510_);
v___x_2518_ = lean_nat_dec_lt(v_i_2511_, v___x_2517_);
if (v___x_2518_ == 0)
{
size_t v_sz_2519_; size_t v___x_2520_; lean_object* v___x_2521_; 
lean_dec_ref(v_edited_2510_);
v_sz_2519_ = lean_array_size(v_original_2509_);
v___x_2520_ = ((size_t)0ULL);
v___x_2521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_2519_, v___x_2520_, v_original_2509_);
return v___x_2521_;
}
else
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v_ds_2524_; lean_object* v___x_2525_; size_t v_sz_2526_; size_t v___x_2527_; lean_object* v___x_2528_; lean_object* v_snd_2529_; lean_object* v_fst_2530_; lean_object* v_fst_2531_; lean_object* v_snd_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2551_; 
lean_inc_ref(v_original_2509_);
v___x_2522_ = l_Array_toSubarray___redArg(v_original_2509_, v_i_2511_, v___x_2512_);
lean_inc_ref(v_edited_2510_);
v___x_2523_ = l_Array_toSubarray___redArg(v_edited_2510_, v_i_2511_, v___x_2517_);
v_ds_2524_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v___x_2522_, v___x_2523_);
v___x_2525_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__1));
v_sz_2526_ = lean_array_size(v_ds_2524_);
v___x_2527_ = ((size_t)0ULL);
v___x_2528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v___x_2517_, v_edited_2510_, v___x_2512_, v_original_2509_, v_ds_2524_, v_sz_2526_, v___x_2527_, v___x_2525_);
lean_dec_ref(v_ds_2524_);
v_snd_2529_ = lean_ctor_get(v___x_2528_, 1);
lean_inc(v_snd_2529_);
v_fst_2530_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_fst_2530_);
lean_dec_ref(v___x_2528_);
v_fst_2531_ = lean_ctor_get(v_snd_2529_, 0);
v_snd_2532_ = lean_ctor_get(v_snd_2529_, 1);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_snd_2529_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2534_ = v_snd_2529_;
v_isShared_2535_ = v_isSharedCheck_2551_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_snd_2532_);
lean_inc(v_fst_2531_);
lean_dec(v_snd_2529_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2551_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 1, v_fst_2531_);
lean_ctor_set(v___x_2534_, 0, v_fst_2530_);
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_fst_2530_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v_fst_2531_);
v___x_2537_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2538_; lean_object* v_fst_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2548_; 
v___x_2538_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2512_, v_original_2509_, v___x_2537_);
lean_dec_ref(v_original_2509_);
v_fst_2539_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2548_ == 0)
{
lean_object* v_unused_2549_; 
v_unused_2549_ = lean_ctor_get(v___x_2538_, 1);
lean_dec(v_unused_2549_);
v___x_2541_ = v___x_2538_;
v_isShared_2542_ = v_isSharedCheck_2548_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_fst_2539_);
lean_dec(v___x_2538_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2548_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 1, v_snd_2532_);
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_fst_2539_);
lean_ctor_set(v_reuseFailAlloc_2547_, 1, v_snd_2532_);
v___x_2544_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2545_; lean_object* v_fst_2546_; 
v___x_2545_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2517_, v_edited_2510_, v___x_2544_);
lean_dec_ref(v_edited_2510_);
v_fst_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_fst_2546_);
lean_dec_ref(v___x_2545_);
return v_fst_2546_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(lean_object* v___x_2552_, uint8_t v_inSubst_2553_, lean_object* v___x_2554_, lean_object* v_____r_2555_, lean_object* v_wssIdx_2556_){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2557_ = lean_box(v_inSubst_2553_);
v___x_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2552_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
v___x_2559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2559_, 0, v_wssIdx_2556_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
v___x_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2554_);
lean_ctor_set(v___x_2560_, 1, v___x_2559_);
v___x_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
return v___x_2561_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1___boxed(lean_object* v___x_2562_, lean_object* v_inSubst_2563_, lean_object* v___x_2564_, lean_object* v_____r_2565_, lean_object* v_wssIdx_2566_){
_start:
{
uint8_t v_inSubst_boxed_2567_; lean_object* v_res_2568_; 
v_inSubst_boxed_2567_ = lean_unbox(v_inSubst_2563_);
v_res_2568_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2562_, v_inSubst_boxed_2567_, v___x_2564_, v_____r_2565_, v_wssIdx_2566_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(lean_object* v_fst_2569_, uint8_t v___x_2570_, lean_object* v_fst_2571_, lean_object* v___x_2572_, lean_object* v_00___2573_){
_start:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; 
v___x_2574_ = lean_box(v___x_2570_);
v___x_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2575_, 0, v_fst_2569_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
v___x_2576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2576_, 0, v_fst_2571_);
lean_ctor_set(v___x_2576_, 1, v___x_2575_);
v___x_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2577_, 0, v___x_2572_);
lean_ctor_set(v___x_2577_, 1, v___x_2576_);
v___x_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2578_, 0, v___x_2577_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0___boxed(lean_object* v_fst_2579_, lean_object* v___x_2580_, lean_object* v_fst_2581_, lean_object* v___x_2582_, lean_object* v_00___2583_){
_start:
{
uint8_t v___x_9315__boxed_2584_; lean_object* v_res_2585_; 
v___x_9315__boxed_2584_ = lean_unbox(v___x_2580_);
v_res_2585_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2579_, v___x_9315__boxed_2584_, v_fst_2581_, v___x_2582_, v_00___2583_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(uint8_t v_inSubst_2586_, lean_object* v_snd_2587_, lean_object* v_fst_2588_, lean_object* v_____r_2589_, lean_object* v_withWs_2590_, lean_object* v_wssIdx_2591_){
_start:
{
lean_object* v_wss_x27Idx_2593_; uint8_t v___x_2599_; 
v___x_2599_ = lean_unbox(v_snd_2587_);
if (v___x_2599_ == 0)
{
v_wss_x27Idx_2593_ = v_fst_2588_;
goto v___jp_2592_;
}
else
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2600_ = lean_unsigned_to_nat(1u);
v___x_2601_ = lean_nat_add(v_fst_2588_, v___x_2600_);
lean_dec(v_fst_2588_);
v_wss_x27Idx_2593_ = v___x_2601_;
goto v___jp_2592_;
}
v___jp_2592_:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2594_ = lean_box(v_inSubst_2586_);
v___x_2595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2595_, 0, v_wss_x27Idx_2593_);
lean_ctor_set(v___x_2595_, 1, v___x_2594_);
v___x_2596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2596_, 0, v_wssIdx_2591_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
v___x_2597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2597_, 0, v_withWs_2590_);
lean_ctor_set(v___x_2597_, 1, v___x_2596_);
v___x_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2597_);
return v___x_2598_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2___boxed(lean_object* v_inSubst_2602_, lean_object* v_snd_2603_, lean_object* v_fst_2604_, lean_object* v_____r_2605_, lean_object* v_withWs_2606_, lean_object* v_wssIdx_2607_){
_start:
{
uint8_t v_inSubst_boxed_2608_; lean_object* v_res_2609_; 
v_inSubst_boxed_2608_ = lean_unbox(v_inSubst_2602_);
v_res_2609_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_boxed_2608_, v_snd_2603_, v_fst_2604_, v_____r_2605_, v_withWs_2606_, v_wssIdx_2607_);
lean_dec(v_snd_2603_);
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(lean_object* v_upperBound_2610_, lean_object* v_diff_2611_, lean_object* v_snd_2612_, lean_object* v_snd_2613_, lean_object* v_a_2614_, lean_object* v_b_2615_){
_start:
{
lean_object* v_a_2617_; lean_object* v___y_2622_; uint8_t v___x_2625_; 
v___x_2625_ = lean_nat_dec_lt(v_a_2614_, v_upperBound_2610_);
if (v___x_2625_ == 0)
{
lean_dec(v_a_2614_);
return v_b_2615_;
}
else
{
lean_object* v___x_2626_; lean_object* v_snd_2627_; lean_object* v_snd_2628_; lean_object* v_fst_2629_; lean_object* v_fst_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2770_; 
v___x_2626_ = lean_array_fget_borrowed(v_diff_2611_, v_a_2614_);
v_snd_2627_ = lean_ctor_get(v_b_2615_, 1);
lean_inc(v_snd_2627_);
v_snd_2628_ = lean_ctor_get(v_snd_2627_, 1);
lean_inc(v_snd_2628_);
v_fst_2629_ = lean_ctor_get(v___x_2626_, 0);
v_fst_2630_ = lean_ctor_get(v_b_2615_, 0);
v_isSharedCheck_2770_ = !lean_is_exclusive(v_b_2615_);
if (v_isSharedCheck_2770_ == 0)
{
lean_object* v_unused_2771_; 
v_unused_2771_ = lean_ctor_get(v_b_2615_, 1);
lean_dec(v_unused_2771_);
v___x_2632_ = v_b_2615_;
v_isShared_2633_ = v_isSharedCheck_2770_;
goto v_resetjp_2631_;
}
else
{
lean_inc(v_fst_2630_);
lean_dec(v_b_2615_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2770_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v_fst_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2768_; 
v_fst_2634_ = lean_ctor_get(v_snd_2627_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v_snd_2627_);
if (v_isSharedCheck_2768_ == 0)
{
lean_object* v_unused_2769_; 
v_unused_2769_ = lean_ctor_get(v_snd_2627_, 1);
lean_dec(v_unused_2769_);
v___x_2636_ = v_snd_2627_;
v_isShared_2637_ = v_isSharedCheck_2768_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_fst_2634_);
lean_dec(v_snd_2627_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2768_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v_fst_2638_; lean_object* v_snd_2639_; lean_object* v___x_2641_; uint8_t v_isShared_2642_; uint8_t v_isSharedCheck_2767_; 
v_fst_2638_ = lean_ctor_get(v_snd_2628_, 0);
v_snd_2639_ = lean_ctor_get(v_snd_2628_, 1);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_snd_2628_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2641_ = v_snd_2628_;
v_isShared_2642_ = v_isSharedCheck_2767_;
goto v_resetjp_2640_;
}
else
{
lean_inc(v_snd_2639_);
lean_inc(v_fst_2638_);
lean_dec(v_snd_2628_);
v___x_2641_ = lean_box(0);
v_isShared_2642_ = v_isSharedCheck_2767_;
goto v_resetjp_2640_;
}
v_resetjp_2640_:
{
lean_object* v___x_2643_; lean_object* v___y_2645_; lean_object* v___y_2660_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; uint8_t v___x_2671_; 
lean_inc(v___x_2626_);
v___x_2643_ = lean_array_push(v_fst_2630_, v___x_2626_);
v___x_2668_ = lean_unsigned_to_nat(1u);
v___x_2669_ = lean_nat_add(v_a_2614_, v___x_2668_);
v___x_2670_ = lean_array_get_size(v_diff_2611_);
v___x_2671_ = lean_nat_dec_lt(v___x_2669_, v___x_2670_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
lean_dec(v___x_2669_);
lean_del_object(v___x_2641_);
lean_del_object(v___x_2636_);
lean_del_object(v___x_2632_);
v___x_2672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2672_, 0, v_fst_2638_);
lean_ctor_set(v___x_2672_, 1, v_snd_2639_);
v___x_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2673_, 0, v_fst_2634_);
lean_ctor_set(v___x_2673_, 1, v___x_2672_);
v___x_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2674_, 0, v___x_2643_);
lean_ctor_set(v___x_2674_, 1, v___x_2673_);
v_a_2617_ = v___x_2674_;
goto v___jp_2616_;
}
else
{
lean_object* v___x_2675_; lean_object* v_fst_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2765_; 
v___x_2675_ = lean_array_fget(v_diff_2611_, v___x_2669_);
lean_dec(v___x_2669_);
v_fst_2676_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2765_ == 0)
{
lean_object* v_unused_2766_; 
v_unused_2766_ = lean_ctor_get(v___x_2675_, 1);
lean_dec(v_unused_2766_);
v___x_2678_ = v___x_2675_;
v_isShared_2679_ = v_isSharedCheck_2765_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_fst_2676_);
lean_dec(v___x_2675_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2765_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
uint8_t v_inSubst_2680_; lean_object* v___y_2682_; lean_object* v___x_2691_; uint8_t v___x_2692_; 
v_inSubst_2680_ = 0;
v___x_2691_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2692_ = lean_unbox(v_fst_2629_);
switch(v___x_2692_)
{
case 0:
{
uint8_t v___x_2693_; 
lean_del_object(v___x_2641_);
lean_del_object(v___x_2636_);
lean_del_object(v___x_2632_);
v___x_2693_ = lean_unbox(v_fst_2676_);
switch(v___x_2693_)
{
case 0:
{
lean_object* v___x_2694_; lean_object* v___x_2696_; 
v___x_2694_ = lean_array_get_borrowed(v___x_2691_, v_snd_2612_, v_fst_2638_);
lean_inc(v___x_2694_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 1, v___x_2694_);
v___x_2696_ = v___x_2678_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_fst_2676_);
lean_ctor_set(v_reuseFailAlloc_2702_, 1, v___x_2694_);
v___x_2696_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2697_ = lean_array_push(v___x_2643_, v___x_2696_);
v___x_2698_ = lean_nat_add(v_fst_2638_, v___x_2668_);
lean_dec(v_fst_2638_);
v___x_2699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
lean_ctor_set(v___x_2699_, 1, v_snd_2639_);
v___x_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2700_, 0, v_fst_2634_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2701_, 0, v___x_2697_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
v_a_2617_ = v___x_2701_;
goto v___jp_2616_;
}
}
case 1:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; 
lean_del_object(v___x_2678_);
lean_dec(v_fst_2676_);
lean_dec(v_snd_2639_);
v___x_2703_ = lean_box(0);
v___x_2704_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2638_, v___x_2625_, v_fst_2634_, v___x_2643_, v___x_2703_);
v___y_2622_ = v___x_2704_;
goto v___jp_2621_;
}
default: 
{
lean_object* v___x_2705_; uint8_t v___x_2706_; 
lean_dec(v_fst_2676_);
v___x_2705_ = lean_array_get_borrowed(v___x_2691_, v_snd_2612_, v_fst_2638_);
v___x_2706_ = lean_unbox(v_snd_2639_);
if (v___x_2706_ == 0)
{
lean_object* v___x_2708_; 
lean_inc(v___x_2705_);
lean_inc(v_fst_2629_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 1, v___x_2705_);
lean_ctor_set(v___x_2678_, 0, v_fst_2629_);
v___x_2708_ = v___x_2678_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_fst_2629_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v___x_2705_);
v___x_2708_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2709_ = lean_mk_empty_array_with_capacity(v___x_2668_);
v___x_2710_ = lean_array_push(v___x_2709_, v___x_2708_);
v___y_2682_ = v___x_2710_;
goto v___jp_2681_;
}
}
else
{
lean_object* v___x_2712_; lean_object* v___x_2713_; 
lean_del_object(v___x_2678_);
v___x_2712_ = lean_array_get_borrowed(v___x_2691_, v_snd_2613_, v_fst_2634_);
lean_inc(v___x_2705_);
lean_inc(v___x_2712_);
v___x_2713_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2712_, v___x_2705_);
v___y_2682_ = v___x_2713_;
goto v___jp_2681_;
}
}
}
}
case 1:
{
uint8_t v___x_2714_; 
lean_del_object(v___x_2641_);
lean_del_object(v___x_2636_);
lean_del_object(v___x_2632_);
v___x_2714_ = lean_unbox(v_fst_2676_);
switch(v___x_2714_)
{
case 0:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; 
lean_del_object(v___x_2678_);
lean_dec(v_fst_2676_);
lean_dec(v_snd_2639_);
v___x_2715_ = lean_box(0);
v___x_2716_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2638_, v___x_2625_, v_fst_2634_, v___x_2643_, v___x_2715_);
v___y_2622_ = v___x_2716_;
goto v___jp_2621_;
}
case 1:
{
lean_object* v___x_2717_; lean_object* v___x_2719_; 
v___x_2717_ = lean_array_get_borrowed(v___x_2691_, v_snd_2613_, v_fst_2634_);
lean_inc(v___x_2717_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 1, v___x_2717_);
v___x_2719_ = v___x_2678_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_fst_2676_);
lean_ctor_set(v_reuseFailAlloc_2725_, 1, v___x_2717_);
v___x_2719_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___x_2720_ = lean_array_push(v___x_2643_, v___x_2719_);
v___x_2721_ = lean_nat_add(v_fst_2634_, v___x_2668_);
lean_dec(v_fst_2634_);
v___x_2722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2722_, 0, v_fst_2638_);
lean_ctor_set(v___x_2722_, 1, v_snd_2639_);
v___x_2723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2723_, 0, v___x_2721_);
lean_ctor_set(v___x_2723_, 1, v___x_2722_);
v___x_2724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2720_);
lean_ctor_set(v___x_2724_, 1, v___x_2723_);
v_a_2617_ = v___x_2724_;
goto v___jp_2616_;
}
}
default: 
{
uint8_t v___x_2729_; 
lean_dec(v_fst_2676_);
v___x_2729_ = lean_unbox(v_snd_2639_);
if (v___x_2729_ == 0)
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; uint8_t v___x_2734_; 
v___x_2730_ = lean_array_get_borrowed(v___x_2691_, v_snd_2613_, v_fst_2634_);
v___x_2731_ = lean_unsigned_to_nat(0u);
v___x_2732_ = lean_string_utf8_byte_size(v___x_2730_);
lean_inc(v___x_2730_);
v___x_2733_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2730_);
lean_ctor_set(v___x_2733_, 1, v___x_2731_);
lean_ctor_set(v___x_2733_, 2, v___x_2732_);
v___x_2734_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_2733_);
lean_dec_ref_known(v___x_2733_, 3);
if (v___x_2734_ == 0)
{
lean_object* v___x_2736_; 
lean_inc(v___x_2730_);
lean_inc(v_fst_2629_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 1, v___x_2730_);
lean_ctor_set(v___x_2678_, 0, v_fst_2629_);
v___x_2736_ = v___x_2678_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_fst_2629_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v___x_2730_);
v___x_2736_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___x_2737_ = lean_array_push(v___x_2643_, v___x_2736_);
v___x_2738_ = lean_nat_add(v_fst_2634_, v___x_2668_);
lean_dec(v_fst_2634_);
v___x_2739_ = lean_box(0);
v___x_2740_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2680_, v_snd_2639_, v_fst_2638_, v___x_2739_, v___x_2737_, v___x_2738_);
lean_dec(v_snd_2639_);
v___y_2622_ = v___x_2740_;
goto v___jp_2621_;
}
}
else
{
lean_del_object(v___x_2678_);
goto v___jp_2726_;
}
}
else
{
lean_del_object(v___x_2678_);
goto v___jp_2726_;
}
v___jp_2726_:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; 
v___x_2727_ = lean_box(0);
v___x_2728_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2680_, v_snd_2639_, v_fst_2638_, v___x_2727_, v___x_2643_, v_fst_2634_);
lean_dec(v_snd_2639_);
v___y_2622_ = v___x_2728_;
goto v___jp_2621_;
}
}
}
}
default: 
{
uint8_t v___x_2742_; 
v___x_2742_ = lean_unbox(v_fst_2676_);
if (v___x_2742_ == 1)
{
lean_object* v___x_2743_; lean_object* v___x_2744_; uint8_t v___x_2745_; 
v___x_2743_ = lean_array_get_borrowed(v___x_2691_, v_snd_2613_, v_fst_2634_);
v___x_2744_ = lean_array_get_size(v_snd_2612_);
v___x_2745_ = lean_nat_dec_lt(v_fst_2638_, v___x_2744_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2747_; 
lean_inc(v___x_2743_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 1, v___x_2743_);
v___x_2747_ = v___x_2678_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_fst_2676_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v___x_2743_);
v___x_2747_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2748_ = lean_mk_empty_array_with_capacity(v___x_2668_);
v___x_2749_ = lean_array_push(v___x_2748_, v___x_2747_);
v___y_2645_ = v___x_2749_;
goto v___jp_2644_;
}
}
else
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
lean_del_object(v___x_2678_);
lean_dec(v_fst_2676_);
v___x_2751_ = lean_array_fget_borrowed(v_snd_2612_, v_fst_2638_);
lean_inc(v___x_2751_);
lean_inc(v___x_2743_);
v___x_2752_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2743_, v___x_2751_);
v___y_2645_ = v___x_2752_;
goto v___jp_2644_;
}
}
else
{
lean_object* v___x_2753_; lean_object* v___x_2754_; uint8_t v___x_2755_; 
lean_dec(v_fst_2676_);
lean_del_object(v___x_2641_);
lean_del_object(v___x_2636_);
lean_del_object(v___x_2632_);
v___x_2753_ = lean_array_get_borrowed(v___x_2691_, v_snd_2612_, v_fst_2638_);
v___x_2754_ = lean_array_get_size(v_snd_2613_);
v___x_2755_ = lean_nat_dec_lt(v_fst_2634_, v___x_2754_);
if (v___x_2755_ == 0)
{
uint8_t v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2759_; 
v___x_2756_ = 0;
v___x_2757_ = lean_box(v___x_2756_);
lean_inc(v___x_2753_);
if (v_isShared_2679_ == 0)
{
lean_ctor_set(v___x_2678_, 1, v___x_2753_);
lean_ctor_set(v___x_2678_, 0, v___x_2757_);
v___x_2759_ = v___x_2678_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v___x_2757_);
lean_ctor_set(v_reuseFailAlloc_2762_, 1, v___x_2753_);
v___x_2759_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2760_ = lean_mk_empty_array_with_capacity(v___x_2668_);
v___x_2761_ = lean_array_push(v___x_2760_, v___x_2759_);
v___y_2660_ = v___x_2761_;
goto v___jp_2659_;
}
}
else
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
lean_del_object(v___x_2678_);
v___x_2763_ = lean_array_fget_borrowed(v_snd_2613_, v_fst_2634_);
lean_inc(v___x_2753_);
lean_inc(v___x_2763_);
v___x_2764_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2763_, v___x_2753_);
v___y_2660_ = v___x_2764_;
goto v___jp_2659_;
}
}
}
}
v___jp_2681_:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; uint8_t v___x_2685_; 
v___x_2683_ = l_Array_append___redArg(v___x_2643_, v___y_2682_);
lean_dec_ref(v___y_2682_);
v___x_2684_ = lean_nat_add(v_fst_2638_, v___x_2668_);
lean_dec(v_fst_2638_);
v___x_2685_ = lean_unbox(v_snd_2639_);
lean_dec(v_snd_2639_);
if (v___x_2685_ == 0)
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2686_ = lean_box(0);
v___x_2687_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2684_, v_inSubst_2680_, v___x_2683_, v___x_2686_, v_fst_2634_);
v___y_2622_ = v___x_2687_;
goto v___jp_2621_;
}
else
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2688_ = lean_nat_add(v_fst_2634_, v___x_2668_);
lean_dec(v_fst_2634_);
v___x_2689_ = lean_box(0);
v___x_2690_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2684_, v_inSubst_2680_, v___x_2683_, v___x_2689_, v___x_2688_);
v___y_2622_ = v___x_2690_;
goto v___jp_2621_;
}
}
}
}
v___jp_2644_:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2646_ = l_Array_append___redArg(v___x_2643_, v___y_2645_);
lean_dec_ref(v___y_2645_);
v___x_2647_ = lean_unsigned_to_nat(1u);
v___x_2648_ = lean_nat_add(v_fst_2634_, v___x_2647_);
lean_dec(v_fst_2634_);
v___x_2649_ = lean_nat_add(v_fst_2638_, v___x_2647_);
lean_dec(v_fst_2638_);
if (v_isShared_2642_ == 0)
{
lean_ctor_set(v___x_2641_, 0, v___x_2649_);
v___x_2651_ = v___x_2641_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v___x_2649_);
lean_ctor_set(v_reuseFailAlloc_2658_, 1, v_snd_2639_);
v___x_2651_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2653_; 
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 1, v___x_2651_);
lean_ctor_set(v___x_2636_, 0, v___x_2648_);
v___x_2653_ = v___x_2636_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2648_);
lean_ctor_set(v_reuseFailAlloc_2657_, 1, v___x_2651_);
v___x_2653_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
lean_object* v___x_2655_; 
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 1, v___x_2653_);
lean_ctor_set(v___x_2632_, 0, v___x_2646_);
v___x_2655_ = v___x_2632_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2646_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v___x_2653_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
v_a_2617_ = v___x_2655_;
goto v___jp_2616_;
}
}
}
}
v___jp_2659_:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2661_ = l_Array_append___redArg(v___x_2643_, v___y_2660_);
lean_dec_ref(v___y_2660_);
v___x_2662_ = lean_unsigned_to_nat(1u);
v___x_2663_ = lean_nat_add(v_fst_2634_, v___x_2662_);
lean_dec(v_fst_2634_);
v___x_2664_ = lean_nat_add(v_fst_2638_, v___x_2662_);
lean_dec(v_fst_2638_);
v___x_2665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2664_);
lean_ctor_set(v___x_2665_, 1, v_snd_2639_);
v___x_2666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2666_, 0, v___x_2663_);
lean_ctor_set(v___x_2666_, 1, v___x_2665_);
v___x_2667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2667_, 0, v___x_2661_);
lean_ctor_set(v___x_2667_, 1, v___x_2666_);
v_a_2617_ = v___x_2667_;
goto v___jp_2616_;
}
}
}
}
}
v___jp_2616_:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2618_ = lean_unsigned_to_nat(1u);
v___x_2619_ = lean_nat_add(v_a_2614_, v___x_2618_);
lean_dec(v_a_2614_);
v_a_2614_ = v___x_2619_;
v_b_2615_ = v_a_2617_;
goto _start;
}
v___jp_2621_:
{
if (lean_obj_tag(v___y_2622_) == 0)
{
lean_object* v_a_2623_; 
lean_dec(v_a_2614_);
v_a_2623_ = lean_ctor_get(v___y_2622_, 0);
lean_inc(v_a_2623_);
lean_dec_ref_known(v___y_2622_, 1);
return v_a_2623_;
}
else
{
lean_object* v_a_2624_; 
v_a_2624_ = lean_ctor_get(v___y_2622_, 0);
lean_inc(v_a_2624_);
lean_dec_ref_known(v___y_2622_, 1);
v_a_2617_ = v_a_2624_;
goto v___jp_2616_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___boxed(lean_object* v_upperBound_2772_, lean_object* v_diff_2773_, lean_object* v_snd_2774_, lean_object* v_snd_2775_, lean_object* v_a_2776_, lean_object* v_b_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2772_, v_diff_2773_, v_snd_2774_, v_snd_2775_, v_a_2776_, v_b_2777_);
lean_dec_ref(v_snd_2775_);
lean_dec_ref(v_snd_2774_);
lean_dec_ref(v_diff_2773_);
lean_dec(v_upperBound_2772_);
return v_res_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(lean_object* v_s_2789_, lean_object* v_s_x27_2790_){
_start:
{
lean_object* v___x_2791_; lean_object* v_fst_2792_; lean_object* v_snd_2793_; lean_object* v___x_2794_; lean_object* v_fst_2795_; lean_object* v_snd_2796_; lean_object* v_diff_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v_fst_2802_; lean_object* v___x_2803_; size_t v_sz_2804_; size_t v___x_2805_; lean_object* v___x_2806_; 
v___x_2791_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_2789_);
v_fst_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_fst_2792_);
v_snd_2793_ = lean_ctor_get(v___x_2791_, 1);
lean_inc(v_snd_2793_);
lean_dec_ref(v___x_2791_);
v___x_2794_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_x27_2790_);
v_fst_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_fst_2795_);
v_snd_2796_ = lean_ctor_get(v___x_2794_, 1);
lean_inc(v_snd_2796_);
lean_dec_ref(v___x_2794_);
v_diff_2797_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(v_fst_2792_, v_fst_2795_);
v___x_2798_ = lean_unsigned_to_nat(0u);
v___x_2799_ = lean_array_get_size(v_diff_2797_);
v___x_2800_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__2));
v___x_2801_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v___x_2799_, v_diff_2797_, v_snd_2796_, v_snd_2793_, v___x_2798_, v___x_2800_);
lean_dec(v_snd_2793_);
lean_dec(v_snd_2796_);
lean_dec_ref(v_diff_2797_);
v_fst_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_fst_2802_);
lean_dec_ref(v___x_2801_);
v___x_2803_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_fst_2802_);
lean_dec(v_fst_2802_);
v_sz_2804_ = lean_array_size(v___x_2803_);
v___x_2805_ = ((size_t)0ULL);
v___x_2806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_2804_, v___x_2805_, v___x_2803_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___boxed(lean_object* v_s_2807_, lean_object* v_s_x27_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_2807_, v_s_x27_2808_);
lean_dec_ref(v_s_x27_2808_);
lean_dec_ref(v_s_2807_);
return v_res_2809_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(lean_object* v_upperBound_2810_, lean_object* v_diff_2811_, lean_object* v_snd_2812_, lean_object* v_snd_2813_, lean_object* v_inst_2814_, lean_object* v_R_2815_, lean_object* v_a_2816_, lean_object* v_b_2817_, lean_object* v_c_2818_){
_start:
{
lean_object* v___x_2819_; 
v___x_2819_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2810_, v_diff_2811_, v_snd_2812_, v_snd_2813_, v_a_2816_, v_b_2817_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___boxed(lean_object* v_upperBound_2820_, lean_object* v_diff_2821_, lean_object* v_snd_2822_, lean_object* v_snd_2823_, lean_object* v_inst_2824_, lean_object* v_R_2825_, lean_object* v_a_2826_, lean_object* v_b_2827_, lean_object* v_c_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(v_upperBound_2820_, v_diff_2821_, v_snd_2822_, v_snd_2823_, v_inst_2824_, v_R_2825_, v_a_2826_, v_b_2827_, v_c_2828_);
lean_dec_ref(v_snd_2823_);
lean_dec_ref(v_snd_2822_);
lean_dec_ref(v_diff_2821_);
lean_dec(v_upperBound_2820_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(lean_object* v___x_2830_, lean_object* v_original_2831_, lean_object* v_a_2832_, lean_object* v_inst_2833_, lean_object* v_a_2834_){
_start:
{
lean_object* v___x_2835_; 
v___x_2835_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2830_, v_original_2831_, v_a_2832_, v_a_2834_);
return v___x_2835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___boxed(lean_object* v___x_2836_, lean_object* v_original_2837_, lean_object* v_a_2838_, lean_object* v_inst_2839_, lean_object* v_a_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v___x_2836_, v_original_2837_, v_a_2838_, v_inst_2839_, v_a_2840_);
lean_dec_ref(v_a_2838_);
lean_dec_ref(v_original_2837_);
lean_dec(v___x_2836_);
return v_res_2841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(lean_object* v___x_2842_, lean_object* v_edited_2843_, lean_object* v_a_2844_, lean_object* v_inst_2845_, lean_object* v_a_2846_){
_start:
{
lean_object* v___x_2847_; 
v___x_2847_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2842_, v_edited_2843_, v_a_2844_, v_a_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___boxed(lean_object* v___x_2848_, lean_object* v_edited_2849_, lean_object* v_a_2850_, lean_object* v_inst_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(v___x_2848_, v_edited_2849_, v_a_2850_, v_inst_2851_, v_a_2852_);
lean_dec_ref(v_a_2850_);
lean_dec_ref(v_edited_2849_);
lean_dec(v___x_2848_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(lean_object* v___x_2854_, lean_object* v_original_2855_, lean_object* v_inst_2856_, lean_object* v_a_2857_){
_start:
{
lean_object* v___x_2858_; 
v___x_2858_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2854_, v_original_2855_, v_a_2857_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___boxed(lean_object* v___x_2859_, lean_object* v_original_2860_, lean_object* v_inst_2861_, lean_object* v_a_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(v___x_2859_, v_original_2860_, v_inst_2861_, v_a_2862_);
lean_dec_ref(v_original_2860_);
lean_dec(v___x_2859_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(lean_object* v___x_2864_, lean_object* v_edited_2865_, lean_object* v_inst_2866_, lean_object* v_a_2867_){
_start:
{
lean_object* v___x_2868_; 
v___x_2868_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2864_, v_edited_2865_, v_a_2867_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___boxed(lean_object* v___x_2869_, lean_object* v_edited_2870_, lean_object* v_inst_2871_, lean_object* v_a_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(v___x_2869_, v_edited_2870_, v_inst_2871_, v_a_2872_);
lean_dec_ref(v_edited_2870_);
lean_dec(v___x_2869_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6(lean_object* v_as_2874_, lean_object* v_as_x27_2875_, lean_object* v_b_2876_, lean_object* v_a_2877_){
_start:
{
lean_object* v___x_2878_; 
v___x_2878_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(v_as_x27_2875_, v_b_2876_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___boxed(lean_object* v_as_2879_, lean_object* v_as_x27_2880_, lean_object* v_b_2881_, lean_object* v_a_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6(v_as_2879_, v_as_x27_2880_, v_b_2881_, v_a_2882_);
lean_dec(v_as_x27_2880_);
lean_dec(v_as_2879_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9(lean_object* v_lsize_2884_, lean_object* v_rsize_2885_, lean_object* v_histogram_2886_, lean_object* v_index_2887_, lean_object* v_val_2888_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___redArg(v_histogram_2886_, v_index_2887_, v_val_2888_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___boxed(lean_object* v_lsize_2890_, lean_object* v_rsize_2891_, lean_object* v_histogram_2892_, lean_object* v_index_2893_, lean_object* v_val_2894_){
_start:
{
lean_object* v_res_2895_; 
v_res_2895_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9(v_lsize_2890_, v_rsize_2891_, v_histogram_2892_, v_index_2893_, v_val_2894_);
lean_dec(v_rsize_2891_);
lean_dec(v_lsize_2890_);
return v_res_2895_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10(lean_object* v_upperBound_2896_, lean_object* v___x_2897_, lean_object* v_fst_2898_, lean_object* v___x_2899_, lean_object* v_inst_2900_, lean_object* v_R_2901_, lean_object* v_a_2902_, lean_object* v_b_2903_, lean_object* v_c_2904_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(v_upperBound_2896_, v___x_2897_, v_fst_2898_, v___x_2899_, v_a_2902_, v_b_2903_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___boxed(lean_object* v_upperBound_2906_, lean_object* v___x_2907_, lean_object* v_fst_2908_, lean_object* v___x_2909_, lean_object* v_inst_2910_, lean_object* v_R_2911_, lean_object* v_a_2912_, lean_object* v_b_2913_, lean_object* v_c_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10(v_upperBound_2906_, v___x_2907_, v_fst_2908_, v___x_2909_, v_inst_2910_, v_R_2911_, v_a_2912_, v_b_2913_, v_c_2914_);
lean_dec(v___x_2909_);
lean_dec_ref(v_fst_2908_);
lean_dec(v___x_2907_);
lean_dec(v_upperBound_2906_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11(lean_object* v_lsize_2916_, lean_object* v_rsize_2917_, lean_object* v_histogram_2918_, lean_object* v_index_2919_, lean_object* v_val_2920_){
_start:
{
lean_object* v___x_2921_; 
v___x_2921_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___redArg(v_histogram_2918_, v_index_2919_, v_val_2920_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___boxed(lean_object* v_lsize_2922_, lean_object* v_rsize_2923_, lean_object* v_histogram_2924_, lean_object* v_index_2925_, lean_object* v_val_2926_){
_start:
{
lean_object* v_res_2927_; 
v_res_2927_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11(v_lsize_2922_, v_rsize_2923_, v_histogram_2924_, v_index_2925_, v_val_2926_);
lean_dec(v_rsize_2923_);
lean_dec(v_lsize_2922_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12(lean_object* v_upperBound_2928_, lean_object* v_fst_2929_, lean_object* v___x_2930_, lean_object* v_fst_2931_, lean_object* v_inst_2932_, lean_object* v_R_2933_, lean_object* v_a_2934_, lean_object* v_b_2935_, lean_object* v_c_2936_){
_start:
{
lean_object* v___x_2937_; 
v___x_2937_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(v_upperBound_2928_, v_fst_2929_, v___x_2930_, v_fst_2931_, v_a_2934_, v_b_2935_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___boxed(lean_object* v_upperBound_2938_, lean_object* v_fst_2939_, lean_object* v___x_2940_, lean_object* v_fst_2941_, lean_object* v_inst_2942_, lean_object* v_R_2943_, lean_object* v_a_2944_, lean_object* v_b_2945_, lean_object* v_c_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12(v_upperBound_2938_, v_fst_2939_, v___x_2940_, v_fst_2941_, v_inst_2942_, v_R_2943_, v_a_2944_, v_b_2945_, v_c_2946_);
lean_dec_ref(v_fst_2941_);
lean_dec(v___x_2940_);
lean_dec_ref(v_fst_2939_);
lean_dec(v_upperBound_2938_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13(lean_object* v_00_u03b2_2948_, lean_object* v_m_2949_, lean_object* v_a_2950_){
_start:
{
lean_object* v___x_2951_; 
v___x_2951_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_m_2949_, v_a_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___boxed(lean_object* v_00_u03b2_2952_, lean_object* v_m_2953_, lean_object* v_a_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13(v_00_u03b2_2952_, v_m_2953_, v_a_2954_);
lean_dec_ref(v_a_2954_);
lean_dec_ref(v_m_2953_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_2956_, lean_object* v_m_2957_, lean_object* v_a_2958_, lean_object* v_b_2959_){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_m_2957_, v_a_2958_, v_b_2959_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14(lean_object* v_inst_2961_, lean_object* v_R_2962_, lean_object* v_a_2963_, lean_object* v_b_2964_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(v_a_2963_, v_b_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20(lean_object* v_00_u03b2_2966_, lean_object* v_a_2967_, lean_object* v_x_2968_){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(v_a_2967_, v_x_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___boxed(lean_object* v_00_u03b2_2970_, lean_object* v_a_2971_, lean_object* v_x_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20(v_00_u03b2_2970_, v_a_2971_, v_x_2972_);
lean_dec(v_x_2972_);
lean_dec_ref(v_a_2971_);
return v_res_2973_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22(lean_object* v_00_u03b2_2974_, lean_object* v_a_2975_, lean_object* v_x_2976_){
_start:
{
uint8_t v___x_2977_; 
v___x_2977_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(v_a_2975_, v_x_2976_);
return v___x_2977_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___boxed(lean_object* v_00_u03b2_2978_, lean_object* v_a_2979_, lean_object* v_x_2980_){
_start:
{
uint8_t v_res_2981_; lean_object* v_r_2982_; 
v_res_2981_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22(v_00_u03b2_2978_, v_a_2979_, v_x_2980_);
lean_dec(v_x_2980_);
lean_dec_ref(v_a_2979_);
v_r_2982_ = lean_box(v_res_2981_);
return v_r_2982_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23(lean_object* v_00_u03b2_2983_, lean_object* v_data_2984_){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23___redArg(v_data_2984_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24(lean_object* v_00_u03b2_2986_, lean_object* v_a_2987_, lean_object* v_b_2988_, lean_object* v_x_2989_){
_start:
{
lean_object* v___x_2990_; 
v___x_2990_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(v_a_2987_, v_b_2988_, v_x_2989_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28(lean_object* v_00_u03b2_2991_, lean_object* v_i_2992_, lean_object* v_source_2993_, lean_object* v_target_2994_){
_start:
{
lean_object* v___x_2995_; 
v___x_2995_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28___redArg(v_i_2992_, v_source_2993_, v_target_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_2996_, lean_object* v_x_2997_, lean_object* v_x_2998_){
_start:
{
lean_object* v___x_2999_; 
v___x_2999_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29___redArg(v_x_2997_, v_x_2998_);
return v___x_2999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(lean_object* v_s_3000_){
_start:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = l_String_toListImpl(v_s_3000_);
v___x_3002_ = lean_array_mk(v___x_3001_);
return v___x_3002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(lean_object* v_s_3003_, lean_object* v_s_x27_3004_){
_start:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3005_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3003_);
v___x_3006_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3004_);
v___x_3007_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3005_, v___x_3006_);
v___x_3008_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_3007_);
lean_dec_ref(v___x_3007_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(lean_object* v_s_3009_, lean_object* v_s_x27_3010_){
_start:
{
uint8_t v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; uint8_t v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; 
v___x_3011_ = 1;
v___x_3012_ = lean_box(v___x_3011_);
v___x_3013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
lean_ctor_set(v___x_3013_, 1, v_s_3009_);
v___x_3014_ = 0;
v___x_3015_ = lean_box(v___x_3014_);
v___x_3016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
lean_ctor_set(v___x_3016_, 1, v_s_x27_3010_);
v___x_3017_ = lean_unsigned_to_nat(2u);
v___x_3018_ = lean_mk_empty_array_with_capacity(v___x_3017_);
v___x_3019_ = lean_array_push(v___x_3018_, v___x_3013_);
v___x_3020_ = lean_array_push(v___x_3019_, v___x_3016_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(lean_object* v_as_3021_, size_t v_i_3022_, size_t v_stop_3023_, lean_object* v_b_3024_){
_start:
{
lean_object* v___y_3026_; uint8_t v___x_3030_; 
v___x_3030_ = lean_usize_dec_eq(v_i_3022_, v_stop_3023_);
if (v___x_3030_ == 0)
{
lean_object* v___x_3031_; lean_object* v_fst_3032_; uint8_t v___x_3033_; uint8_t v___x_3034_; uint8_t v___x_3035_; 
v___x_3031_ = lean_array_uget_borrowed(v_as_3021_, v_i_3022_);
v_fst_3032_ = lean_ctor_get(v___x_3031_, 0);
v___x_3033_ = 2;
v___x_3034_ = lean_unbox(v_fst_3032_);
v___x_3035_ = l_Lean_Diff_instBEqAction_beq(v___x_3034_, v___x_3033_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3036_; 
lean_inc(v___x_3031_);
v___x_3036_ = lean_array_push(v_b_3024_, v___x_3031_);
v___y_3026_ = v___x_3036_;
goto v___jp_3025_;
}
else
{
v___y_3026_ = v_b_3024_;
goto v___jp_3025_;
}
}
else
{
return v_b_3024_;
}
v___jp_3025_:
{
size_t v___x_3027_; size_t v___x_3028_; 
v___x_3027_ = ((size_t)1ULL);
v___x_3028_ = lean_usize_add(v_i_3022_, v___x_3027_);
v_i_3022_ = v___x_3028_;
v_b_3024_ = v___y_3026_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0___boxed(lean_object* v_as_3037_, lean_object* v_i_3038_, lean_object* v_stop_3039_, lean_object* v_b_3040_){
_start:
{
size_t v_i_boxed_3041_; size_t v_stop_boxed_3042_; lean_object* v_res_3043_; 
v_i_boxed_3041_ = lean_unbox_usize(v_i_3038_);
lean_dec(v_i_3038_);
v_stop_boxed_3042_ = lean_unbox_usize(v_stop_3039_);
lean_dec(v_stop_3039_);
v_res_3043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_as_3037_, v_i_boxed_3041_, v_stop_boxed_3042_, v_b_3040_);
lean_dec_ref(v_as_3037_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff(lean_object* v_s_3044_, lean_object* v_s_x27_3045_, uint8_t v_granularity_3046_){
_start:
{
lean_object* v___y_3048_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; 
switch(v_granularity_3046_)
{
case 0:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___y_3086_; uint8_t v___x_3092_; 
v___x_3083_ = lean_string_length(v_s_3044_);
v___x_3084_ = lean_string_length(v_s_x27_3045_);
v___x_3092_ = lean_nat_dec_le(v___x_3083_, v___x_3084_);
if (v___x_3092_ == 0)
{
v___y_3086_ = v___x_3084_;
goto v___jp_3085_;
}
else
{
v___y_3086_ = v___x_3083_;
goto v___jp_3085_;
}
v___jp_3085_:
{
lean_object* v___x_3087_; lean_object* v_maxCharDiffDistance_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; uint8_t v___x_3091_; 
v___x_3087_ = lean_unsigned_to_nat(5u);
v_maxCharDiffDistance_3088_ = lean_nat_div(v___y_3086_, v___x_3087_);
v___x_3089_ = lean_unsigned_to_nat(1u);
v___x_3090_ = lean_nat_shiftr(v___y_3086_, v___x_3089_);
lean_dec(v___y_3086_);
v___x_3091_ = lean_nat_dec_le(v___x_3083_, v___x_3084_);
if (v___x_3091_ == 0)
{
v___y_3067_ = v___x_3090_;
v___y_3068_ = v_maxCharDiffDistance_3088_;
v___y_3069_ = v___x_3089_;
v___y_3070_ = v___x_3083_;
goto v___jp_3066_;
}
else
{
v___y_3067_ = v___x_3090_;
v___y_3068_ = v_maxCharDiffDistance_3088_;
v___y_3069_ = v___x_3089_;
v___y_3070_ = v___x_3084_;
goto v___jp_3066_;
}
}
}
case 1:
{
lean_object* v___x_3093_; 
v___x_3093_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(v_s_3044_, v_s_x27_3045_);
return v___x_3093_;
}
case 2:
{
lean_object* v___x_3094_; 
v___x_3094_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3044_, v_s_x27_3045_);
lean_dec_ref(v_s_x27_3045_);
lean_dec_ref(v_s_3044_);
return v___x_3094_;
}
case 3:
{
lean_object* v___x_3095_; 
v___x_3095_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3044_, v_s_x27_3045_);
return v___x_3095_;
}
default: 
{
uint8_t v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
lean_dec_ref(v_s_3044_);
v___x_3096_ = 0;
v___x_3097_ = lean_box(v___x_3096_);
v___x_3098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3097_);
lean_ctor_set(v___x_3098_, 1, v_s_x27_3045_);
v___x_3099_ = lean_unsigned_to_nat(1u);
v___x_3100_ = lean_mk_empty_array_with_capacity(v___x_3099_);
v___x_3101_ = lean_array_push(v___x_3100_, v___x_3098_);
return v___x_3101_;
}
}
v___jp_3047_:
{
size_t v_sz_3049_; size_t v___x_3050_; lean_object* v___x_3051_; 
v_sz_3049_ = lean_array_size(v___y_3048_);
v___x_3050_ = ((size_t)0ULL);
v___x_3051_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_3049_, v___x_3050_, v___y_3048_);
return v___x_3051_;
}
v___jp_3052_:
{
lean_object* v_charArrDiff_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; uint8_t v___x_3060_; 
v_charArrDiff_3057_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v___y_3055_);
lean_dec_ref(v___y_3055_);
v___x_3058_ = lean_array_get_size(v_charArrDiff_3057_);
v___x_3059_ = lean_unsigned_to_nat(3u);
v___x_3060_ = lean_nat_dec_le(v___x_3058_, v___x_3059_);
if (v___x_3060_ == 0)
{
lean_object* v_approxEditDistance_3061_; uint8_t v___x_3062_; 
v_approxEditDistance_3061_ = lean_array_get_size(v___y_3056_);
lean_dec_ref(v___y_3056_);
v___x_3062_ = lean_nat_dec_le(v_approxEditDistance_3061_, v___y_3053_);
lean_dec(v___y_3053_);
if (v___x_3062_ == 0)
{
uint8_t v___x_3063_; 
lean_dec_ref(v_charArrDiff_3057_);
v___x_3063_ = lean_nat_dec_le(v_approxEditDistance_3061_, v___y_3054_);
lean_dec(v___y_3054_);
if (v___x_3063_ == 0)
{
lean_object* v___x_3064_; 
v___x_3064_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3044_, v_s_x27_3045_);
return v___x_3064_;
}
else
{
lean_object* v___x_3065_; 
v___x_3065_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3044_, v_s_x27_3045_);
lean_dec_ref(v_s_x27_3045_);
lean_dec_ref(v_s_3044_);
return v___x_3065_;
}
}
else
{
lean_dec(v___y_3054_);
lean_dec_ref(v_s_x27_3045_);
lean_dec_ref(v_s_3044_);
v___y_3048_ = v_charArrDiff_3057_;
goto v___jp_3047_;
}
}
else
{
lean_dec_ref(v___y_3056_);
lean_dec(v___y_3054_);
lean_dec(v___y_3053_);
lean_dec_ref(v_s_x27_3045_);
lean_dec_ref(v_s_3044_);
v___y_3048_ = v_charArrDiff_3057_;
goto v___jp_3047_;
}
}
v___jp_3066_:
{
lean_object* v___x_3071_; lean_object* v_maxWordDiffDistance_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v_charDiffRaw_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; uint8_t v___x_3079_; 
v___x_3071_ = lean_nat_shiftr(v___y_3070_, v___y_3069_);
lean_dec(v___y_3070_);
v_maxWordDiffDistance_3072_ = lean_nat_add(v___y_3067_, v___x_3071_);
lean_dec(v___x_3071_);
lean_dec(v___y_3067_);
lean_inc_ref(v_s_3044_);
v___x_3073_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3044_);
lean_inc_ref(v_s_x27_3045_);
v___x_3074_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3045_);
v_charDiffRaw_3075_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3073_, v___x_3074_);
v___x_3076_ = lean_unsigned_to_nat(0u);
v___x_3077_ = lean_array_get_size(v_charDiffRaw_3075_);
v___x_3078_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0));
v___x_3079_ = lean_nat_dec_lt(v___x_3076_, v___x_3077_);
if (v___x_3079_ == 0)
{
v___y_3053_ = v___y_3068_;
v___y_3054_ = v_maxWordDiffDistance_3072_;
v___y_3055_ = v_charDiffRaw_3075_;
v___y_3056_ = v___x_3078_;
goto v___jp_3052_;
}
else
{
size_t v___x_3080_; size_t v___x_3081_; lean_object* v___x_3082_; 
v___x_3080_ = ((size_t)0ULL);
v___x_3081_ = lean_usize_of_nat(v___x_3077_);
v___x_3082_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3075_, v___x_3080_, v___x_3081_, v___x_3078_);
v___y_3053_ = v___y_3068_;
v___y_3054_ = v_maxWordDiffDistance_3072_;
v___y_3055_ = v_charDiffRaw_3075_;
v___y_3056_ = v___x_3082_;
goto v___jp_3052_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff___boxed(lean_object* v_s_3102_, lean_object* v_s_x27_3103_, lean_object* v_granularity_3104_){
_start:
{
uint8_t v_granularity_boxed_3105_; lean_object* v_res_3106_; 
v_granularity_boxed_3105_ = lean_unbox(v_granularity_3104_);
v_res_3106_ = l_Lean_Meta_Hint_readableDiff(v_s_3102_, v_s_x27_3103_, v_granularity_boxed_3105_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(lean_object* v_as_3107_, size_t v_i_3108_, size_t v_stop_3109_, lean_object* v_b_3110_){
_start:
{
uint8_t v___x_3111_; 
v___x_3111_ = lean_usize_dec_eq(v_i_3108_, v_stop_3109_);
if (v___x_3111_ == 0)
{
lean_object* v___x_3112_; lean_object* v_snd_3113_; lean_object* v___x_3114_; size_t v___x_3115_; size_t v___x_3116_; 
v___x_3112_ = lean_array_uget_borrowed(v_as_3107_, v_i_3108_);
v_snd_3113_ = lean_ctor_get(v___x_3112_, 1);
v___x_3114_ = lean_string_append(v_b_3110_, v_snd_3113_);
v___x_3115_ = ((size_t)1ULL);
v___x_3116_ = lean_usize_add(v_i_3108_, v___x_3115_);
v_i_3108_ = v___x_3116_;
v_b_3110_ = v___x_3114_;
goto _start;
}
else
{
return v_b_3110_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0___boxed(lean_object* v_as_3118_, lean_object* v_i_3119_, lean_object* v_stop_3120_, lean_object* v_b_3121_){
_start:
{
size_t v_i_boxed_3122_; size_t v_stop_boxed_3123_; lean_object* v_res_3124_; 
v_i_boxed_3122_ = lean_unbox_usize(v_i_3119_);
lean_dec(v_i_3119_);
v_stop_boxed_3123_ = lean_unbox_usize(v_stop_3120_);
lean_dec(v_stop_3120_);
v_res_3124_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v_as_3118_, v_i_boxed_3122_, v_stop_boxed_3123_, v_b_3121_);
lean_dec_ref(v_as_3118_);
return v_res_3124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(lean_object* v_t_3125_, lean_object* v___y_3126_){
_start:
{
lean_object* v___x_3128_; lean_object* v_infoState_3129_; uint8_t v_enabled_3130_; 
v___x_3128_ = lean_st_ref_get(v___y_3126_);
v_infoState_3129_ = lean_ctor_get(v___x_3128_, 8);
lean_inc_ref(v_infoState_3129_);
lean_dec(v___x_3128_);
v_enabled_3130_ = lean_ctor_get_uint8(v_infoState_3129_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3129_);
if (v_enabled_3130_ == 0)
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
lean_dec_ref(v_t_3125_);
v___x_3131_ = lean_box(0);
v___x_3132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
return v___x_3132_;
}
else
{
lean_object* v___x_3133_; lean_object* v_infoState_3134_; lean_object* v_env_3135_; lean_object* v_nextMacroScope_3136_; lean_object* v_ngen_3137_; lean_object* v_auxDeclNGen_3138_; lean_object* v_traceState_3139_; lean_object* v_cache_3140_; lean_object* v_recordedDeps_3141_; lean_object* v_messages_3142_; lean_object* v_snapshotTasks_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3165_; 
v___x_3133_ = lean_st_ref_take(v___y_3126_);
v_infoState_3134_ = lean_ctor_get(v___x_3133_, 8);
v_env_3135_ = lean_ctor_get(v___x_3133_, 0);
v_nextMacroScope_3136_ = lean_ctor_get(v___x_3133_, 1);
v_ngen_3137_ = lean_ctor_get(v___x_3133_, 2);
v_auxDeclNGen_3138_ = lean_ctor_get(v___x_3133_, 3);
v_traceState_3139_ = lean_ctor_get(v___x_3133_, 4);
v_cache_3140_ = lean_ctor_get(v___x_3133_, 5);
v_recordedDeps_3141_ = lean_ctor_get(v___x_3133_, 6);
v_messages_3142_ = lean_ctor_get(v___x_3133_, 7);
v_snapshotTasks_3143_ = lean_ctor_get(v___x_3133_, 9);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3133_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3145_ = v___x_3133_;
v_isShared_3146_ = v_isSharedCheck_3165_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_snapshotTasks_3143_);
lean_inc(v_infoState_3134_);
lean_inc(v_messages_3142_);
lean_inc(v_recordedDeps_3141_);
lean_inc(v_cache_3140_);
lean_inc(v_traceState_3139_);
lean_inc(v_auxDeclNGen_3138_);
lean_inc(v_ngen_3137_);
lean_inc(v_nextMacroScope_3136_);
lean_inc(v_env_3135_);
lean_dec(v___x_3133_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3165_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
uint8_t v_enabled_3147_; lean_object* v_assignment_3148_; lean_object* v_lazyAssignment_3149_; lean_object* v_trees_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3164_; 
v_enabled_3147_ = lean_ctor_get_uint8(v_infoState_3134_, sizeof(void*)*3);
v_assignment_3148_ = lean_ctor_get(v_infoState_3134_, 0);
v_lazyAssignment_3149_ = lean_ctor_get(v_infoState_3134_, 1);
v_trees_3150_ = lean_ctor_get(v_infoState_3134_, 2);
v_isSharedCheck_3164_ = !lean_is_exclusive(v_infoState_3134_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3152_ = v_infoState_3134_;
v_isShared_3153_ = v_isSharedCheck_3164_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_trees_3150_);
lean_inc(v_lazyAssignment_3149_);
lean_inc(v_assignment_3148_);
lean_dec(v_infoState_3134_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3164_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3157_; 
v___x_3154_ = lean_box(0);
v___x_3155_ = l_Lean_PersistentArray_push___redArg(v_trees_3150_, v_t_3125_);
if (v_isShared_3153_ == 0)
{
lean_ctor_set(v___x_3152_, 2, v___x_3155_);
v___x_3157_ = v___x_3152_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_assignment_3148_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v_lazyAssignment_3149_);
lean_ctor_set(v_reuseFailAlloc_3163_, 2, v___x_3155_);
lean_ctor_set_uint8(v_reuseFailAlloc_3163_, sizeof(void*)*3, v_enabled_3147_);
v___x_3157_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
lean_object* v___x_3159_; 
if (v_isShared_3146_ == 0)
{
lean_ctor_set(v___x_3145_, 8, v___x_3157_);
v___x_3159_ = v___x_3145_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_env_3135_);
lean_ctor_set(v_reuseFailAlloc_3162_, 1, v_nextMacroScope_3136_);
lean_ctor_set(v_reuseFailAlloc_3162_, 2, v_ngen_3137_);
lean_ctor_set(v_reuseFailAlloc_3162_, 3, v_auxDeclNGen_3138_);
lean_ctor_set(v_reuseFailAlloc_3162_, 4, v_traceState_3139_);
lean_ctor_set(v_reuseFailAlloc_3162_, 5, v_cache_3140_);
lean_ctor_set(v_reuseFailAlloc_3162_, 6, v_recordedDeps_3141_);
lean_ctor_set(v_reuseFailAlloc_3162_, 7, v_messages_3142_);
lean_ctor_set(v_reuseFailAlloc_3162_, 8, v___x_3157_);
lean_ctor_set(v_reuseFailAlloc_3162_, 9, v_snapshotTasks_3143_);
v___x_3159_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3160_ = lean_st_ref_put(v___y_3126_, v___x_3159_);
v___x_3161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3154_);
return v___x_3161_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg___boxed(lean_object* v_t_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3166_, v___y_3167_);
lean_dec(v___y_3167_);
return v_res_3169_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3170_ = lean_unsigned_to_nat(32u);
v___x_3171_ = lean_mk_empty_array_with_capacity(v___x_3170_);
v___x_3172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3171_);
return v___x_3172_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1(void){
_start:
{
size_t v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3173_ = ((size_t)5ULL);
v___x_3174_ = lean_unsigned_to_nat(0u);
v___x_3175_ = lean_unsigned_to_nat(32u);
v___x_3176_ = lean_mk_empty_array_with_capacity(v___x_3175_);
v___x_3177_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0);
v___x_3178_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3178_, 0, v___x_3177_);
lean_ctor_set(v___x_3178_, 1, v___x_3176_);
lean_ctor_set(v___x_3178_, 2, v___x_3174_);
lean_ctor_set(v___x_3178_, 3, v___x_3174_);
lean_ctor_set_usize(v___x_3178_, 4, v___x_3173_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(lean_object* v_t_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
lean_object* v___x_3183_; lean_object* v_infoState_3184_; uint8_t v_enabled_3185_; 
v___x_3183_ = lean_st_ref_get(v___y_3181_);
v_infoState_3184_ = lean_ctor_get(v___x_3183_, 8);
lean_inc_ref(v_infoState_3184_);
lean_dec(v___x_3183_);
v_enabled_3185_ = lean_ctor_get_uint8(v_infoState_3184_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3184_);
if (v_enabled_3185_ == 0)
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
lean_dec_ref(v_t_3179_);
v___x_3186_ = lean_box(0);
v___x_3187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
return v___x_3187_;
}
else
{
lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3188_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1);
v___x_3189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3189_, 0, v_t_3179_);
lean_ctor_set(v___x_3189_, 1, v___x_3188_);
v___x_3190_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v___x_3189_, v___y_3181_);
return v___x_3190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___boxed(lean_object* v_t_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
lean_object* v_res_3195_; 
v_res_3195_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v_t_3191_, v___y_3192_, v___y_3193_);
lean_dec(v___y_3193_);
lean_dec_ref(v___y_3192_);
return v_res_3195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0(lean_object* v___x_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v___x_3198_; 
v___x_3198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3198_, 0, v___x_3196_);
lean_ctor_set(v___x_3198_, 1, v___y_3197_);
return v___x_3198_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__0));
v___x_3201_ = l_Lean_stringToMessageData(v___x_3200_);
return v___x_3201_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3203_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__2));
v___x_3204_ = l_Lean_stringToMessageData(v___x_3203_);
return v___x_3204_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29(void){
_start:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3253_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__28));
v___x_3254_ = l_Lean_Json_mkObj(v___x_3253_);
return v___x_3254_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30(void){
_start:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3255_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29);
v___x_3256_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__19));
v___x_3257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3256_);
lean_ctor_set(v___x_3257_, 1, v___x_3255_);
return v___x_3257_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31(void){
_start:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; 
v___x_3258_ = lean_box(0);
v___x_3259_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30);
v___x_3260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3259_);
lean_ctor_set(v___x_3260_, 1, v___x_3258_);
return v___x_3260_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33(void){
_start:
{
lean_object* v___x_3263_; lean_object* v___x_3264_; 
v___x_3263_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__32));
v___x_3264_ = l_Lean_MessageData_ofFormat(v___x_3263_);
return v___x_3264_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35(void){
_start:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3266_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__34));
v___x_3267_ = l_Lean_stringToMessageData(v___x_3266_);
return v___x_3267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(lean_object* v_suggestions_3269_, uint8_t v_forceList_3270_, lean_object* v_codeActionPrefix_x3f_3271_, lean_object* v_ref_3272_, lean_object* v_as_3273_, size_t v_sz_3274_, size_t v_i_3275_, lean_object* v_b_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
lean_object* v_a_3281_; lean_object* v___y_3286_; lean_object* v___y_3290_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; uint8_t v___x_3325_; 
v___x_3325_ = lean_usize_dec_lt(v_i_3275_, v_sz_3274_);
if (v___x_3325_ == 0)
{
lean_object* v___x_3326_; 
lean_dec(v_ref_3272_);
lean_dec(v_codeActionPrefix_x3f_3271_);
v___x_3326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3326_, 0, v_b_3276_);
return v___x_3326_;
}
else
{
lean_object* v_a_3327_; lean_object* v_toTryThisSuggestion_3328_; lean_object* v_span_x3f_3329_; lean_object* v_previewSpan_x3f_3330_; uint8_t v_diffGranularity_3331_; lean_object* v___x_3332_; lean_object* v___y_3334_; uint8_t v___y_3335_; lean_object* v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3363_; lean_object* v___y_3364_; uint8_t v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3409_; lean_object* v___y_3410_; uint8_t v___y_3411_; lean_object* v___y_3412_; uint8_t v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; uint8_t v___y_3423_; uint8_t v___y_3424_; lean_object* v___y_3425_; lean_object* v_postInfo_x3f_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3431_; lean_object* v___y_3432_; uint8_t v___y_3433_; lean_object* v___y_3434_; uint8_t v___y_3435_; lean_object* v___y_3436_; lean_object* v_edits_3437_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; uint8_t v___y_3447_; uint8_t v___y_3448_; lean_object* v_stop_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; lean_object* v_edits_3452_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; uint8_t v___y_3467_; uint8_t v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v_edits_3472_; lean_object* v___y_3473_; lean_object* v___x_3499_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; uint8_t v___y_3504_; lean_object* v___y_3505_; uint8_t v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3549_; uint8_t v___y_3550_; lean_object* v___y_3551_; uint8_t v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3565_; 
v_a_3327_ = lean_array_uget_borrowed(v_as_3273_, v_i_3275_);
v_toTryThisSuggestion_3328_ = lean_ctor_get(v_a_3327_, 0);
v_span_x3f_3329_ = lean_ctor_get(v_a_3327_, 1);
v_previewSpan_x3f_3330_ = lean_ctor_get(v_a_3327_, 2);
v_diffGranularity_3331_ = lean_ctor_get_uint8(v_a_3327_, sizeof(void*)*3);
v___x_3332_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_3499_ = l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_;
if (lean_obj_tag(v_span_x3f_3329_) == 0)
{
lean_inc(v_ref_3272_);
v___y_3565_ = v_ref_3272_;
goto v___jp_3564_;
}
else
{
lean_object* v_val_3583_; 
v_val_3583_ = lean_ctor_get(v_span_x3f_3329_, 0);
lean_inc(v_val_3583_);
v___y_3565_ = v_val_3583_;
goto v___jp_3564_;
}
v___jp_3333_:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___f_3354_; 
lean_inc_ref(v___y_3339_);
v___x_3340_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson(v___y_3339_);
v___x_3341_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__9));
v___x_3342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3341_);
lean_ctor_set(v___x_3342_, 1, v___x_3340_);
v___x_3343_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3344_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3344_, 0, v___y_3336_);
v___x_3345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3345_, 0, v___x_3343_);
lean_ctor_set(v___x_3345_, 1, v___x_3344_);
v___x_3346_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3347_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3337_);
v___x_3348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3346_);
lean_ctor_set(v___x_3348_, 1, v___x_3347_);
v___x_3349_ = lean_box(0);
v___x_3350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3348_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
v___x_3351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3345_);
lean_ctor_set(v___x_3351_, 1, v___x_3350_);
v___x_3352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3342_);
lean_ctor_set(v___x_3352_, 1, v___x_3351_);
v___x_3353_ = l_Lean_Json_mkObj(v___x_3352_);
lean_dec_ref_known(v___x_3352_, 2);
v___f_3354_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3354_, 0, v___x_3353_);
if (v___y_3335_ == 0)
{
lean_object* v___x_3355_; 
v___x_3355_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString(v___y_3339_);
v___y_3305_ = v___y_3334_;
v___y_3306_ = v___f_3354_;
v___y_3307_ = v___y_3338_;
v___y_3308_ = v___x_3355_;
goto v___jp_3304_;
}
else
{
lean_object* v___x_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; 
v___x_3356_ = lean_unsigned_to_nat(0u);
v___x_3357_ = lean_array_get_size(v___y_3339_);
v___x_3358_ = lean_nat_dec_lt(v___x_3356_, v___x_3357_);
if (v___x_3358_ == 0)
{
lean_dec_ref(v___y_3339_);
v___y_3305_ = v___y_3334_;
v___y_3306_ = v___f_3354_;
v___y_3307_ = v___y_3338_;
v___y_3308_ = v___x_3332_;
goto v___jp_3304_;
}
else
{
size_t v___x_3359_; size_t v___x_3360_; lean_object* v___x_3361_; 
v___x_3359_ = ((size_t)0ULL);
v___x_3360_ = lean_usize_of_nat(v___x_3357_);
v___x_3361_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3339_, v___x_3359_, v___x_3360_, v___x_3332_);
lean_dec_ref(v___y_3339_);
v___y_3305_ = v___y_3334_;
v___y_3306_ = v___f_3354_;
v___y_3307_ = v___y_3338_;
v___y_3308_ = v___x_3361_;
goto v___jp_3304_;
}
}
}
v___jp_3362_:
{
if (lean_obj_tag(v___y_3363_) == 0)
{
lean_object* v___x_3371_; uint64_t v_javascriptHash_3372_; lean_object* v_suggestion_3373_; lean_object* v_messageData_x3f_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___f_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; 
lean_dec_ref(v___y_3370_);
v___x_3371_ = ((lean_object*)(l_Lean_Meta_Hint_textInsertionWidget));
v_javascriptHash_3372_ = lean_ctor_get_uint64(v___x_3371_, sizeof(void*)*1);
v_suggestion_3373_ = lean_ctor_get(v___y_3368_, 0);
lean_inc_ref(v_suggestion_3373_);
v_messageData_x3f_3374_ = lean_ctor_get(v___y_3368_, 4);
lean_inc(v_messageData_x3f_3374_);
lean_dec_ref(v___y_3368_);
v___x_3375_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18));
v___x_3376_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3377_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3367_);
v___x_3378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3376_);
lean_ctor_set(v___x_3378_, 1, v___x_3377_);
v___x_3379_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3380_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3380_, 0, v___y_3366_);
v___x_3381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3379_);
lean_ctor_set(v___x_3381_, 1, v___x_3380_);
v___x_3382_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31);
v___x_3383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3381_);
lean_ctor_set(v___x_3383_, 1, v___x_3382_);
v___x_3384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3384_, 0, v___x_3378_);
lean_ctor_set(v___x_3384_, 1, v___x_3383_);
v___x_3385_ = l_Lean_Json_mkObj(v___x_3384_);
lean_dec_ref_known(v___x_3384_, 2);
v___f_3386_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3386_, 0, v___x_3385_);
v___x_3387_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3387_, 0, v___x_3375_);
lean_ctor_set(v___x_3387_, 1, v___f_3386_);
lean_ctor_set_uint64(v___x_3387_, sizeof(void*)*2, v_javascriptHash_3372_);
v___x_3388_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33);
v___x_3389_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3387_);
lean_ctor_set(v___x_3389_, 1, v___x_3388_);
v___x_3390_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3391_, 0, v___x_3390_);
lean_ctor_set(v___x_3391_, 1, v___x_3389_);
v___x_3392_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35);
v___x_3393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3391_);
lean_ctor_set(v___x_3393_, 1, v___x_3392_);
v___x_3394_ = l_Lean_stringToMessageData(v___y_3369_);
v___x_3395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3393_);
lean_ctor_set(v___x_3395_, 1, v___x_3394_);
if (lean_obj_tag(v_messageData_x3f_3374_) == 0)
{
if (lean_obj_tag(v_suggestion_3373_) == 0)
{
lean_object* v_a_3396_; lean_object* v___x_3397_; 
v_a_3396_ = lean_ctor_get(v_suggestion_3373_, 1);
lean_inc(v_a_3396_);
lean_dec_ref_known(v_suggestion_3373_, 2);
v___x_3397_ = l_Lean_MessageData_ofSyntax(v_a_3396_);
v___y_3298_ = v___y_3364_;
v___y_3299_ = v___x_3395_;
v___y_3300_ = v___x_3397_;
goto v___jp_3297_;
}
else
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3406_; 
v_a_3398_ = lean_ctor_get(v_suggestion_3373_, 0);
v_isSharedCheck_3406_ = !lean_is_exclusive(v_suggestion_3373_);
if (v_isSharedCheck_3406_ == 0)
{
v___x_3400_ = v_suggestion_3373_;
v_isShared_3401_ = v_isSharedCheck_3406_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v_suggestion_3373_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3406_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3403_; 
if (v_isShared_3401_ == 0)
{
lean_ctor_set_tag(v___x_3400_, 3);
v___x_3403_ = v___x_3400_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3405_; 
v_reuseFailAlloc_3405_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3405_, 0, v_a_3398_);
v___x_3403_ = v_reuseFailAlloc_3405_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
lean_object* v___x_3404_; 
v___x_3404_ = l_Lean_MessageData_ofFormat(v___x_3403_);
v___y_3298_ = v___y_3364_;
v___y_3299_ = v___x_3395_;
v___y_3300_ = v___x_3404_;
goto v___jp_3297_;
}
}
}
}
else
{
lean_object* v_val_3407_; 
lean_dec_ref(v_suggestion_3373_);
v_val_3407_ = lean_ctor_get(v_messageData_x3f_3374_, 0);
lean_inc(v_val_3407_);
lean_dec_ref_known(v_messageData_x3f_3374_, 1);
v___y_3298_ = v___y_3364_;
v___y_3299_ = v___x_3395_;
v___y_3300_ = v_val_3407_;
goto v___jp_3297_;
}
}
else
{
lean_dec_ref_known(v___y_3363_, 1);
lean_dec_ref(v___y_3368_);
v___y_3334_ = v___y_3364_;
v___y_3335_ = v___y_3365_;
v___y_3336_ = v___y_3366_;
v___y_3337_ = v___y_3367_;
v___y_3338_ = v___y_3369_;
v___y_3339_ = v___y_3370_;
goto v___jp_3333_;
}
}
v___jp_3408_:
{
if (v___y_3413_ == 4)
{
v___y_3363_ = v___y_3409_;
v___y_3364_ = v___y_3417_;
v___y_3365_ = v___x_3325_;
v___y_3366_ = v___y_3410_;
v___y_3367_ = v___y_3412_;
v___y_3368_ = v___y_3415_;
v___y_3369_ = v___y_3414_;
v___y_3370_ = v___y_3416_;
goto v___jp_3362_;
}
else
{
if (v___y_3411_ == 0)
{
lean_object* v_messageData_x3f_3418_; 
v_messageData_x3f_3418_ = lean_ctor_get(v___y_3415_, 4);
if (lean_obj_tag(v_messageData_x3f_3418_) == 0)
{
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3409_);
v___y_3334_ = v___y_3417_;
v___y_3335_ = v___y_3411_;
v___y_3336_ = v___y_3410_;
v___y_3337_ = v___y_3412_;
v___y_3338_ = v___y_3414_;
v___y_3339_ = v___y_3416_;
goto v___jp_3333_;
}
else
{
v___y_3363_ = v___y_3409_;
v___y_3364_ = v___y_3417_;
v___y_3365_ = v___y_3411_;
v___y_3366_ = v___y_3410_;
v___y_3367_ = v___y_3412_;
v___y_3368_ = v___y_3415_;
v___y_3369_ = v___y_3414_;
v___y_3370_ = v___y_3416_;
goto v___jp_3362_;
}
}
else
{
v___y_3363_ = v___y_3409_;
v___y_3364_ = v___y_3417_;
v___y_3365_ = v___y_3411_;
v___y_3366_ = v___y_3410_;
v___y_3367_ = v___y_3412_;
v___y_3368_ = v___y_3415_;
v___y_3369_ = v___y_3414_;
v___y_3370_ = v___y_3416_;
goto v___jp_3362_;
}
}
}
v___jp_3419_:
{
if (lean_obj_tag(v_postInfo_x3f_3426_) == 0)
{
v___y_3409_ = v___y_3420_;
v___y_3410_ = v___y_3421_;
v___y_3411_ = v___y_3423_;
v___y_3412_ = v___y_3422_;
v___y_3413_ = v___y_3424_;
v___y_3414_ = v___y_3428_;
v___y_3415_ = v___y_3425_;
v___y_3416_ = v___y_3427_;
v___y_3417_ = v___x_3332_;
goto v___jp_3408_;
}
else
{
lean_object* v_val_3429_; 
v_val_3429_ = lean_ctor_get(v_postInfo_x3f_3426_, 0);
lean_inc(v_val_3429_);
lean_dec_ref_known(v_postInfo_x3f_3426_, 1);
v___y_3409_ = v___y_3420_;
v___y_3410_ = v___y_3421_;
v___y_3411_ = v___y_3423_;
v___y_3412_ = v___y_3422_;
v___y_3413_ = v___y_3424_;
v___y_3414_ = v___y_3428_;
v___y_3415_ = v___y_3425_;
v___y_3416_ = v___y_3427_;
v___y_3417_ = v_val_3429_;
goto v___jp_3408_;
}
}
v___jp_3430_:
{
lean_object* v_preInfo_x3f_3438_; 
v_preInfo_x3f_3438_ = lean_ctor_get(v___y_3436_, 1);
if (lean_obj_tag(v_preInfo_x3f_3438_) == 0)
{
lean_object* v_postInfo_x3f_3439_; 
v_postInfo_x3f_3439_ = lean_ctor_get(v___y_3436_, 2);
lean_inc(v_postInfo_x3f_3439_);
v___y_3420_ = v___y_3431_;
v___y_3421_ = v___y_3432_;
v___y_3422_ = v___y_3434_;
v___y_3423_ = v___y_3433_;
v___y_3424_ = v___y_3435_;
v___y_3425_ = v___y_3436_;
v_postInfo_x3f_3426_ = v_postInfo_x3f_3439_;
v___y_3427_ = v_edits_3437_;
v___y_3428_ = v___x_3332_;
goto v___jp_3419_;
}
else
{
lean_object* v_postInfo_x3f_3440_; lean_object* v_val_3441_; 
v_postInfo_x3f_3440_ = lean_ctor_get(v___y_3436_, 2);
lean_inc(v_postInfo_x3f_3440_);
v_val_3441_ = lean_ctor_get(v_preInfo_x3f_3438_, 0);
lean_inc(v_val_3441_);
v___y_3420_ = v___y_3431_;
v___y_3421_ = v___y_3432_;
v___y_3422_ = v___y_3434_;
v___y_3423_ = v___y_3433_;
v___y_3424_ = v___y_3435_;
v___y_3425_ = v___y_3436_;
v_postInfo_x3f_3426_ = v_postInfo_x3f_3440_;
v___y_3427_ = v_edits_3437_;
v___y_3428_ = v_val_3441_;
goto v___jp_3419_;
}
}
v___jp_3442_:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; uint8_t v___x_3455_; 
v___x_3453_ = lean_unsigned_to_nat(1u);
v___x_3454_ = lean_nat_add(v___y_3451_, v___x_3453_);
v___x_3455_ = lean_nat_dec_le(v___x_3454_, v_stop_3449_);
lean_dec(v___x_3454_);
if (v___x_3455_ == 0)
{
lean_dec(v___y_3451_);
lean_dec(v_stop_3449_);
v___y_3431_ = v___y_3443_;
v___y_3432_ = v___y_3444_;
v___y_3433_ = v___y_3447_;
v___y_3434_ = v___y_3446_;
v___y_3435_ = v___y_3448_;
v___y_3436_ = v___y_3450_;
v_edits_3437_ = v_edits_3452_;
goto v___jp_3430_;
}
else
{
lean_object* v_source_3456_; uint8_t v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; 
v_source_3456_ = lean_ctor_get(v___y_3445_, 0);
v___x_3457_ = 2;
v___x_3458_ = lean_string_utf8_extract(v_source_3456_, v___y_3451_, v_stop_3449_);
lean_dec(v_stop_3449_);
lean_dec(v___y_3451_);
v___x_3459_ = lean_box(v___x_3457_);
v___x_3460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3459_);
lean_ctor_set(v___x_3460_, 1, v___x_3458_);
v___x_3461_ = lean_array_push(v_edits_3452_, v___x_3460_);
v___y_3431_ = v___y_3443_;
v___y_3432_ = v___y_3444_;
v___y_3433_ = v___y_3447_;
v___y_3434_ = v___y_3446_;
v___y_3435_ = v___y_3448_;
v___y_3436_ = v___y_3450_;
v_edits_3437_ = v___x_3461_;
goto v___jp_3430_;
}
}
v___jp_3462_:
{
if (lean_obj_tag(v___y_3463_) == 0)
{
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec(v___y_3464_);
v___y_3431_ = v___y_3463_;
v___y_3432_ = v___y_3465_;
v___y_3433_ = v___y_3467_;
v___y_3434_ = v___y_3466_;
v___y_3435_ = v___y_3468_;
v___y_3436_ = v___y_3469_;
v_edits_3437_ = v_edits_3472_;
goto v___jp_3430_;
}
else
{
lean_object* v_val_3474_; lean_object* v___x_3475_; 
v_val_3474_ = lean_ctor_get(v___y_3463_, 0);
v___x_3475_ = l_Lean_Syntax_getRange_x3f(v_val_3474_, v___y_3467_);
if (lean_obj_tag(v___x_3475_) == 1)
{
lean_object* v_val_3476_; uint8_t v___x_3477_; 
v_val_3476_ = lean_ctor_get(v___x_3475_, 0);
lean_inc(v_val_3476_);
lean_dec_ref_known(v___x_3475_, 1);
v___x_3477_ = l_Lean_Syntax_Range_includes(v_val_3476_, v___y_3470_, v___y_3467_, v___y_3467_);
lean_dec_ref(v___y_3470_);
if (v___x_3477_ == 0)
{
lean_dec(v_val_3476_);
lean_dec(v___y_3471_);
lean_dec(v___y_3464_);
v___y_3431_ = v___y_3463_;
v___y_3432_ = v___y_3465_;
v___y_3433_ = v___y_3467_;
v___y_3434_ = v___y_3466_;
v___y_3435_ = v___y_3468_;
v___y_3436_ = v___y_3469_;
v_edits_3437_ = v_edits_3472_;
goto v___jp_3430_;
}
else
{
lean_object* v_toCold_3478_; lean_object* v_fileMap_3479_; lean_object* v_start_3480_; lean_object* v_stop_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3498_; 
v_toCold_3478_ = lean_ctor_get(v___y_3473_, 0);
v_fileMap_3479_ = lean_ctor_get(v_toCold_3478_, 1);
v_start_3480_ = lean_ctor_get(v_val_3476_, 0);
v_stop_3481_ = lean_ctor_get(v_val_3476_, 1);
v_isSharedCheck_3498_ = !lean_is_exclusive(v_val_3476_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3483_ = v_val_3476_;
v_isShared_3484_ = v_isSharedCheck_3498_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_stop_3481_);
lean_inc(v_start_3480_);
lean_dec(v_val_3476_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3498_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; uint8_t v___x_3487_; 
v___x_3485_ = lean_unsigned_to_nat(1u);
v___x_3486_ = lean_nat_add(v_start_3480_, v___x_3485_);
v___x_3487_ = lean_nat_dec_le(v___x_3486_, v___y_3464_);
lean_dec(v___x_3486_);
if (v___x_3487_ == 0)
{
lean_del_object(v___x_3483_);
lean_dec(v_start_3480_);
lean_dec(v___y_3464_);
v___y_3443_ = v___y_3463_;
v___y_3444_ = v___y_3465_;
v___y_3445_ = v_fileMap_3479_;
v___y_3446_ = v___y_3466_;
v___y_3447_ = v___y_3467_;
v___y_3448_ = v___y_3468_;
v_stop_3449_ = v_stop_3481_;
v___y_3450_ = v___y_3469_;
v___y_3451_ = v___y_3471_;
v_edits_3452_ = v_edits_3472_;
goto v___jp_3442_;
}
else
{
lean_object* v_source_3488_; uint8_t v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3493_; 
v_source_3488_ = lean_ctor_get(v_fileMap_3479_, 0);
v___x_3489_ = 2;
v___x_3490_ = lean_string_utf8_extract(v_source_3488_, v_start_3480_, v___y_3464_);
lean_dec(v___y_3464_);
lean_dec(v_start_3480_);
v___x_3491_ = lean_box(v___x_3489_);
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 1, v___x_3490_);
lean_ctor_set(v___x_3483_, 0, v___x_3491_);
v___x_3493_ = v___x_3483_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v___x_3491_);
lean_ctor_set(v_reuseFailAlloc_3497_, 1, v___x_3490_);
v___x_3493_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3494_ = lean_mk_empty_array_with_capacity(v___x_3485_);
v___x_3495_ = lean_array_push(v___x_3494_, v___x_3493_);
v___x_3496_ = l_Array_append___redArg(v___x_3495_, v_edits_3472_);
lean_dec_ref(v_edits_3472_);
v___y_3443_ = v___y_3463_;
v___y_3444_ = v___y_3465_;
v___y_3445_ = v_fileMap_3479_;
v___y_3446_ = v___y_3466_;
v___y_3447_ = v___y_3467_;
v___y_3448_ = v___y_3468_;
v_stop_3449_ = v_stop_3481_;
v___y_3450_ = v___y_3469_;
v___y_3451_ = v___y_3471_;
v_edits_3452_ = v___x_3496_;
goto v___jp_3442_;
}
}
}
}
}
else
{
lean_dec(v___x_3475_);
lean_dec(v___y_3471_);
lean_dec_ref(v___y_3470_);
lean_dec(v___y_3464_);
v___y_3431_ = v___y_3463_;
v___y_3432_ = v___y_3465_;
v___y_3433_ = v___y_3467_;
v___y_3434_ = v___y_3466_;
v___y_3435_ = v___y_3468_;
v___y_3436_ = v___y_3469_;
v_edits_3437_ = v_edits_3472_;
goto v___jp_3430_;
}
}
}
v___jp_3500_:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
lean_inc_ref(v___y_3508_);
v___x_3511_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3511_, 0, v___y_3507_);
lean_ctor_set(v___x_3511_, 1, v___y_3510_);
lean_ctor_set(v___x_3511_, 2, v___y_3508_);
v___x_3512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3512_, 0, v___x_3499_);
lean_ctor_set(v___x_3512_, 1, v___x_3511_);
v___x_3513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3513_, 0, v___y_3502_);
lean_ctor_set(v___x_3513_, 1, v___x_3512_);
v___x_3514_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3513_);
v___x_3515_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v___x_3514_, v___y_3277_, v___y_3278_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_messageData_x3f_3516_; 
lean_dec_ref_known(v___x_3515_, 1);
v_messageData_x3f_3516_ = lean_ctor_get(v___y_3508_, 4);
if (lean_obj_tag(v_messageData_x3f_3516_) == 1)
{
lean_object* v_start_3517_; lean_object* v_stop_3518_; lean_object* v_val_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; uint8_t v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; 
v_start_3517_ = lean_ctor_get(v___y_3509_, 0);
lean_inc(v_start_3517_);
v_stop_3518_ = lean_ctor_get(v___y_3509_, 1);
lean_inc(v_stop_3518_);
v_val_3519_ = lean_ctor_get(v_messageData_x3f_3516_, 0);
v___x_3520_ = lean_box(0);
lean_inc(v_val_3519_);
v___x_3521_ = l_Lean_MessageData_format(v_val_3519_, v___x_3520_);
v___x_3522_ = 0;
v___x_3523_ = l_Std_Format_defWidth;
v___x_3524_ = lean_unsigned_to_nat(0u);
v___x_3525_ = l_Std_Format_pretty(v___x_3521_, v___x_3523_, v___x_3524_, v___x_3524_);
v___x_3526_ = lean_box(v___x_3522_);
v___x_3527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3526_);
lean_ctor_set(v___x_3527_, 1, v___x_3525_);
v___x_3528_ = lean_unsigned_to_nat(1u);
v___x_3529_ = lean_mk_empty_array_with_capacity(v___x_3528_);
v___x_3530_ = lean_array_push(v___x_3529_, v___x_3527_);
v___y_3463_ = v___y_3501_;
v___y_3464_ = v_start_3517_;
v___y_3465_ = v___y_3503_;
v___y_3466_ = v___y_3505_;
v___y_3467_ = v___y_3504_;
v___y_3468_ = v___y_3506_;
v___y_3469_ = v___y_3508_;
v___y_3470_ = v___y_3509_;
v___y_3471_ = v_stop_3518_;
v_edits_3472_ = v___x_3530_;
v___y_3473_ = v___y_3277_;
goto v___jp_3462_;
}
else
{
lean_object* v_toCold_3531_; lean_object* v_fileMap_3532_; lean_object* v_start_3533_; lean_object* v_stop_3534_; lean_object* v_source_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; 
v_toCold_3531_ = lean_ctor_get(v___y_3277_, 0);
v_fileMap_3532_ = lean_ctor_get(v_toCold_3531_, 1);
v_start_3533_ = lean_ctor_get(v___y_3509_, 0);
lean_inc(v_start_3533_);
v_stop_3534_ = lean_ctor_get(v___y_3509_, 1);
lean_inc(v_stop_3534_);
v_source_3535_ = lean_ctor_get(v_fileMap_3532_, 0);
v___x_3536_ = lean_string_utf8_extract(v_source_3535_, v_start_3533_, v_stop_3534_);
lean_inc_ref(v___y_3503_);
v___x_3537_ = l_Lean_Meta_Hint_readableDiff(v___x_3536_, v___y_3503_, v___y_3506_);
v___y_3463_ = v___y_3501_;
v___y_3464_ = v_start_3533_;
v___y_3465_ = v___y_3503_;
v___y_3466_ = v___y_3505_;
v___y_3467_ = v___y_3504_;
v___y_3468_ = v___y_3506_;
v___y_3469_ = v___y_3508_;
v___y_3470_ = v___y_3509_;
v___y_3471_ = v_stop_3534_;
v_edits_3472_ = v___x_3537_;
v___y_3473_ = v___y_3277_;
goto v___jp_3462_;
}
}
else
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
lean_dec_ref(v___y_3509_);
lean_dec_ref(v___y_3508_);
lean_dec_ref(v___y_3505_);
lean_dec_ref(v___y_3503_);
lean_dec(v___y_3501_);
lean_dec_ref(v_b_3276_);
lean_dec(v_ref_3272_);
lean_dec(v_codeActionPrefix_x3f_3271_);
v_a_3538_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3540_ = v___x_3515_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3515_);
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
v___jp_3546_:
{
lean_object* v_toCodeActionTitle_x3f_3556_; lean_object* v___x_3557_; 
v_toCodeActionTitle_x3f_3556_ = lean_ctor_get(v___y_3553_, 5);
v___x_3557_ = l_Lean_Syntax_ofRange(v___y_3555_, v___x_3325_);
if (lean_obj_tag(v_toCodeActionTitle_x3f_3556_) == 0)
{
if (lean_obj_tag(v_codeActionPrefix_x3f_3271_) == 0)
{
lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3558_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__36));
v___x_3559_ = lean_string_append(v___x_3558_, v___y_3548_);
v___y_3501_ = v___y_3547_;
v___y_3502_ = v___x_3557_;
v___y_3503_ = v___y_3548_;
v___y_3504_ = v___y_3550_;
v___y_3505_ = v___y_3549_;
v___y_3506_ = v___y_3552_;
v___y_3507_ = v___y_3551_;
v___y_3508_ = v___y_3553_;
v___y_3509_ = v___y_3554_;
v___y_3510_ = v___x_3559_;
goto v___jp_3500_;
}
else
{
lean_object* v_val_3560_; lean_object* v___x_3561_; 
v_val_3560_ = lean_ctor_get(v_codeActionPrefix_x3f_3271_, 0);
lean_inc(v_val_3560_);
v___x_3561_ = lean_string_append(v_val_3560_, v___y_3548_);
v___y_3501_ = v___y_3547_;
v___y_3502_ = v___x_3557_;
v___y_3503_ = v___y_3548_;
v___y_3504_ = v___y_3550_;
v___y_3505_ = v___y_3549_;
v___y_3506_ = v___y_3552_;
v___y_3507_ = v___y_3551_;
v___y_3508_ = v___y_3553_;
v___y_3509_ = v___y_3554_;
v___y_3510_ = v___x_3561_;
goto v___jp_3500_;
}
}
else
{
lean_object* v_val_3562_; lean_object* v___x_3563_; 
v_val_3562_ = lean_ctor_get(v_toCodeActionTitle_x3f_3556_, 0);
lean_inc(v_val_3562_);
lean_inc_ref(v___y_3548_);
v___x_3563_ = lean_apply_1(v_val_3562_, v___y_3548_);
v___y_3501_ = v___y_3547_;
v___y_3502_ = v___x_3557_;
v___y_3503_ = v___y_3548_;
v___y_3504_ = v___y_3550_;
v___y_3505_ = v___y_3549_;
v___y_3506_ = v___y_3552_;
v___y_3507_ = v___y_3551_;
v___y_3508_ = v___y_3553_;
v___y_3509_ = v___y_3554_;
v___y_3510_ = v___x_3563_;
goto v___jp_3500_;
}
}
v___jp_3564_:
{
uint8_t v___x_3566_; lean_object* v___x_3567_; 
v___x_3566_ = 0;
v___x_3567_ = l_Lean_Syntax_getRange_x3f(v___y_3565_, v___x_3566_);
lean_dec(v___y_3565_);
if (lean_obj_tag(v___x_3567_) == 1)
{
lean_object* v_val_3568_; lean_object* v___x_3569_; 
v_val_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc_n(v_val_3568_, 2);
lean_dec_ref_known(v___x_3567_, 1);
lean_inc_ref(v_toTryThisSuggestion_3328_);
v___x_3569_ = l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(v_toTryThisSuggestion_3328_, v_val_3568_, v___y_3277_, v___y_3278_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v_a_3570_; lean_object* v_range_3571_; lean_object* v_newText_3572_; lean_object* v___x_3573_; 
v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
lean_inc(v_a_3570_);
lean_dec_ref_known(v___x_3569_, 1);
v_range_3571_ = lean_ctor_get(v_a_3570_, 0);
lean_inc_ref(v_range_3571_);
v_newText_3572_ = lean_ctor_get(v_a_3570_, 1);
lean_inc_ref(v_newText_3572_);
v___x_3573_ = l_Lean_Syntax_getRange_x3f(v_ref_3272_, v___x_3566_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_inc(v_val_3568_);
lean_inc_ref(v_toTryThisSuggestion_3328_);
lean_inc(v_previewSpan_x3f_3330_);
v___y_3547_ = v_previewSpan_x3f_3330_;
v___y_3548_ = v_newText_3572_;
v___y_3549_ = v_range_3571_;
v___y_3550_ = v___x_3566_;
v___y_3551_ = v_a_3570_;
v___y_3552_ = v_diffGranularity_3331_;
v___y_3553_ = v_toTryThisSuggestion_3328_;
v___y_3554_ = v_val_3568_;
v___y_3555_ = v_val_3568_;
goto v___jp_3546_;
}
else
{
lean_object* v_val_3574_; 
v_val_3574_ = lean_ctor_get(v___x_3573_, 0);
lean_inc(v_val_3574_);
lean_dec_ref_known(v___x_3573_, 1);
lean_inc_ref(v_toTryThisSuggestion_3328_);
lean_inc(v_previewSpan_x3f_3330_);
v___y_3547_ = v_previewSpan_x3f_3330_;
v___y_3548_ = v_newText_3572_;
v___y_3549_ = v_range_3571_;
v___y_3550_ = v___x_3566_;
v___y_3551_ = v_a_3570_;
v___y_3552_ = v_diffGranularity_3331_;
v___y_3553_ = v_toTryThisSuggestion_3328_;
v___y_3554_ = v_val_3568_;
v___y_3555_ = v_val_3574_;
goto v___jp_3546_;
}
}
else
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
lean_dec(v_val_3568_);
lean_dec_ref(v_b_3276_);
lean_dec(v_ref_3272_);
lean_dec(v_codeActionPrefix_x3f_3271_);
v_a_3575_ = lean_ctor_get(v___x_3569_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3569_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___x_3569_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3569_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
}
else
{
lean_dec(v___x_3567_);
v_a_3281_ = v_b_3276_;
goto v___jp_3280_;
}
}
}
v___jp_3280_:
{
size_t v___x_3282_; size_t v___x_3283_; 
v___x_3282_ = ((size_t)1ULL);
v___x_3283_ = lean_usize_add(v_i_3275_, v___x_3282_);
v_i_3275_ = v___x_3283_;
v_b_3276_ = v_a_3281_;
goto _start;
}
v___jp_3285_:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; 
v___x_3287_ = l_Lean_MessageData_nestD(v___y_3286_);
v___x_3288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3288_, 0, v_b_3276_);
lean_ctor_set(v___x_3288_, 1, v___x_3287_);
v_a_3281_ = v___x_3288_;
goto v___jp_3280_;
}
v___jp_3289_:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3291_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3292_ = lean_unsigned_to_nat(2u);
v___x_3293_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3);
v___x_3294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3294_, 0, v___x_3293_);
lean_ctor_set(v___x_3294_, 1, v___y_3290_);
v___x_3295_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3292_);
lean_ctor_set(v___x_3295_, 1, v___x_3294_);
v___x_3296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3296_, 0, v___x_3291_);
lean_ctor_set(v___x_3296_, 1, v___x_3295_);
v___y_3286_ = v___x_3296_;
goto v___jp_3285_;
}
v___jp_3297_:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3301_, 0, v___y_3299_);
lean_ctor_set(v___x_3301_, 1, v___y_3300_);
v___x_3302_ = l_Lean_stringToMessageData(v___y_3298_);
v___x_3303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3301_);
lean_ctor_set(v___x_3303_, 1, v___x_3302_);
v___y_3286_ = v___x_3303_;
goto v___jp_3285_;
}
v___jp_3304_:
{
lean_object* v___x_3309_; uint64_t v_javascriptHash_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; uint8_t v___x_3322_; 
v___x_3309_ = ((lean_object*)(l_Lean_Meta_Hint_tryThisDiffWidget));
v_javascriptHash_3310_ = lean_ctor_get_uint64(v___x_3309_, sizeof(void*)*1);
v___x_3311_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8));
v___x_3312_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3312_, 0, v___x_3311_);
lean_ctor_set(v___x_3312_, 1, v___y_3306_);
lean_ctor_set_uint64(v___x_3312_, sizeof(void*)*2, v_javascriptHash_3310_);
v___x_3313_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3313_, 0, v___y_3308_);
v___x_3314_ = l_Lean_MessageData_ofFormat(v___x_3313_);
v___x_3315_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3312_);
lean_ctor_set(v___x_3315_, 1, v___x_3314_);
v___x_3316_ = l_Lean_stringToMessageData(v___y_3307_);
v___x_3317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3316_);
lean_ctor_set(v___x_3317_, 1, v___x_3315_);
v___x_3318_ = l_Lean_stringToMessageData(v___y_3305_);
v___x_3319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3317_);
lean_ctor_set(v___x_3319_, 1, v___x_3318_);
v___x_3320_ = lean_array_get_size(v_suggestions_3269_);
v___x_3321_ = lean_unsigned_to_nat(1u);
v___x_3322_ = lean_nat_dec_eq(v___x_3320_, v___x_3321_);
if (v___x_3322_ == 0)
{
v___y_3290_ = v___x_3319_;
goto v___jp_3289_;
}
else
{
if (v_forceList_3270_ == 0)
{
lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3323_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
lean_ctor_set(v___x_3324_, 1, v___x_3319_);
v___y_3286_ = v___x_3324_;
goto v___jp_3285_;
}
else
{
v___y_3290_ = v___x_3319_;
goto v___jp_3289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___boxed(lean_object* v_suggestions_3584_, lean_object* v_forceList_3585_, lean_object* v_codeActionPrefix_x3f_3586_, lean_object* v_ref_3587_, lean_object* v_as_3588_, lean_object* v_sz_3589_, lean_object* v_i_3590_, lean_object* v_b_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
uint8_t v_forceList_boxed_3595_; size_t v_sz_boxed_3596_; size_t v_i_boxed_3597_; lean_object* v_res_3598_; 
v_forceList_boxed_3595_ = lean_unbox(v_forceList_3585_);
v_sz_boxed_3596_ = lean_unbox_usize(v_sz_3589_);
lean_dec(v_sz_3589_);
v_i_boxed_3597_ = lean_unbox_usize(v_i_3590_);
lean_dec(v_i_3590_);
v_res_3598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3584_, v_forceList_boxed_3595_, v_codeActionPrefix_x3f_3586_, v_ref_3587_, v_as_3588_, v_sz_boxed_3596_, v_i_boxed_3597_, v_b_3591_, v___y_3592_, v___y_3593_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec_ref(v_as_3588_);
lean_dec_ref(v_suggestions_3584_);
return v_res_3598_;
}
}
static lean_object* _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0(void){
_start:
{
lean_object* v___x_3599_; lean_object* v_msg_3600_; 
v___x_3599_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v_msg_3600_ = l_Lean_stringToMessageData(v___x_3599_);
return v_msg_3600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage(lean_object* v_suggestions_3601_, lean_object* v_ref_3602_, lean_object* v_codeActionPrefix_x3f_3603_, uint8_t v_forceList_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_){
_start:
{
lean_object* v_msg_3608_; size_t v_sz_3609_; size_t v___x_3610_; lean_object* v___x_3611_; 
v_msg_3608_ = lean_obj_once(&l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0, &l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0_once, _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0);
v_sz_3609_ = lean_array_size(v_suggestions_3601_);
v___x_3610_ = ((size_t)0ULL);
v___x_3611_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3601_, v_forceList_3604_, v_codeActionPrefix_x3f_3603_, v_ref_3602_, v_suggestions_3601_, v_sz_3609_, v___x_3610_, v_msg_3608_, v_a_3605_, v_a_3606_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage___boxed(lean_object* v_suggestions_3612_, lean_object* v_ref_3613_, lean_object* v_codeActionPrefix_x3f_3614_, lean_object* v_forceList_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_){
_start:
{
uint8_t v_forceList_boxed_3619_; lean_object* v_res_3620_; 
v_forceList_boxed_3619_ = lean_unbox(v_forceList_3615_);
v_res_3620_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3612_, v_ref_3613_, v_codeActionPrefix_x3f_3614_, v_forceList_boxed_3619_, v_a_3616_, v_a_3617_);
lean_dec(v_a_3617_);
lean_dec_ref(v_a_3616_);
lean_dec_ref(v_suggestions_3612_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(lean_object* v_t_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v___x_3625_; 
v___x_3625_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3621_, v___y_3623_);
return v___x_3625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___boxed(lean_object* v_t_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_){
_start:
{
lean_object* v_res_3630_; 
v_res_3630_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(v_t_3626_, v___y_3627_, v___y_3628_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
return v_res_3630_;
}
}
static lean_object* _init_l_Lean_MessageData_hint___closed__3(void){
_start:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = ((lean_object*)(l_Lean_MessageData_hint___closed__2));
v___x_3636_ = l_Lean_stringToMessageData(v___x_3635_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint(lean_object* v_hint_3637_, lean_object* v_suggestions_3638_, lean_object* v_ref_x3f_3639_, lean_object* v_codeActionPrefix_x3f_3640_, uint8_t v_forceList_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_){
_start:
{
lean_object* v___y_3646_; 
if (lean_obj_tag(v_ref_x3f_3639_) == 0)
{
lean_object* v_ref_3661_; 
v_ref_3661_ = lean_ctor_get(v_a_3642_, 2);
lean_inc(v_ref_3661_);
v___y_3646_ = v_ref_3661_;
goto v___jp_3645_;
}
else
{
lean_object* v_val_3662_; 
v_val_3662_ = lean_ctor_get(v_ref_x3f_3639_, 0);
lean_inc(v_val_3662_);
lean_dec_ref_known(v_ref_x3f_3639_, 1);
v___y_3646_ = v_val_3662_;
goto v___jp_3645_;
}
v___jp_3645_:
{
lean_object* v___x_3647_; 
v___x_3647_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3638_, v___y_3646_, v_codeActionPrefix_x3f_3640_, v_forceList_3641_, v_a_3642_, v_a_3643_);
if (lean_obj_tag(v___x_3647_) == 0)
{
lean_object* v_a_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3660_; 
v_a_3648_ = lean_ctor_get(v___x_3647_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3647_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3650_ = v___x_3647_;
v_isShared_3651_ = v_isSharedCheck_3660_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_a_3648_);
lean_dec(v___x_3647_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3660_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3658_; 
v___x_3652_ = ((lean_object*)(l_Lean_MessageData_hint___closed__1));
v___x_3653_ = lean_obj_once(&l_Lean_MessageData_hint___closed__3, &l_Lean_MessageData_hint___closed__3_once, _init_l_Lean_MessageData_hint___closed__3);
v___x_3654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3653_);
lean_ctor_set(v___x_3654_, 1, v_hint_3637_);
v___x_3655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3654_);
lean_ctor_set(v___x_3655_, 1, v_a_3648_);
v___x_3656_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3652_);
lean_ctor_set(v___x_3656_, 1, v___x_3655_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set(v___x_3650_, 0, v___x_3656_);
v___x_3658_ = v___x_3650_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3656_);
v___x_3658_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
return v___x_3658_;
}
}
}
else
{
lean_dec_ref(v_hint_3637_);
return v___x_3647_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint___boxed(lean_object* v_hint_3663_, lean_object* v_suggestions_3664_, lean_object* v_ref_x3f_3665_, lean_object* v_codeActionPrefix_x3f_3666_, lean_object* v_forceList_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_){
_start:
{
uint8_t v_forceList_boxed_3671_; lean_object* v_res_3672_; 
v_forceList_boxed_3671_ = lean_unbox(v_forceList_3667_);
v_res_3672_ = l_Lean_MessageData_hint(v_hint_3663_, v_suggestions_3664_, v_ref_x3f_3665_, v_codeActionPrefix_x3f_3666_, v_forceList_boxed_3671_, v_a_3668_, v_a_3669_);
lean_dec(v_a_3669_);
lean_dec_ref(v_a_3668_);
lean_dec_ref(v_suggestions_3664_);
return v_res_3672_;
}
}
lean_object* runtime_initialize_Lean_Meta_TryThis(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Diff(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Csimp(uint8_t builtin);
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
res = runtime_initialize_Init_Data_String_Csimp(builtin);
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
lean_object* initialize_Init_Data_String_Csimp(uint8_t builtin);
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
res = initialize_Init_Data_String_Csimp(builtin);
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
