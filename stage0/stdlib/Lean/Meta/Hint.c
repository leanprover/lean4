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
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1(size_t v_sz_11_, size_t v_i_12_, lean_object* v_bs_13_){
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
size_t v_sz_11_ = stack[0].m_num;
size_t v_i_12_ = stack[1].m_num;
lean_object* v_bs_13_ = stack[2].m_obj;
lean_object* v_res_22_;
v_res_22_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1(v_sz_11_, v_i_12_, v_bs_13_);
stack->m_obj
 = v_res_22_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1___boxed(lean_object* v_sz_23_, lean_object* v_i_24_, lean_object* v_bs_25_){
_start:
{
size_t v_sz_boxed_26_; size_t v_i_boxed_27_; lean_object* v_res_28_; 
v_sz_boxed_26_ = lean_unbox_usize(v_sz_23_);
lean_dec(v_sz_23_);
v_i_boxed_27_ = lean_unbox_usize(v_i_24_);
lean_dec(v_i_24_);
v_res_28_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1(v_sz_boxed_26_, v_i_boxed_27_, v_bs_25_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1(lean_object* v_a_29_){
_start:
{
size_t v_sz_30_; size_t v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v_sz_30_ = lean_array_size(v_a_29_);
v___x_31_ = ((size_t)0ULL);
v___x_32_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1_spec__1(v_sz_30_, v___x_31_, v_a_29_);
v___x_33_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
return v___x_33_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0(size_t v_sz_54_, size_t v_i_55_, lean_object* v_bs_56_){
_start:
{
uint8_t v___x_57_; 
v___x_57_ = lean_usize_dec_lt(v_i_55_, v_sz_54_);
if (v___x_57_ == 0)
{
return v_bs_56_;
}
else
{
lean_object* v_v_58_; lean_object* v_fst_59_; lean_object* v_snd_60_; lean_object* v___x_62_; uint8_t v_isShared_63_; uint8_t v_isSharedCheck_103_; 
v_v_58_ = lean_array_uget(v_bs_56_, v_i_55_);
v_fst_59_ = lean_ctor_get(v_v_58_, 0);
v_snd_60_ = lean_ctor_get(v_v_58_, 1);
v_isSharedCheck_103_ = !lean_is_exclusive(v_v_58_);
if (v_isSharedCheck_103_ == 0)
{
v___x_62_ = v_v_58_;
v_isShared_63_ = v_isSharedCheck_103_;
goto v_resetjp_61_;
}
else
{
lean_inc(v_snd_60_);
lean_inc(v_fst_59_);
lean_dec(v_v_58_);
v___x_62_ = lean_box(0);
v_isShared_63_ = v_isSharedCheck_103_;
goto v_resetjp_61_;
}
v_resetjp_61_:
{
lean_object* v___x_64_; lean_object* v_bs_x27_65_; lean_object* v___y_67_; uint8_t v___x_72_; 
v___x_64_ = lean_unsigned_to_nat(0u);
v_bs_x27_65_ = lean_array_uset(v_bs_56_, v_i_55_, v___x_64_);
v___x_72_ = lean_unbox(v_fst_59_);
lean_dec(v_fst_59_);
switch(v___x_72_)
{
case 0:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_73_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__3));
v___x_74_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__4));
v___x_75_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_75_, 0, v_snd_60_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 1, v___x_75_);
lean_ctor_set(v___x_62_, 0, v___x_74_);
v___x_77_ = v___x_62_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_74_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v___x_75_);
v___x_77_ = v_reuseFailAlloc_82_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_78_ = lean_box(0);
v___x_79_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_77_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_73_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = l_Lean_Json_mkObj(v___x_80_);
lean_dec_ref_known(v___x_80_, 2);
v___y_67_ = v___x_81_;
goto v___jp_66_;
}
}
case 1:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_83_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__7));
v___x_84_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__4));
v___x_85_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_85_, 0, v_snd_60_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 1, v___x_85_);
lean_ctor_set(v___x_62_, 0, v___x_84_);
v___x_87_ = v___x_62_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_84_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v___x_85_);
v___x_87_ = v_reuseFailAlloc_92_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_88_ = lean_box(0);
v___x_89_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_83_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
v___x_91_ = l_Lean_Json_mkObj(v___x_90_);
lean_dec_ref_known(v___x_90_, 2);
v___y_67_ = v___x_91_;
goto v___jp_66_;
}
}
default: 
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_97_; 
v___x_93_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__10));
v___x_94_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___closed__4));
v___x_95_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_95_, 0, v_snd_60_);
if (v_isShared_63_ == 0)
{
lean_ctor_set(v___x_62_, 1, v___x_95_);
lean_ctor_set(v___x_62_, 0, v___x_94_);
v___x_97_ = v___x_62_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v___x_94_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v___x_95_);
v___x_97_ = v_reuseFailAlloc_102_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_98_ = lean_box(0);
v___x_99_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_97_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v___x_100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_93_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
v___x_101_ = l_Lean_Json_mkObj(v___x_100_);
lean_dec_ref_known(v___x_100_, 2);
v___y_67_ = v___x_101_;
goto v___jp_66_;
}
}
}
v___jp_66_:
{
size_t v___x_68_; size_t v___x_69_; lean_object* v___x_70_; 
v___x_68_ = ((size_t)1ULL);
v___x_69_ = lean_usize_add(v_i_55_, v___x_68_);
v___x_70_ = lean_array_uset(v_bs_x27_65_, v_i_55_, v___y_67_);
v_i_55_ = v___x_69_;
v_bs_56_ = v___x_70_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_54_ = stack[0].m_num;
size_t v_i_55_ = stack[1].m_num;
lean_object* v_bs_56_ = stack[2].m_obj;
lean_object* v_res_104_;
v_res_104_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0(v_sz_54_, v_i_55_, v_bs_56_);
stack->m_obj
 = v_res_104_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0___boxed(lean_object* v_sz_105_, lean_object* v_i_106_, lean_object* v_bs_107_){
_start:
{
size_t v_sz_boxed_108_; size_t v_i_boxed_109_; lean_object* v_res_110_; 
v_sz_boxed_108_ = lean_unbox_usize(v_sz_105_);
lean_dec(v_sz_105_);
v_i_boxed_109_ = lean_unbox_usize(v_i_106_);
lean_dec(v_i_106_);
v_res_110_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0(v_sz_boxed_108_, v_i_boxed_109_, v_bs_107_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson(lean_object* v_ds_111_){
_start:
{
size_t v_sz_112_; size_t v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_sz_112_ = lean_array_size(v_ds_111_);
v___x_113_ = ((size_t)0ULL);
v___x_114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__0(v_sz_112_, v___x_113_, v_ds_111_);
v___x_115_ = l_Lean_Array_toJson___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson_spec__1(v___x_114_);
return v___x_115_;
}
}
static lean_object* _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_116_; lean_object* v___x_117_; 
v___x_116_ = 821;
v___x_117_ = lean_box_uint32(v___x_116_);
return v___x_117_;
}
}
static lean_object* _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_118_ = lean_box(0);
v___x_119_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0___boxed__const__1;
v___x_120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v___x_118_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1(lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
if (lean_obj_tag(v_a_121_) == 0)
{
lean_object* v___x_123_; 
v___x_123_ = lean_array_to_list(v_a_122_);
return v___x_123_;
}
else
{
lean_object* v_head_124_; lean_object* v_tail_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_135_; 
v_head_124_ = lean_ctor_get(v_a_121_, 0);
v_tail_125_ = lean_ctor_get(v_a_121_, 1);
v_isSharedCheck_135_ = !lean_is_exclusive(v_a_121_);
if (v_isSharedCheck_135_ == 0)
{
v___x_127_ = v_a_121_;
v_isShared_128_ = v_isSharedCheck_135_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_tail_125_);
lean_inc(v_head_124_);
lean_dec(v_a_121_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_135_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_129_ = lean_obj_once(&l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0, &l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0_once, _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1___closed__0);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v___x_129_);
v___x_131_ = v___x_127_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_head_124_);
lean_ctor_set(v_reuseFailAlloc_134_, 1, v___x_129_);
v___x_131_ = v_reuseFailAlloc_134_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_132_; 
v___x_132_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_122_, v___x_131_);
v_a_121_ = v_tail_125_;
v_a_122_ = v___x_132_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_136_; lean_object* v___x_137_; 
v___x_136_ = 818;
v___x_137_ = lean_box_uint32(v___x_136_);
return v___x_137_;
}
}
static lean_object* _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0(void){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = lean_box(0);
v___x_139_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0___boxed__const__1;
v___x_140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_139_);
lean_ctor_set(v___x_140_, 1, v___x_138_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0(lean_object* v_a_141_, lean_object* v_a_142_){
_start:
{
if (lean_obj_tag(v_a_141_) == 0)
{
lean_object* v___x_143_; 
v___x_143_ = lean_array_to_list(v_a_142_);
return v___x_143_;
}
else
{
lean_object* v_head_144_; lean_object* v_tail_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_155_; 
v_head_144_ = lean_ctor_get(v_a_141_, 0);
v_tail_145_ = lean_ctor_get(v_a_141_, 1);
v_isSharedCheck_155_ = !lean_is_exclusive(v_a_141_);
if (v_isSharedCheck_155_ == 0)
{
v___x_147_ = v_a_141_;
v_isShared_148_ = v_isSharedCheck_155_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_tail_145_);
lean_inc(v_head_144_);
lean_dec(v_a_141_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_155_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_149_; lean_object* v___x_151_; 
v___x_149_ = lean_obj_once(&l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0, &l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0_once, _init_l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0___closed__0);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 1, v___x_149_);
v___x_151_ = v___x_147_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_head_144_);
lean_ctor_set(v_reuseFailAlloc_154_, 1, v___x_149_);
v___x_151_ = v_reuseFailAlloc_154_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
lean_object* v___x_152_; 
v___x_152_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(v_a_142_, v___x_151_);
v_a_141_ = v_tail_145_;
v_a_142_ = v___x_152_;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2(size_t v_sz_158_, size_t v_i_159_, lean_object* v_bs_160_){
_start:
{
uint8_t v___x_161_; 
v___x_161_ = lean_usize_dec_lt(v_i_159_, v_sz_158_);
if (v___x_161_ == 0)
{
return v_bs_160_;
}
else
{
lean_object* v_v_162_; lean_object* v_fst_163_; lean_object* v_snd_164_; lean_object* v___x_165_; lean_object* v_bs_x27_166_; lean_object* v___y_168_; uint8_t v___x_173_; 
v_v_162_ = lean_array_uget_borrowed(v_bs_160_, v_i_159_);
v_fst_163_ = lean_ctor_get(v_v_162_, 0);
lean_inc(v_fst_163_);
v_snd_164_ = lean_ctor_get(v_v_162_, 1);
lean_inc(v_snd_164_);
v___x_165_ = lean_unsigned_to_nat(0u);
v_bs_x27_166_ = lean_array_uset(v_bs_160_, v_i_159_, v___x_165_);
v___x_173_ = lean_unbox(v_fst_163_);
lean_dec(v_fst_163_);
switch(v___x_173_)
{
case 0:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_174_ = l_String_toListImpl(v_snd_164_);
v___x_175_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_176_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__0(v___x_174_, v___x_175_);
v___x_177_ = lean_string_mk(v___x_176_);
v___y_168_ = v___x_177_;
goto v___jp_167_;
}
case 1:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_178_ = l_String_toListImpl(v_snd_164_);
v___x_179_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_180_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__1(v___x_178_, v___x_179_);
v___x_181_ = lean_string_mk(v___x_180_);
v___y_168_ = v___x_181_;
goto v___jp_167_;
}
default: 
{
v___y_168_ = v_snd_164_;
goto v___jp_167_;
}
}
v___jp_167_:
{
size_t v___x_169_; size_t v___x_170_; lean_object* v___x_171_; 
v___x_169_ = ((size_t)1ULL);
v___x_170_ = lean_usize_add(v_i_159_, v___x_169_);
v___x_171_ = lean_array_uset(v_bs_x27_166_, v_i_159_, v___y_168_);
v_i_159_ = v___x_170_;
v_bs_160_ = v___x_171_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_sz_158_ = stack[0].m_num;
size_t v_i_159_ = stack[1].m_num;
lean_object* v_bs_160_ = stack[2].m_obj;
lean_object* v_res_182_;
v_res_182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2(v_sz_158_, v_i_159_, v_bs_160_);
stack->m_obj
 = v_res_182_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___boxed(lean_object* v_sz_183_, lean_object* v_i_184_, lean_object* v_bs_185_){
_start:
{
size_t v_sz_boxed_186_; size_t v_i_boxed_187_; lean_object* v_res_188_; 
v_sz_boxed_186_ = lean_unbox_usize(v_sz_183_);
lean_dec(v_sz_183_);
v_i_boxed_187_ = lean_unbox_usize(v_i_184_);
lean_dec(v_i_184_);
v_res_188_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2(v_sz_boxed_186_, v_i_boxed_187_, v_bs_185_);
return v_res_188_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(lean_object* v_as_189_, size_t v_i_190_, size_t v_stop_191_, lean_object* v_b_192_){
_start:
{
uint8_t v___x_193_; 
v___x_193_ = lean_usize_dec_eq(v_i_190_, v_stop_191_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v___x_195_; size_t v___x_196_; size_t v___x_197_; 
v___x_194_ = lean_array_uget_borrowed(v_as_189_, v_i_190_);
v___x_195_ = lean_string_append(v_b_192_, v___x_194_);
v___x_196_ = ((size_t)1ULL);
v___x_197_ = lean_usize_add(v_i_190_, v___x_196_);
v_i_190_ = v___x_197_;
v_b_192_ = v___x_195_;
goto _start;
}
else
{
return v_b_192_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_189_ = stack[0].m_obj;
size_t v_i_190_ = stack[1].m_num;
size_t v_stop_191_ = stack[2].m_num;
lean_object* v_b_192_ = stack[3].m_obj;
lean_object* v_res_199_;
v_res_199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_as_189_, v_i_190_, v_stop_191_, v_b_192_);
stack->m_obj
 = v_res_199_;
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
lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorIdx___impl(uint8_t v_x_221_){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_box(v_x_221_);
v___x_223_ = lean_obj_tag_nat(v___x_222_);
lean_dec(v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT void l_Lean_Meta_Hint_DiffGranularity_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_221_ = stack[0].m_num;
lean_object* v_res_224_;
v_res_224_ = l_Lean_Meta_Hint_DiffGranularity_ctorIdx___impl(v_x_221_);
stack->m_obj
 = v_res_224_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorIdx___impl___boxed(lean_object* v_x_225_){
_start:
{
uint8_t v_x_4__boxed_226_; lean_object* v_res_227_; 
v_x_4__boxed_226_ = lean_unbox(v_x_225_);
v_res_227_ = l_Lean_Meta_Hint_DiffGranularity_ctorIdx___impl(v_x_4__boxed_226_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim___redArg(lean_object* v_k_228_){
_start:
{
lean_inc(v_k_228_);
return v_k_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim___redArg___boxed(lean_object* v_k_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_Meta_Hint_DiffGranularity_ctorElim___redArg(v_k_229_);
lean_dec(v_k_229_);
return v_res_230_;
}
}
lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim(lean_object* v_motive_231_, lean_object* v_ctorIdx_232_, uint8_t v_t_233_, lean_object* v_h_234_, lean_object* v_k_235_){
_start:
{
lean_inc(v_k_235_);
return v_k_235_;
}
}
LEAN_EXPORT void l_Lean_Meta_Hint_DiffGranularity_ctorElim_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctorIdx_232_ = stack[1].m_obj;
uint8_t v_t_233_ = stack[2].m_num;
lean_object* v_k_235_ = stack[4].m_obj;
lean_object* v_res_236_;
v_res_236_ = l_Lean_Meta_Hint_DiffGranularity_ctorElim(lean_box(0), v_ctorIdx_232_, v_t_233_, lean_box(0), v_k_235_);
stack->m_obj
 = v_res_236_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_ctorElim___boxed(lean_object* v_motive_237_, lean_object* v_ctorIdx_238_, lean_object* v_t_239_, lean_object* v_h_240_, lean_object* v_k_241_){
_start:
{
uint8_t v_t_boxed_242_; lean_object* v_res_243_; 
v_t_boxed_242_ = lean_unbox(v_t_239_);
v_res_243_ = l_Lean_Meta_Hint_DiffGranularity_ctorElim(v_motive_237_, v_ctorIdx_238_, v_t_boxed_242_, v_h_240_, v_k_241_);
lean_dec(v_k_241_);
lean_dec(v_ctorIdx_238_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim___redArg(lean_object* v_auto_244_){
_start:
{
lean_inc(v_auto_244_);
return v_auto_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim___redArg___boxed(lean_object* v_auto_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_Meta_Hint_DiffGranularity_auto_elim___redArg(v_auto_245_);
lean_dec(v_auto_245_);
return v_res_246_;
}
}
lean_object* l_Lean_Meta_Hint_DiffGranularity_auto_elim(lean_object* v_motive_247_, uint8_t v_t_248_, lean_object* v_h_249_, lean_object* v_auto_250_){
_start:
{
lean_inc(v_auto_250_);
return v_auto_250_;
}
}
LEAN_EXPORT void l_Lean_Meta_Hint_DiffGranularity_auto_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_248_ = stack[1].m_num;
lean_object* v_auto_250_ = stack[3].m_obj;
lean_object* v_res_251_;
v_res_251_ = l_Lean_Meta_Hint_DiffGranularity_auto_elim(lean_box(0), v_t_248_, lean_box(0), v_auto_250_);
stack->m_obj
 = v_res_251_;
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
lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim(lean_object* v_motive_261_, uint8_t v_t_262_, lean_object* v_h_263_, lean_object* v_char_264_){
_start:
{
lean_inc(v_char_264_);
return v_char_264_;
}
}
LEAN_EXPORT void l_Lean_Meta_Hint_DiffGranularity_char_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_262_ = stack[1].m_num;
lean_object* v_char_264_ = stack[3].m_obj;
lean_object* v_res_265_;
v_res_265_ = l_Lean_Meta_Hint_DiffGranularity_char_elim(lean_box(0), v_t_262_, lean_box(0), v_char_264_);
stack->m_obj
 = v_res_265_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_char_elim___boxed(lean_object* v_motive_266_, lean_object* v_t_267_, lean_object* v_h_268_, lean_object* v_char_269_){
_start:
{
uint8_t v_t_boxed_270_; lean_object* v_res_271_; 
v_t_boxed_270_ = lean_unbox(v_t_267_);
v_res_271_ = l_Lean_Meta_Hint_DiffGranularity_char_elim(v_motive_266_, v_t_boxed_270_, v_h_268_, v_char_269_);
lean_dec(v_char_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim___redArg(lean_object* v_word_272_){
_start:
{
lean_inc(v_word_272_);
return v_word_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim___redArg___boxed(lean_object* v_word_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Meta_Hint_DiffGranularity_word_elim___redArg(v_word_273_);
lean_dec(v_word_273_);
return v_res_274_;
}
}
lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim(lean_object* v_motive_275_, uint8_t v_t_276_, lean_object* v_h_277_, lean_object* v_word_278_){
_start:
{
lean_inc(v_word_278_);
return v_word_278_;
}
}
LEAN_EXPORT void l_Lean_Meta_Hint_DiffGranularity_word_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_276_ = stack[1].m_num;
lean_object* v_word_278_ = stack[3].m_obj;
lean_object* v_res_279_;
v_res_279_ = l_Lean_Meta_Hint_DiffGranularity_word_elim(lean_box(0), v_t_276_, lean_box(0), v_word_278_);
stack->m_obj
 = v_res_279_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_word_elim___boxed(lean_object* v_motive_280_, lean_object* v_t_281_, lean_object* v_h_282_, lean_object* v_word_283_){
_start:
{
uint8_t v_t_boxed_284_; lean_object* v_res_285_; 
v_t_boxed_284_ = lean_unbox(v_t_281_);
v_res_285_ = l_Lean_Meta_Hint_DiffGranularity_word_elim(v_motive_280_, v_t_boxed_284_, v_h_282_, v_word_283_);
lean_dec(v_word_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim___redArg(lean_object* v_all_286_){
_start:
{
lean_inc(v_all_286_);
return v_all_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim___redArg___boxed(lean_object* v_all_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Meta_Hint_DiffGranularity_all_elim___redArg(v_all_287_);
lean_dec(v_all_287_);
return v_res_288_;
}
}
lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim(lean_object* v_motive_289_, uint8_t v_t_290_, lean_object* v_h_291_, lean_object* v_all_292_){
_start:
{
lean_inc(v_all_292_);
return v_all_292_;
}
}
LEAN_EXPORT void l_Lean_Meta_Hint_DiffGranularity_all_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_290_ = stack[1].m_num;
lean_object* v_all_292_ = stack[3].m_obj;
lean_object* v_res_293_;
v_res_293_ = l_Lean_Meta_Hint_DiffGranularity_all_elim(lean_box(0), v_t_290_, lean_box(0), v_all_292_);
stack->m_obj
 = v_res_293_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_all_elim___boxed(lean_object* v_motive_294_, lean_object* v_t_295_, lean_object* v_h_296_, lean_object* v_all_297_){
_start:
{
uint8_t v_t_boxed_298_; lean_object* v_res_299_; 
v_t_boxed_298_ = lean_unbox(v_t_295_);
v_res_299_ = l_Lean_Meta_Hint_DiffGranularity_all_elim(v_motive_294_, v_t_boxed_298_, v_h_296_, v_all_297_);
lean_dec(v_all_297_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim___redArg(lean_object* v_none_300_){
_start:
{
lean_inc(v_none_300_);
return v_none_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim___redArg___boxed(lean_object* v_none_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_Meta_Hint_DiffGranularity_none_elim___redArg(v_none_301_);
lean_dec(v_none_301_);
return v_res_302_;
}
}
lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim(lean_object* v_motive_303_, uint8_t v_t_304_, lean_object* v_h_305_, lean_object* v_none_306_){
_start:
{
lean_inc(v_none_306_);
return v_none_306_;
}
}
LEAN_EXPORT void l_Lean_Meta_Hint_DiffGranularity_none_elim_0interp(lean_interpreter_value* stack)
{
uint8_t v_t_304_ = stack[1].m_num;
lean_object* v_none_306_ = stack[3].m_obj;
lean_object* v_res_307_;
v_res_307_ = l_Lean_Meta_Hint_DiffGranularity_none_elim(lean_box(0), v_t_304_, lean_box(0), v_none_306_);
stack->m_obj
 = v_res_307_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_DiffGranularity_none_elim___boxed(lean_object* v_motive_308_, lean_object* v_t_309_, lean_object* v_h_310_, lean_object* v_none_311_){
_start:
{
uint8_t v_t_boxed_312_; lean_object* v_res_313_; 
v_t_boxed_312_ = lean_unbox(v_t_309_);
v_res_313_ = l_Lean_Meta_Hint_DiffGranularity_none_elim(v_motive_308_, v_t_boxed_312_, v_h_310_, v_none_311_);
lean_dec(v_none_311_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_instCoeSuggestionTextSuggestion___lam__0(lean_object* v_t_314_){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; lean_object* v___x_318_; 
v___x_315_ = lean_box(0);
v___x_316_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_316_, 0, v_t_314_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
lean_ctor_set(v___x_316_, 2, v___x_315_);
lean_ctor_set(v___x_316_, 3, v___x_315_);
lean_ctor_set(v___x_316_, 4, v___x_315_);
lean_ctor_set(v___x_316_, 5, v___x_315_);
v___x_317_ = 0;
v___x_318_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_318_, 0, v___x_316_);
lean_ctor_set(v___x_318_, 1, v___x_315_);
lean_ctor_set(v___x_318_, 2, v___x_315_);
lean_ctor_set_uint8(v___x_318_, sizeof(void*)*3, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_instToMessageDataSuggestion___lam__0(lean_object* v_s_321_){
_start:
{
lean_object* v_toTryThisSuggestion_322_; lean_object* v_messageData_x3f_323_; 
v_toTryThisSuggestion_322_ = lean_ctor_get(v_s_321_, 0);
lean_inc_ref(v_toTryThisSuggestion_322_);
lean_dec_ref(v_s_321_);
v_messageData_x3f_323_ = lean_ctor_get(v_toTryThisSuggestion_322_, 4);
if (lean_obj_tag(v_messageData_x3f_323_) == 0)
{
lean_object* v_suggestion_324_; 
v_suggestion_324_ = lean_ctor_get(v_toTryThisSuggestion_322_, 0);
lean_inc_ref(v_suggestion_324_);
lean_dec_ref(v_toTryThisSuggestion_322_);
if (lean_obj_tag(v_suggestion_324_) == 0)
{
lean_object* v_a_325_; lean_object* v___x_326_; 
v_a_325_ = lean_ctor_get(v_suggestion_324_, 1);
lean_inc(v_a_325_);
lean_dec_ref_known(v_suggestion_324_, 2);
v___x_326_ = l_Lean_MessageData_ofSyntax(v_a_325_);
return v___x_326_;
}
else
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_335_; 
v_a_327_ = lean_ctor_get(v_suggestion_324_, 0);
v_isSharedCheck_335_ = !lean_is_exclusive(v_suggestion_324_);
if (v_isSharedCheck_335_ == 0)
{
v___x_329_ = v_suggestion_324_;
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v_suggestion_324_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_335_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
lean_ctor_set_tag(v___x_329_, 3);
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_334_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
lean_object* v___x_333_; 
v___x_333_ = l_Lean_MessageData_ofFormat(v___x_332_);
return v___x_333_;
}
}
}
}
else
{
lean_object* v_val_336_; 
lean_inc_ref(v_messageData_x3f_323_);
lean_dec_ref(v_toTryThisSuggestion_322_);
v_val_336_ = lean_ctor_get(v_messageData_x3f_323_, 0);
lean_inc(v_val_336_);
lean_dec_ref_known(v_messageData_x3f_323_, 1);
return v_val_336_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(lean_object* v_as_339_, size_t v_i_340_, size_t v_stop_341_, lean_object* v_b_342_){
_start:
{
lean_object* v___y_344_; uint8_t v___x_348_; 
v___x_348_ = lean_usize_dec_eq(v_i_340_, v_stop_341_);
if (v___x_348_ == 0)
{
lean_object* v___x_349_; lean_object* v_fst_350_; lean_object* v_snd_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_388_; 
v___x_349_ = lean_array_uget(v_as_339_, v_i_340_);
v_fst_350_ = lean_ctor_get(v___x_349_, 0);
v_snd_351_ = lean_ctor_get(v___x_349_, 1);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_388_ == 0)
{
v___x_353_ = v___x_349_;
v_isShared_354_ = v_isSharedCheck_388_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_snd_351_);
lean_inc(v_fst_350_);
lean_dec(v___x_349_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_388_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_355_ = lean_array_get_size(v_b_342_);
v___x_356_ = lean_unsigned_to_nat(0u);
v___x_357_ = lean_nat_dec_eq(v___x_355_, v___x_356_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v_fst_361_; lean_object* v_snd_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_380_; 
lean_del_object(v___x_353_);
v___x_358_ = lean_unsigned_to_nat(1u);
v___x_359_ = lean_nat_sub(v___x_355_, v___x_358_);
v___x_360_ = lean_array_fget(v_b_342_, v___x_359_);
v_fst_361_ = lean_ctor_get(v___x_360_, 0);
v_snd_362_ = lean_ctor_get(v___x_360_, 1);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_360_);
if (v_isSharedCheck_380_ == 0)
{
v___x_364_ = v___x_360_;
v_isShared_365_ = v_isSharedCheck_380_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_snd_362_);
lean_inc(v_fst_361_);
lean_dec(v___x_360_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_380_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
uint8_t v___x_366_; uint8_t v___x_367_; uint8_t v___x_368_; 
v___x_366_ = lean_unbox(v_fst_350_);
v___x_367_ = lean_unbox(v_fst_361_);
lean_dec(v_fst_361_);
v___x_368_ = l_Lean_Diff_instBEqAction_beq(v___x_366_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_372_; 
lean_dec(v_snd_362_);
lean_dec(v___x_359_);
v___x_369_ = lean_mk_empty_array_with_capacity(v___x_358_);
v___x_370_ = lean_array_push(v___x_369_, v_snd_351_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 1, v___x_370_);
lean_ctor_set(v___x_364_, 0, v_fst_350_);
v___x_372_ = v___x_364_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_fst_350_);
lean_ctor_set(v_reuseFailAlloc_374_, 1, v___x_370_);
v___x_372_ = v_reuseFailAlloc_374_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_373_; 
v___x_373_ = lean_array_push(v_b_342_, v___x_372_);
v___y_344_ = v___x_373_;
goto v___jp_343_;
}
}
else
{
lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_375_ = lean_array_push(v_snd_362_, v_snd_351_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 1, v___x_375_);
lean_ctor_set(v___x_364_, 0, v_fst_350_);
v___x_377_ = v___x_364_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_fst_350_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v___x_375_);
v___x_377_ = v_reuseFailAlloc_379_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; 
v___x_378_ = lean_array_fset(v_b_342_, v___x_359_, v___x_377_);
lean_dec(v___x_359_);
v___y_344_ = v___x_378_;
goto v___jp_343_;
}
}
}
}
else
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_385_; 
lean_dec_ref(v_b_342_);
v___x_381_ = lean_unsigned_to_nat(1u);
v___x_382_ = lean_mk_empty_array_with_capacity(v___x_381_);
lean_inc_ref(v___x_382_);
v___x_383_ = lean_array_push(v___x_382_, v_snd_351_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v___x_383_);
v___x_385_ = v___x_353_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_fst_350_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v___x_383_);
v___x_385_ = v_reuseFailAlloc_387_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
lean_object* v___x_386_; 
v___x_386_ = lean_array_push(v___x_382_, v___x_385_);
v___y_344_ = v___x_386_;
goto v___jp_343_;
}
}
}
}
else
{
return v_b_342_;
}
v___jp_343_:
{
size_t v___x_345_; size_t v___x_346_; 
v___x_345_ = ((size_t)1ULL);
v___x_346_ = lean_usize_add(v_i_340_, v___x_345_);
v_i_340_ = v___x_346_;
v_b_342_ = v___y_344_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_339_ = stack[0].m_obj;
size_t v_i_340_ = stack[1].m_num;
size_t v_stop_341_ = stack[2].m_num;
lean_object* v_b_342_ = stack[3].m_obj;
lean_object* v_res_389_;
v_res_389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_as_339_, v_i_340_, v_stop_341_, v_b_342_);
stack->m_obj
 = v_res_389_;
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0(lean_object* v_00_u03b1_419_, lean_object* v_as_420_, size_t v_i_421_, size_t v_stop_422_, lean_object* v_b_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___redArg(v_as_420_, v_i_421_, v_stop_422_, v_b_423_);
return v___x_424_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_420_ = stack[1].m_obj;
size_t v_i_421_ = stack[2].m_num;
size_t v_stop_422_ = stack[3].m_num;
lean_object* v_b_423_ = stack[4].m_obj;
lean_object* v_res_425_;
v_res_425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0(lean_box(0), v_as_420_, v_i_421_, v_stop_422_, v_b_423_);
stack->m_obj
 = v_res_425_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0___boxed(lean_object* v_00_u03b1_426_, lean_object* v_as_427_, lean_object* v_i_428_, lean_object* v_stop_429_, lean_object* v_b_430_){
_start:
{
size_t v_i_boxed_431_; size_t v_stop_boxed_432_; lean_object* v_res_433_; 
v_i_boxed_431_ = lean_unbox_usize(v_i_428_);
lean_dec(v_i_428_);
v_stop_boxed_432_ = lean_unbox_usize(v_stop_429_);
lean_dec(v_stop_429_);
v_res_433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits_spec__0(v_00_u03b1_426_, v_as_427_, v_i_boxed_431_, v_stop_boxed_432_, v_b_430_);
lean_dec_ref(v_as_427_);
return v_res_433_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(size_t v_sz_434_, size_t v_i_435_, lean_object* v_bs_436_){
_start:
{
uint8_t v___x_437_; 
v___x_437_ = lean_usize_dec_lt(v_i_435_, v_sz_434_);
if (v___x_437_ == 0)
{
return v_bs_436_;
}
else
{
lean_object* v_v_438_; lean_object* v_fst_439_; lean_object* v_snd_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_455_; 
v_v_438_ = lean_array_uget(v_bs_436_, v_i_435_);
v_fst_439_ = lean_ctor_get(v_v_438_, 0);
v_snd_440_ = lean_ctor_get(v_v_438_, 1);
v_isSharedCheck_455_ = !lean_is_exclusive(v_v_438_);
if (v_isSharedCheck_455_ == 0)
{
v___x_442_ = v_v_438_;
v_isShared_443_ = v_isSharedCheck_455_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_snd_440_);
lean_inc(v_fst_439_);
lean_dec(v_v_438_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_455_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
lean_object* v___x_444_; lean_object* v_bs_x27_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_449_; 
v___x_444_ = lean_unsigned_to_nat(0u);
v_bs_x27_445_ = lean_array_uset(v_bs_436_, v_i_435_, v___x_444_);
v___x_446_ = lean_array_to_list(v_snd_440_);
v___x_447_ = lean_string_mk(v___x_446_);
if (v_isShared_443_ == 0)
{
lean_ctor_set(v___x_442_, 1, v___x_447_);
v___x_449_ = v___x_442_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_fst_439_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v___x_447_);
v___x_449_ = v_reuseFailAlloc_454_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
size_t v___x_450_; size_t v___x_451_; lean_object* v___x_452_; 
v___x_450_ = ((size_t)1ULL);
v___x_451_ = lean_usize_add(v_i_435_, v___x_450_);
v___x_452_ = lean_array_uset(v_bs_x27_445_, v_i_435_, v___x_449_);
v_i_435_ = v___x_451_;
v_bs_436_ = v___x_452_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_434_ = stack[0].m_num;
size_t v_i_435_ = stack[1].m_num;
lean_object* v_bs_436_ = stack[2].m_obj;
lean_object* v_res_456_;
v_res_456_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_434_, v_i_435_, v_bs_436_);
stack->m_obj
 = v_res_456_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0___boxed(lean_object* v_sz_457_, lean_object* v_i_458_, lean_object* v_bs_459_){
_start:
{
size_t v_sz_boxed_460_; size_t v_i_boxed_461_; lean_object* v_res_462_; 
v_sz_boxed_460_ = lean_unbox_usize(v_sz_457_);
lean_dec(v_sz_457_);
v_i_boxed_461_ = lean_unbox_usize(v_i_458_);
lean_dec(v_i_458_);
v_res_462_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_boxed_460_, v_i_boxed_461_, v_bs_459_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(lean_object* v_d_463_){
_start:
{
lean_object* v___x_464_; size_t v_sz_465_; size_t v___x_466_; lean_object* v___x_467_; 
v___x_464_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_d_463_);
v_sz_465_ = lean_array_size(v___x_464_);
v___x_466_ = ((size_t)0ULL);
v___x_467_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_465_, v___x_466_, v___x_464_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff___boxed(lean_object* v_d_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v_d_468_);
lean_dec_ref(v_d_468_);
return v_res_469_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(size_t v_sz_470_, size_t v_i_471_, lean_object* v_bs_472_){
_start:
{
uint8_t v___x_473_; 
v___x_473_ = lean_usize_dec_lt(v_i_471_, v_sz_470_);
if (v___x_473_ == 0)
{
return v_bs_472_;
}
else
{
lean_object* v_v_474_; lean_object* v___x_475_; lean_object* v_bs_x27_476_; uint8_t v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; size_t v___x_480_; size_t v___x_481_; lean_object* v___x_482_; 
v_v_474_ = lean_array_uget(v_bs_472_, v_i_471_);
v___x_475_ = lean_unsigned_to_nat(0u);
v_bs_x27_476_ = lean_array_uset(v_bs_472_, v_i_471_, v___x_475_);
v___x_477_ = 0;
v___x_478_ = lean_box(v___x_477_);
v___x_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v_v_474_);
v___x_480_ = ((size_t)1ULL);
v___x_481_ = lean_usize_add(v_i_471_, v___x_480_);
v___x_482_ = lean_array_uset(v_bs_x27_476_, v_i_471_, v___x_479_);
v_i_471_ = v___x_481_;
v_bs_472_ = v___x_482_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9_0interp(lean_interpreter_value* stack)
{
size_t v_sz_470_ = stack[0].m_num;
size_t v_i_471_ = stack[1].m_num;
lean_object* v_bs_472_ = stack[2].m_obj;
lean_object* v_res_484_;
v_res_484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(v_sz_470_, v_i_471_, v_bs_472_);
stack->m_obj
 = v_res_484_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9___boxed(lean_object* v_sz_485_, lean_object* v_i_486_, lean_object* v_bs_487_){
_start:
{
size_t v_sz_boxed_488_; size_t v_i_boxed_489_; lean_object* v_res_490_; 
v_sz_boxed_488_ = lean_unbox_usize(v_sz_485_);
lean_dec(v_sz_485_);
v_i_boxed_489_ = lean_unbox_usize(v_i_486_);
lean_dec(v_i_486_);
v_res_490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(v_sz_boxed_488_, v_i_boxed_489_, v_bs_487_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(lean_object* v___x_491_, lean_object* v_original_492_, lean_object* v_a_493_){
_start:
{
lean_object* v_fst_494_; lean_object* v_snd_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_514_; 
v_fst_494_ = lean_ctor_get(v_a_493_, 0);
v_snd_495_ = lean_ctor_get(v_a_493_, 1);
v_isSharedCheck_514_ = !lean_is_exclusive(v_a_493_);
if (v_isSharedCheck_514_ == 0)
{
v___x_497_ = v_a_493_;
v_isShared_498_ = v_isSharedCheck_514_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_snd_495_);
lean_inc(v_fst_494_);
lean_dec(v_a_493_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_514_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
uint8_t v___x_499_; 
v___x_499_ = lean_nat_dec_lt(v_snd_495_, v___x_491_);
if (v___x_499_ == 0)
{
lean_object* v___x_501_; 
if (v_isShared_498_ == 0)
{
v___x_501_ = v___x_497_;
goto v_reusejp_500_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_fst_494_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_snd_495_);
v___x_501_ = v_reuseFailAlloc_502_;
goto v_reusejp_500_;
}
v_reusejp_500_:
{
return v___x_501_;
}
}
else
{
uint8_t v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_503_ = 1;
v___x_504_ = lean_array_fget_borrowed(v_original_492_, v_snd_495_);
v___x_505_ = lean_box(v___x_503_);
lean_inc(v___x_504_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 1, v___x_504_);
lean_ctor_set(v___x_497_, 0, v___x_505_);
v___x_507_ = v___x_497_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_505_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v___x_504_);
v___x_507_ = v_reuseFailAlloc_513_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_508_ = lean_array_push(v_fst_494_, v___x_507_);
v___x_509_ = lean_unsigned_to_nat(1u);
v___x_510_ = lean_nat_add(v_snd_495_, v___x_509_);
lean_dec(v_snd_495_);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_508_);
lean_ctor_set(v___x_511_, 1, v___x_510_);
v_a_493_ = v___x_511_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg___boxed(lean_object* v___x_515_, lean_object* v_original_516_, lean_object* v_a_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_515_, v_original_516_, v_a_517_);
lean_dec_ref(v_original_516_);
lean_dec(v___x_515_);
return v_res_518_;
}
}
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg(uint32_t v_a_519_, lean_object* v_x_520_){
_start:
{
if (lean_obj_tag(v_x_520_) == 0)
{
lean_object* v___x_521_; 
v___x_521_ = lean_box(0);
return v___x_521_;
}
else
{
lean_object* v_key_522_; lean_object* v_value_523_; lean_object* v_tail_524_; uint32_t v___x_525_; uint8_t v___x_526_; 
v_key_522_ = lean_ctor_get(v_x_520_, 0);
v_value_523_ = lean_ctor_get(v_x_520_, 1);
v_tail_524_ = lean_ctor_get(v_x_520_, 2);
v___x_525_ = lean_unbox_uint32(v_key_522_);
v___x_526_ = lean_uint32_dec_eq(v___x_525_, v_a_519_);
if (v___x_526_ == 0)
{
v_x_520_ = v_tail_524_;
goto _start;
}
else
{
lean_object* v___x_528_; 
lean_inc(v_value_523_);
v___x_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_528_, 0, v_value_523_);
return v___x_528_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_519_ = stack[0].m_num;
lean_object* v_x_520_ = stack[1].m_obj;
lean_object* v_res_529_;
v_res_529_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg(v_a_519_, v_x_520_);
stack->m_obj
 = v_res_529_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg___boxed(lean_object* v_a_530_, lean_object* v_x_531_){
_start:
{
uint32_t v_a_boxed_532_; lean_object* v_res_533_; 
v_a_boxed_532_ = lean_unbox_uint32(v_a_530_);
lean_dec(v_a_530_);
v_res_533_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg(v_a_boxed_532_, v_x_531_);
lean_dec(v_x_531_);
return v_res_533_;
}
}
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(lean_object* v_m_534_, uint32_t v_a_535_){
_start:
{
lean_object* v_buckets_536_; lean_object* v___x_537_; uint64_t v___x_538_; uint64_t v___x_539_; uint64_t v___x_540_; uint64_t v_fold_541_; uint64_t v___x_542_; uint64_t v___x_543_; uint64_t v___x_544_; size_t v___x_545_; size_t v___x_546_; size_t v___x_547_; size_t v___x_548_; size_t v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
v_buckets_536_ = lean_ctor_get(v_m_534_, 1);
v___x_537_ = lean_array_get_size(v_buckets_536_);
v___x_538_ = lean_uint32_to_uint64(v_a_535_);
v___x_539_ = 32ULL;
v___x_540_ = lean_uint64_shift_right(v___x_538_, v___x_539_);
v_fold_541_ = lean_uint64_xor(v___x_538_, v___x_540_);
v___x_542_ = 16ULL;
v___x_543_ = lean_uint64_shift_right(v_fold_541_, v___x_542_);
v___x_544_ = lean_uint64_xor(v_fold_541_, v___x_543_);
v___x_545_ = lean_uint64_to_usize(v___x_544_);
v___x_546_ = lean_usize_of_nat(v___x_537_);
v___x_547_ = ((size_t)1ULL);
v___x_548_ = lean_usize_sub(v___x_546_, v___x_547_);
v___x_549_ = lean_usize_land(v___x_545_, v___x_548_);
v___x_550_ = lean_array_uget_borrowed(v_buckets_536_, v___x_549_);
v___x_551_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg(v_a_535_, v___x_550_);
return v___x_551_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_534_ = stack[0].m_obj;
uint32_t v_a_535_ = stack[1].m_num;
lean_object* v_res_552_;
v_res_552_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_m_534_, v_a_535_);
stack->m_obj
 = v_res_552_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg___boxed(lean_object* v_m_553_, lean_object* v_a_554_){
_start:
{
uint32_t v_a_boxed_555_; lean_object* v_res_556_; 
v_a_boxed_555_ = lean_unbox_uint32(v_a_554_);
lean_dec(v_a_554_);
v_res_556_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_m_553_, v_a_boxed_555_);
lean_dec_ref(v_m_553_);
return v_res_556_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(uint32_t v_a_557_, lean_object* v_x_558_){
_start:
{
if (lean_obj_tag(v_x_558_) == 0)
{
uint8_t v___x_559_; 
v___x_559_ = 0;
return v___x_559_;
}
else
{
lean_object* v_key_560_; lean_object* v_tail_561_; uint32_t v___x_562_; uint8_t v___x_563_; 
v_key_560_ = lean_ctor_get(v_x_558_, 0);
v_tail_561_ = lean_ctor_get(v_x_558_, 2);
v___x_562_ = lean_unbox_uint32(v_key_560_);
v___x_563_ = lean_uint32_dec_eq(v___x_562_, v_a_557_);
if (v___x_563_ == 0)
{
v_x_558_ = v_tail_561_;
goto _start;
}
else
{
return v___x_563_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_557_ = stack[0].m_num;
lean_object* v_x_558_ = stack[1].m_obj;
uint8_t v_res_565_;
v_res_565_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(v_a_557_, v_x_558_);
stack->m_num = v_res_565_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg___boxed(lean_object* v_a_566_, lean_object* v_x_567_){
_start:
{
uint32_t v_a_boxed_568_; uint8_t v_res_569_; lean_object* v_r_570_; 
v_a_boxed_568_ = lean_unbox_uint32(v_a_566_);
lean_dec(v_a_566_);
v_res_569_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(v_a_boxed_568_, v_x_567_);
lean_dec(v_x_567_);
v_r_570_ = lean_box(v_res_569_);
return v_r_570_;
}
}
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(uint32_t v_a_571_, lean_object* v_b_572_, lean_object* v_x_573_){
_start:
{
if (lean_obj_tag(v_x_573_) == 0)
{
lean_dec(v_b_572_);
return v_x_573_;
}
else
{
lean_object* v_key_574_; lean_object* v_value_575_; lean_object* v_tail_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_590_; 
v_key_574_ = lean_ctor_get(v_x_573_, 0);
v_value_575_ = lean_ctor_get(v_x_573_, 1);
v_tail_576_ = lean_ctor_get(v_x_573_, 2);
v_isSharedCheck_590_ = !lean_is_exclusive(v_x_573_);
if (v_isSharedCheck_590_ == 0)
{
v___x_578_ = v_x_573_;
v_isShared_579_ = v_isSharedCheck_590_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_tail_576_);
lean_inc(v_value_575_);
lean_inc(v_key_574_);
lean_dec(v_x_573_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_590_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
uint32_t v___x_580_; uint8_t v___x_581_; 
v___x_580_ = lean_unbox_uint32(v_key_574_);
v___x_581_ = lean_uint32_dec_eq(v___x_580_, v_a_571_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_584_; 
v___x_582_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(v_a_571_, v_b_572_, v_tail_576_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 2, v___x_582_);
v___x_584_ = v___x_578_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_key_574_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_value_575_);
lean_ctor_set(v_reuseFailAlloc_585_, 2, v___x_582_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
else
{
lean_object* v___x_586_; lean_object* v___x_588_; 
lean_dec(v_value_575_);
lean_dec(v_key_574_);
v___x_586_ = lean_box_uint32(v_a_571_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 1, v_b_572_);
lean_ctor_set(v___x_578_, 0, v___x_586_);
v___x_588_ = v___x_578_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_b_572_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v_tail_576_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_571_ = stack[0].m_num;
lean_object* v_b_572_ = stack[1].m_obj;
lean_object* v_x_573_ = stack[2].m_obj;
lean_object* v_res_591_;
v_res_591_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(v_a_571_, v_b_572_, v_x_573_);
stack->m_obj
 = v_res_591_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg___boxed(lean_object* v_a_592_, lean_object* v_b_593_, lean_object* v_x_594_){
_start:
{
uint32_t v_a_boxed_595_; lean_object* v_res_596_; 
v_a_boxed_595_ = lean_unbox_uint32(v_a_592_);
lean_dec(v_a_592_);
v_res_596_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(v_a_boxed_595_, v_b_593_, v_x_594_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29___redArg(lean_object* v_x_597_, lean_object* v_x_598_){
_start:
{
if (lean_obj_tag(v_x_598_) == 0)
{
return v_x_597_;
}
else
{
lean_object* v_key_599_; lean_object* v_value_600_; lean_object* v_tail_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_625_; 
v_key_599_ = lean_ctor_get(v_x_598_, 0);
v_value_600_ = lean_ctor_get(v_x_598_, 1);
v_tail_601_ = lean_ctor_get(v_x_598_, 2);
v_isSharedCheck_625_ = !lean_is_exclusive(v_x_598_);
if (v_isSharedCheck_625_ == 0)
{
v___x_603_ = v_x_598_;
v_isShared_604_ = v_isSharedCheck_625_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_tail_601_);
lean_inc(v_value_600_);
lean_inc(v_key_599_);
lean_dec(v_x_598_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_625_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; uint32_t v___x_606_; uint64_t v___x_607_; uint64_t v___x_608_; uint64_t v___x_609_; uint64_t v_fold_610_; uint64_t v___x_611_; uint64_t v___x_612_; uint64_t v___x_613_; size_t v___x_614_; size_t v___x_615_; size_t v___x_616_; size_t v___x_617_; size_t v___x_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
v___x_605_ = lean_array_get_size(v_x_597_);
v___x_606_ = lean_unbox_uint32(v_key_599_);
v___x_607_ = lean_uint32_to_uint64(v___x_606_);
v___x_608_ = 32ULL;
v___x_609_ = lean_uint64_shift_right(v___x_607_, v___x_608_);
v_fold_610_ = lean_uint64_xor(v___x_607_, v___x_609_);
v___x_611_ = 16ULL;
v___x_612_ = lean_uint64_shift_right(v_fold_610_, v___x_611_);
v___x_613_ = lean_uint64_xor(v_fold_610_, v___x_612_);
v___x_614_ = lean_uint64_to_usize(v___x_613_);
v___x_615_ = lean_usize_of_nat(v___x_605_);
v___x_616_ = ((size_t)1ULL);
v___x_617_ = lean_usize_sub(v___x_615_, v___x_616_);
v___x_618_ = lean_usize_land(v___x_614_, v___x_617_);
v___x_619_ = lean_array_uget_borrowed(v_x_597_, v___x_618_);
lean_inc(v___x_619_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 2, v___x_619_);
v___x_621_ = v___x_603_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_key_599_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_value_600_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v___x_619_);
v___x_621_ = v_reuseFailAlloc_624_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_622_; 
v___x_622_ = lean_array_uset(v_x_597_, v___x_618_, v___x_621_);
v_x_597_ = v___x_622_;
v_x_598_ = v_tail_601_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28___redArg(lean_object* v_i_626_, lean_object* v_source_627_, lean_object* v_target_628_){
_start:
{
lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_629_ = lean_array_get_size(v_source_627_);
v___x_630_ = lean_nat_dec_lt(v_i_626_, v___x_629_);
if (v___x_630_ == 0)
{
lean_dec_ref(v_source_627_);
lean_dec(v_i_626_);
return v_target_628_;
}
else
{
lean_object* v_es_631_; lean_object* v___x_632_; lean_object* v_source_633_; lean_object* v_target_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v_es_631_ = lean_array_fget(v_source_627_, v_i_626_);
v___x_632_ = lean_box(0);
v_source_633_ = lean_array_fset(v_source_627_, v_i_626_, v___x_632_);
v_target_634_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29___redArg(v_target_628_, v_es_631_);
v___x_635_ = lean_unsigned_to_nat(1u);
v___x_636_ = lean_nat_add(v_i_626_, v___x_635_);
lean_dec(v_i_626_);
v_i_626_ = v___x_636_;
v_source_627_ = v_source_633_;
v_target_628_ = v_target_634_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23___redArg(lean_object* v_data_638_){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v_nbuckets_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_639_ = lean_array_get_size(v_data_638_);
v___x_640_ = lean_unsigned_to_nat(2u);
v_nbuckets_641_ = lean_nat_mul(v___x_639_, v___x_640_);
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = lean_box(0);
v___x_644_ = lean_mk_array(v_nbuckets_641_, v___x_643_);
v___x_645_ = lean_array_propagate_mark(v_data_638_, v___x_644_);
v___x_646_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28___redArg(v___x_642_, v_data_638_, v___x_645_);
return v___x_646_;
}
}
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(lean_object* v_m_647_, uint32_t v_a_648_, lean_object* v_b_649_){
_start:
{
lean_object* v_size_650_; lean_object* v_buckets_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_695_; 
v_size_650_ = lean_ctor_get(v_m_647_, 0);
v_buckets_651_ = lean_ctor_get(v_m_647_, 1);
v_isSharedCheck_695_ = !lean_is_exclusive(v_m_647_);
if (v_isSharedCheck_695_ == 0)
{
v___x_653_ = v_m_647_;
v_isShared_654_ = v_isSharedCheck_695_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_buckets_651_);
lean_inc(v_size_650_);
lean_dec(v_m_647_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_695_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_655_; uint64_t v___x_656_; uint64_t v___x_657_; uint64_t v___x_658_; uint64_t v_fold_659_; uint64_t v___x_660_; uint64_t v___x_661_; uint64_t v___x_662_; size_t v___x_663_; size_t v___x_664_; size_t v___x_665_; size_t v___x_666_; size_t v___x_667_; lean_object* v_bkt_668_; uint8_t v___x_669_; 
v___x_655_ = lean_array_get_size(v_buckets_651_);
v___x_656_ = lean_uint32_to_uint64(v_a_648_);
v___x_657_ = 32ULL;
v___x_658_ = lean_uint64_shift_right(v___x_656_, v___x_657_);
v_fold_659_ = lean_uint64_xor(v___x_656_, v___x_658_);
v___x_660_ = 16ULL;
v___x_661_ = lean_uint64_shift_right(v_fold_659_, v___x_660_);
v___x_662_ = lean_uint64_xor(v_fold_659_, v___x_661_);
v___x_663_ = lean_uint64_to_usize(v___x_662_);
v___x_664_ = lean_usize_of_nat(v___x_655_);
v___x_665_ = ((size_t)1ULL);
v___x_666_ = lean_usize_sub(v___x_664_, v___x_665_);
v___x_667_ = lean_usize_land(v___x_663_, v___x_666_);
v_bkt_668_ = lean_array_uget_borrowed(v_buckets_651_, v___x_667_);
v___x_669_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(v_a_648_, v_bkt_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; lean_object* v_size_x27_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v_buckets_x27_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_670_ = lean_unsigned_to_nat(1u);
v_size_x27_671_ = lean_nat_add(v_size_650_, v___x_670_);
lean_dec(v_size_650_);
v___x_672_ = lean_box_uint32(v_a_648_);
lean_inc(v_bkt_668_);
v___x_673_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
lean_ctor_set(v___x_673_, 1, v_b_649_);
lean_ctor_set(v___x_673_, 2, v_bkt_668_);
v_buckets_x27_674_ = lean_array_uset(v_buckets_651_, v___x_667_, v___x_673_);
v___x_675_ = lean_unsigned_to_nat(4u);
v___x_676_ = lean_nat_mul(v_size_x27_671_, v___x_675_);
v___x_677_ = lean_unsigned_to_nat(3u);
v___x_678_ = lean_nat_div(v___x_676_, v___x_677_);
lean_dec(v___x_676_);
v___x_679_ = lean_array_get_size(v_buckets_x27_674_);
v___x_680_ = lean_nat_dec_le(v___x_678_, v___x_679_);
lean_dec(v___x_678_);
if (v___x_680_ == 0)
{
lean_object* v_val_681_; lean_object* v___x_683_; 
v_val_681_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23___redArg(v_buckets_x27_674_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 1, v_val_681_);
lean_ctor_set(v___x_653_, 0, v_size_x27_671_);
v___x_683_ = v___x_653_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v_size_x27_671_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_val_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
else
{
lean_object* v___x_686_; 
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 1, v_buckets_x27_674_);
lean_ctor_set(v___x_653_, 0, v_size_x27_671_);
v___x_686_ = v___x_653_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_size_x27_671_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_buckets_x27_674_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
else
{
lean_object* v___x_688_; lean_object* v_buckets_x27_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
lean_inc(v_bkt_668_);
v___x_688_ = lean_box(0);
v_buckets_x27_689_ = lean_array_uset(v_buckets_651_, v___x_667_, v___x_688_);
v___x_690_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(v_a_648_, v_b_649_, v_bkt_668_);
v___x_691_ = lean_array_uset(v_buckets_x27_689_, v___x_667_, v___x_690_);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 1, v___x_691_);
v___x_693_ = v___x_653_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_size_650_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_647_ = stack[0].m_obj;
uint32_t v_a_648_ = stack[1].m_num;
lean_object* v_b_649_ = stack[2].m_obj;
lean_object* v_res_696_;
v_res_696_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_m_647_, v_a_648_, v_b_649_);
stack->m_obj
 = v_res_696_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg___boxed(lean_object* v_m_697_, lean_object* v_a_698_, lean_object* v_b_699_){
_start:
{
uint32_t v_a_boxed_700_; lean_object* v_res_701_; 
v_a_boxed_700_ = lean_unbox_uint32(v_a_698_);
lean_dec(v_a_698_);
v_res_701_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_m_697_, v_a_boxed_700_, v_b_699_);
return v_res_701_;
}
}
lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(lean_object* v_histogram_702_, lean_object* v_index_703_, uint32_t v_val_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_histogram_702_, v_val_704_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_706_ = lean_unsigned_to_nat(0u);
v___x_707_ = lean_box(0);
v___x_708_ = lean_unsigned_to_nat(1u);
v___x_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_709_, 0, v_index_703_);
v___x_710_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_710_, 0, v___x_706_);
lean_ctor_set(v___x_710_, 1, v___x_707_);
lean_ctor_set(v___x_710_, 2, v___x_708_);
lean_ctor_set(v___x_710_, 3, v___x_709_);
v___x_711_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_702_, v_val_704_, v___x_710_);
return v___x_711_;
}
else
{
lean_object* v_val_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_733_; 
v_val_712_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_733_ == 0)
{
v___x_714_ = v___x_705_;
v_isShared_715_ = v_isSharedCheck_733_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_val_712_);
lean_dec(v___x_705_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_733_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v_leftCount_716_; lean_object* v_leftIndex_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_730_; 
v_leftCount_716_ = lean_ctor_get(v_val_712_, 0);
v_leftIndex_717_ = lean_ctor_get(v_val_712_, 1);
v_isSharedCheck_730_ = !lean_is_exclusive(v_val_712_);
if (v_isSharedCheck_730_ == 0)
{
lean_object* v_unused_731_; lean_object* v_unused_732_; 
v_unused_731_ = lean_ctor_get(v_val_712_, 3);
lean_dec(v_unused_731_);
v_unused_732_ = lean_ctor_get(v_val_712_, 2);
lean_dec(v_unused_732_);
v___x_719_ = v_val_712_;
v_isShared_720_ = v_isSharedCheck_730_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_leftIndex_717_);
lean_inc(v_leftCount_716_);
lean_dec(v_val_712_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_730_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_721_ = lean_unsigned_to_nat(1u);
v___x_722_ = lean_nat_add(v_leftCount_716_, v___x_721_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v_index_703_);
v___x_724_ = v___x_714_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_index_703_);
v___x_724_ = v_reuseFailAlloc_729_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
lean_object* v___x_726_; 
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 3, v___x_724_);
lean_ctor_set(v___x_719_, 2, v___x_722_);
v___x_726_ = v___x_719_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_728_; 
v_reuseFailAlloc_728_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_728_, 0, v_leftCount_716_);
lean_ctor_set(v_reuseFailAlloc_728_, 1, v_leftIndex_717_);
lean_ctor_set(v_reuseFailAlloc_728_, 2, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_728_, 3, v___x_724_);
v___x_726_ = v_reuseFailAlloc_728_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_727_; 
v___x_727_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_702_, v_val_704_, v___x_726_);
return v___x_727_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_histogram_702_ = stack[0].m_obj;
lean_object* v_index_703_ = stack[1].m_obj;
uint32_t v_val_704_ = stack[2].m_num;
lean_object* v_res_734_;
v_res_734_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(v_histogram_702_, v_index_703_, v_val_704_);
stack->m_obj
 = v_res_734_;
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_histogram_735_, lean_object* v_index_736_, lean_object* v_val_737_){
_start:
{
uint32_t v_val_boxed_738_; lean_object* v_res_739_; 
v_val_boxed_738_ = lean_unbox_uint32(v_val_737_);
lean_dec(v_val_737_);
v_res_739_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(v_histogram_735_, v_index_736_, v_val_boxed_738_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(lean_object* v_upperBound_740_, lean_object* v___x_741_, lean_object* v_fst_742_, lean_object* v___x_743_, lean_object* v_a_744_, lean_object* v_b_745_){
_start:
{
uint8_t v___x_746_; 
v___x_746_ = lean_nat_dec_lt(v_a_744_, v_upperBound_740_);
if (v___x_746_ == 0)
{
lean_dec(v_a_744_);
return v_b_745_;
}
else
{
lean_object* v___x_747_; uint32_t v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_747_ = l_Subarray_get___redArg(v_fst_742_, v_a_744_);
v___x_748_ = lean_unbox_uint32(v___x_747_);
lean_dec(v___x_747_);
lean_inc(v_a_744_);
v___x_749_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(v_b_745_, v_a_744_, v___x_748_);
v___x_750_ = lean_unsigned_to_nat(1u);
v___x_751_ = lean_nat_add(v_a_744_, v___x_750_);
lean_dec(v_a_744_);
v_a_744_ = v___x_751_;
v_b_745_ = v___x_749_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg___boxed(lean_object* v_upperBound_753_, lean_object* v___x_754_, lean_object* v_fst_755_, lean_object* v___x_756_, lean_object* v_a_757_, lean_object* v_b_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(v_upperBound_753_, v___x_754_, v_fst_755_, v___x_756_, v_a_757_, v_b_758_);
lean_dec(v___x_756_);
lean_dec_ref(v_fst_755_);
lean_dec(v___x_754_);
lean_dec(v_upperBound_753_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(lean_object* v_as_x27_760_, lean_object* v_b_761_){
_start:
{
if (lean_obj_tag(v_as_x27_760_) == 0)
{
return v_b_761_;
}
else
{
lean_object* v_head_762_; lean_object* v_snd_763_; lean_object* v_leftIndex_764_; 
v_head_762_ = lean_ctor_get(v_as_x27_760_, 0);
v_snd_763_ = lean_ctor_get(v_head_762_, 1);
v_leftIndex_764_ = lean_ctor_get(v_snd_763_, 1);
if (lean_obj_tag(v_leftIndex_764_) == 1)
{
lean_object* v_rightIndex_765_; 
v_rightIndex_765_ = lean_ctor_get(v_snd_763_, 3);
if (lean_obj_tag(v_rightIndex_765_) == 1)
{
if (lean_obj_tag(v_b_761_) == 0)
{
lean_object* v_tail_766_; lean_object* v_fst_767_; lean_object* v_leftCount_768_; lean_object* v_rightCount_769_; lean_object* v_val_770_; lean_object* v_val_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_tail_766_ = lean_ctor_get(v_as_x27_760_, 1);
v_fst_767_ = lean_ctor_get(v_head_762_, 0);
v_leftCount_768_ = lean_ctor_get(v_snd_763_, 0);
v_rightCount_769_ = lean_ctor_get(v_snd_763_, 2);
v_val_770_ = lean_ctor_get(v_leftIndex_764_, 0);
v_val_771_ = lean_ctor_get(v_rightIndex_765_, 0);
v___x_772_ = lean_nat_add(v_leftCount_768_, v_rightCount_769_);
lean_inc(v_val_771_);
lean_inc(v_val_770_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v_val_770_);
lean_ctor_set(v___x_773_, 1, v_val_771_);
lean_inc(v_fst_767_);
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v_fst_767_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_772_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
v___x_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
v_as_x27_760_ = v_tail_766_;
v_b_761_ = v___x_776_;
goto _start;
}
else
{
lean_object* v_val_778_; lean_object* v_tail_779_; lean_object* v_fst_780_; lean_object* v_leftCount_781_; lean_object* v_rightCount_782_; lean_object* v_val_783_; lean_object* v_val_784_; lean_object* v_fst_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_806_; 
v_val_778_ = lean_ctor_get(v_b_761_, 0);
lean_inc(v_val_778_);
v_tail_779_ = lean_ctor_get(v_as_x27_760_, 1);
v_fst_780_ = lean_ctor_get(v_head_762_, 0);
v_leftCount_781_ = lean_ctor_get(v_snd_763_, 0);
v_rightCount_782_ = lean_ctor_get(v_snd_763_, 2);
v_val_783_ = lean_ctor_get(v_leftIndex_764_, 0);
v_val_784_ = lean_ctor_get(v_rightIndex_765_, 0);
v_fst_785_ = lean_ctor_get(v_val_778_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v_val_778_);
if (v_isSharedCheck_806_ == 0)
{
lean_object* v_unused_807_; 
v_unused_807_ = lean_ctor_get(v_val_778_, 1);
lean_dec(v_unused_807_);
v___x_787_ = v_val_778_;
v_isShared_788_ = v_isSharedCheck_806_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_fst_785_);
lean_dec(v_val_778_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_806_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_789_ = lean_nat_add(v_leftCount_781_, v_rightCount_782_);
v___x_790_ = lean_nat_dec_lt(v___x_789_, v_fst_785_);
lean_dec(v_fst_785_);
if (v___x_790_ == 0)
{
lean_dec(v___x_789_);
lean_del_object(v___x_787_);
v_as_x27_760_ = v_tail_779_;
goto _start;
}
else
{
lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_804_; 
v_isSharedCheck_804_ = !lean_is_exclusive(v_b_761_);
if (v_isSharedCheck_804_ == 0)
{
lean_object* v_unused_805_; 
v_unused_805_ = lean_ctor_get(v_b_761_, 0);
lean_dec(v_unused_805_);
v___x_793_ = v_b_761_;
v_isShared_794_ = v_isSharedCheck_804_;
goto v_resetjp_792_;
}
else
{
lean_dec(v_b_761_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_804_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
lean_inc(v_val_784_);
lean_inc(v_val_783_);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 1, v_val_784_);
lean_ctor_set(v___x_787_, 0, v_val_783_);
v___x_796_ = v___x_787_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_val_783_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_val_784_);
v___x_796_ = v_reuseFailAlloc_803_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_800_; 
lean_inc(v_fst_780_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v_fst_780_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_789_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_798_);
v___x_800_ = v___x_793_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_798_);
v___x_800_ = v_reuseFailAlloc_802_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
v_as_x27_760_ = v_tail_779_;
v_b_761_ = v___x_800_;
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
lean_object* v_tail_808_; 
v_tail_808_ = lean_ctor_get(v_as_x27_760_, 1);
v_as_x27_760_ = v_tail_808_;
goto _start;
}
}
else
{
lean_object* v_tail_810_; 
v_tail_810_ = lean_ctor_get(v_as_x27_760_, 1);
v_as_x27_760_ = v_tail_810_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg___boxed(lean_object* v_as_x27_812_, lean_object* v_b_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(v_as_x27_812_, v_b_813_);
lean_dec(v_as_x27_812_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(lean_object* v_a_815_, lean_object* v_b_816_){
_start:
{
lean_object* v_array_817_; lean_object* v_start_818_; lean_object* v_stop_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_832_; 
v_array_817_ = lean_ctor_get(v_a_815_, 0);
v_start_818_ = lean_ctor_get(v_a_815_, 1);
v_stop_819_ = lean_ctor_get(v_a_815_, 2);
v_isSharedCheck_832_ = !lean_is_exclusive(v_a_815_);
if (v_isSharedCheck_832_ == 0)
{
v___x_821_ = v_a_815_;
v_isShared_822_ = v_isSharedCheck_832_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_stop_819_);
lean_inc(v_start_818_);
lean_inc(v_array_817_);
lean_dec(v_a_815_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_832_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
uint8_t v___x_823_; 
v___x_823_ = lean_nat_dec_lt(v_start_818_, v_stop_819_);
if (v___x_823_ == 0)
{
lean_del_object(v___x_821_);
lean_dec(v_stop_819_);
lean_dec(v_start_818_);
lean_dec_ref(v_array_817_);
return v_b_816_;
}
else
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_827_; 
v___x_824_ = lean_unsigned_to_nat(1u);
v___x_825_ = lean_nat_add(v_start_818_, v___x_824_);
lean_inc_ref(v_array_817_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 1, v___x_825_);
v___x_827_ = v___x_821_;
goto v_reusejp_826_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_array_817_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___x_825_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v_stop_819_);
v___x_827_ = v_reuseFailAlloc_831_;
goto v_reusejp_826_;
}
v_reusejp_826_:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = lean_array_fget(v_array_817_, v_start_818_);
lean_dec(v_start_818_);
lean_dec_ref(v_array_817_);
v___x_829_ = lean_array_push(v_b_816_, v___x_828_);
v_a_815_ = v___x_827_;
v_b_816_ = v___x_829_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8(lean_object* v_left_833_, lean_object* v_right_834_, lean_object* v_i_835_){
_start:
{
lean_object* v_start_836_; lean_object* v_stop_837_; lean_object* v___x_838_; uint8_t v___x_852_; 
v_start_836_ = lean_ctor_get(v_left_833_, 1);
v_stop_837_ = lean_ctor_get(v_left_833_, 2);
v___x_838_ = lean_nat_sub(v_stop_837_, v_start_836_);
v___x_852_ = lean_nat_dec_lt(v_i_835_, v___x_838_);
if (v___x_852_ == 0)
{
goto v___jp_839_;
}
else
{
lean_object* v_start_853_; lean_object* v_stop_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v_start_853_ = lean_ctor_get(v_right_834_, 1);
v_stop_854_ = lean_ctor_get(v_right_834_, 2);
v___x_855_ = lean_nat_sub(v_stop_854_, v_start_853_);
v___x_856_ = lean_nat_dec_lt(v_i_835_, v___x_855_);
if (v___x_856_ == 0)
{
lean_dec(v___x_855_);
goto v___jp_839_;
}
else
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; uint32_t v___x_864_; uint32_t v___x_865_; uint8_t v___x_866_; 
v___x_857_ = lean_nat_sub(v___x_838_, v_i_835_);
lean_dec(v___x_838_);
v___x_858_ = lean_unsigned_to_nat(1u);
v___x_859_ = lean_nat_sub(v___x_857_, v___x_858_);
v___x_860_ = l_Subarray_get___redArg(v_left_833_, v___x_859_);
lean_dec(v___x_859_);
v___x_861_ = lean_nat_sub(v___x_855_, v_i_835_);
lean_dec(v___x_855_);
v___x_862_ = lean_nat_sub(v___x_861_, v___x_858_);
v___x_863_ = l_Subarray_get___redArg(v_right_834_, v___x_862_);
lean_dec(v___x_862_);
v___x_864_ = lean_unbox_uint32(v___x_860_);
lean_dec(v___x_860_);
v___x_865_ = lean_unbox_uint32(v___x_863_);
lean_dec(v___x_863_);
v___x_866_ = lean_uint32_dec_eq(v___x_864_, v___x_865_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
lean_dec(v_i_835_);
lean_inc_ref(v_left_833_);
v___x_867_ = l_Subarray_take___redArg(v_left_833_, v___x_857_);
v___x_868_ = l_Subarray_take___redArg(v_right_834_, v___x_861_);
lean_dec(v___x_861_);
v___x_869_ = l_Subarray_drop___redArg(v_left_833_, v___x_857_);
lean_dec(v___x_857_);
v___x_870_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_871_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(v___x_869_, v___x_870_);
v___x_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_868_);
lean_ctor_set(v___x_872_, 1, v___x_871_);
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_867_);
lean_ctor_set(v___x_873_, 1, v___x_872_);
return v___x_873_;
}
else
{
lean_object* v___x_874_; 
lean_dec(v___x_861_);
lean_dec(v___x_857_);
v___x_874_ = lean_nat_add(v_i_835_, v___x_858_);
lean_dec(v_i_835_);
v_i_835_ = v___x_874_;
goto _start;
}
}
}
v___jp_839_:
{
lean_object* v_start_840_; lean_object* v_stop_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_start_840_ = lean_ctor_get(v_right_834_, 1);
v_stop_841_ = lean_ctor_get(v_right_834_, 2);
v___x_842_ = lean_nat_sub(v___x_838_, v_i_835_);
lean_dec(v___x_838_);
lean_inc_ref(v_left_833_);
v___x_843_ = l_Subarray_take___redArg(v_left_833_, v___x_842_);
v___x_844_ = lean_nat_sub(v_stop_841_, v_start_840_);
v___x_845_ = lean_nat_sub(v___x_844_, v_i_835_);
lean_dec(v_i_835_);
lean_dec(v___x_844_);
v___x_846_ = l_Subarray_take___redArg(v_right_834_, v___x_845_);
lean_dec(v___x_845_);
v___x_847_ = l_Subarray_drop___redArg(v_left_833_, v___x_842_);
lean_dec(v___x_842_);
v___x_848_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_849_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(v___x_847_, v___x_848_);
v___x_850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_846_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_843_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
return v___x_851_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6(lean_object* v_left_876_, lean_object* v_right_877_){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = lean_unsigned_to_nat(0u);
v___x_879_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8(v_left_876_, v_right_877_, v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(lean_object* v_x_880_, lean_object* v_x_881_){
_start:
{
if (lean_obj_tag(v_x_881_) == 0)
{
lean_inc(v_x_880_);
return v_x_880_;
}
else
{
lean_object* v_key_882_; lean_object* v_value_883_; lean_object* v_tail_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_key_882_ = lean_ctor_get(v_x_881_, 0);
v_value_883_ = lean_ctor_get(v_x_881_, 1);
v_tail_884_ = lean_ctor_get(v_x_881_, 2);
v___x_885_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(v_x_880_, v_tail_884_);
lean_inc(v_value_883_);
lean_inc(v_key_882_);
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v_key_882_);
lean_ctor_set(v___x_886_, 1, v_value_883_);
v___x_887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set(v___x_887_, 1, v___x_885_);
return v___x_887_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8___boxed(lean_object* v_x_888_, lean_object* v_x_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(v_x_888_, v_x_889_);
lean_dec(v_x_889_);
lean_dec(v_x_888_);
return v_res_890_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9(lean_object* v_as_891_, size_t v_i_892_, size_t v_stop_893_, lean_object* v_b_894_){
_start:
{
uint8_t v___x_895_; 
v___x_895_ = lean_usize_dec_eq(v_i_892_, v_stop_893_);
if (v___x_895_ == 0)
{
size_t v___x_896_; size_t v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_896_ = ((size_t)1ULL);
v___x_897_ = lean_usize_sub(v_i_892_, v___x_896_);
v___x_898_ = lean_array_uget_borrowed(v_as_891_, v___x_897_);
v___x_899_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__8(v_b_894_, v___x_898_);
lean_dec(v_b_894_);
v_i_892_ = v___x_897_;
v_b_894_ = v___x_899_;
goto _start;
}
else
{
return v_b_894_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_891_ = stack[0].m_obj;
size_t v_i_892_ = stack[1].m_num;
size_t v_stop_893_ = stack[2].m_num;
lean_object* v_b_894_ = stack[3].m_obj;
lean_object* v_res_901_;
v_res_901_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9(v_as_891_, v_i_892_, v_stop_893_, v_b_894_);
stack->m_obj
 = v_res_901_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9___boxed(lean_object* v_as_902_, lean_object* v_i_903_, lean_object* v_stop_904_, lean_object* v_b_905_){
_start:
{
size_t v_i_boxed_906_; size_t v_stop_boxed_907_; lean_object* v_res_908_; 
v_i_boxed_906_ = lean_unbox_usize(v_i_903_);
lean_dec(v_i_903_);
v_stop_boxed_907_ = lean_unbox_usize(v_stop_904_);
lean_dec(v_stop_904_);
v_res_908_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9(v_as_902_, v_i_boxed_906_, v_stop_boxed_907_, v_b_905_);
lean_dec_ref(v_as_902_);
return v_res_908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5_spec__6(lean_object* v_left_909_, lean_object* v_right_910_, lean_object* v_pref_911_){
_start:
{
lean_object* v_start_912_; lean_object* v_stop_913_; lean_object* v_i_914_; lean_object* v___x_920_; uint8_t v___x_921_; 
v_start_912_ = lean_ctor_get(v_left_909_, 1);
v_stop_913_ = lean_ctor_get(v_left_909_, 2);
v_i_914_ = lean_array_get_size(v_pref_911_);
v___x_920_ = lean_nat_sub(v_stop_913_, v_start_912_);
v___x_921_ = lean_nat_dec_lt(v_i_914_, v___x_920_);
lean_dec(v___x_920_);
if (v___x_921_ == 0)
{
goto v___jp_915_;
}
else
{
lean_object* v_start_922_; lean_object* v_stop_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v_start_922_ = lean_ctor_get(v_right_910_, 1);
v_stop_923_ = lean_ctor_get(v_right_910_, 2);
v___x_924_ = lean_nat_sub(v_stop_923_, v_start_922_);
v___x_925_ = lean_nat_dec_lt(v_i_914_, v___x_924_);
lean_dec(v___x_924_);
if (v___x_925_ == 0)
{
goto v___jp_915_;
}
else
{
lean_object* v___x_926_; lean_object* v___x_927_; uint32_t v___x_928_; uint32_t v___x_929_; uint8_t v___x_930_; 
v___x_926_ = l_Subarray_get___redArg(v_left_909_, v_i_914_);
v___x_927_ = l_Subarray_get___redArg(v_right_910_, v_i_914_);
v___x_928_ = lean_unbox_uint32(v___x_926_);
v___x_929_ = lean_unbox_uint32(v___x_927_);
lean_dec(v___x_927_);
v___x_930_ = lean_uint32_dec_eq(v___x_928_, v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
lean_dec(v___x_926_);
v___x_931_ = l_Subarray_drop___redArg(v_left_909_, v_i_914_);
v___x_932_ = l_Subarray_drop___redArg(v_right_910_, v_i_914_);
v___x_933_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_933_, 0, v___x_931_);
lean_ctor_set(v___x_933_, 1, v___x_932_);
v___x_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_934_, 0, v_pref_911_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
return v___x_934_;
}
else
{
lean_object* v___x_935_; 
v___x_935_ = lean_array_push(v_pref_911_, v___x_926_);
v_pref_911_ = v___x_935_;
goto _start;
}
}
}
v___jp_915_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_916_ = l_Subarray_drop___redArg(v_left_909_, v_i_914_);
v___x_917_ = l_Subarray_drop___redArg(v_right_910_, v_i_914_);
v___x_918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_919_, 0, v_pref_911_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
return v___x_919_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5(lean_object* v_left_937_, lean_object* v_right_938_){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; 
v___x_939_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__2___closed__0));
v___x_940_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5_spec__6(v_left_937_, v_right_938_, v___x_939_);
return v___x_940_;
}
}
lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(lean_object* v_histogram_941_, lean_object* v_index_942_, uint32_t v_val_943_){
_start:
{
lean_object* v___x_944_; 
v___x_944_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_histogram_941_, v_val_943_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_945_ = lean_unsigned_to_nat(1u);
v___x_946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_946_, 0, v_index_942_);
v___x_947_ = lean_unsigned_to_nat(0u);
v___x_948_ = lean_box(0);
v___x_949_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_949_, 0, v___x_945_);
lean_ctor_set(v___x_949_, 1, v___x_946_);
lean_ctor_set(v___x_949_, 2, v___x_947_);
lean_ctor_set(v___x_949_, 3, v___x_948_);
v___x_950_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_941_, v_val_943_, v___x_949_);
return v___x_950_;
}
else
{
lean_object* v_val_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_972_; 
v_val_951_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_972_ == 0)
{
v___x_953_ = v___x_944_;
v_isShared_954_ = v_isSharedCheck_972_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_val_951_);
lean_dec(v___x_944_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_972_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v_leftCount_955_; lean_object* v_rightCount_956_; lean_object* v_rightIndex_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_970_; 
v_leftCount_955_ = lean_ctor_get(v_val_951_, 0);
v_rightCount_956_ = lean_ctor_get(v_val_951_, 2);
v_rightIndex_957_ = lean_ctor_get(v_val_951_, 3);
v_isSharedCheck_970_ = !lean_is_exclusive(v_val_951_);
if (v_isSharedCheck_970_ == 0)
{
lean_object* v_unused_971_; 
v_unused_971_ = lean_ctor_get(v_val_951_, 1);
lean_dec(v_unused_971_);
v___x_959_ = v_val_951_;
v_isShared_960_ = v_isSharedCheck_970_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_rightIndex_957_);
lean_inc(v_rightCount_956_);
lean_inc(v_leftCount_955_);
lean_dec(v_val_951_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_970_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_961_ = lean_unsigned_to_nat(1u);
v___x_962_ = lean_nat_add(v_leftCount_955_, v___x_961_);
lean_dec(v_leftCount_955_);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 0, v_index_942_);
v___x_964_ = v___x_953_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_index_942_);
v___x_964_ = v_reuseFailAlloc_969_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_966_; 
if (v_isShared_960_ == 0)
{
lean_ctor_set(v___x_959_, 1, v___x_964_);
lean_ctor_set(v___x_959_, 0, v___x_962_);
v___x_966_ = v___x_959_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v___x_964_);
lean_ctor_set(v_reuseFailAlloc_968_, 2, v_rightCount_956_);
lean_ctor_set(v_reuseFailAlloc_968_, 3, v_rightIndex_957_);
v___x_966_ = v_reuseFailAlloc_968_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_967_; 
v___x_967_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_histogram_941_, v_val_943_, v___x_966_);
return v___x_967_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_histogram_941_ = stack[0].m_obj;
lean_object* v_index_942_ = stack[1].m_obj;
uint32_t v_val_943_ = stack[2].m_num;
lean_object* v_res_973_;
v_res_973_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(v_histogram_941_, v_index_942_, v_val_943_);
stack->m_obj
 = v_res_973_;
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg___boxed(lean_object* v_histogram_974_, lean_object* v_index_975_, lean_object* v_val_976_){
_start:
{
uint32_t v_val_boxed_977_; lean_object* v_res_978_; 
v_val_boxed_977_ = lean_unbox_uint32(v_val_976_);
lean_dec(v_val_976_);
v_res_978_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(v_histogram_974_, v_index_975_, v_val_boxed_977_);
return v_res_978_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(lean_object* v_upperBound_979_, lean_object* v_fst_980_, lean_object* v___x_981_, lean_object* v_fst_982_, lean_object* v_a_983_, lean_object* v_b_984_){
_start:
{
uint8_t v___x_985_; 
v___x_985_ = lean_nat_dec_lt(v_a_983_, v_upperBound_979_);
if (v___x_985_ == 0)
{
lean_dec(v_a_983_);
return v_b_984_;
}
else
{
lean_object* v___x_986_; uint32_t v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_986_ = l_Subarray_get___redArg(v_fst_982_, v_a_983_);
v___x_987_ = lean_unbox_uint32(v___x_986_);
lean_dec(v___x_986_);
lean_inc(v_a_983_);
v___x_988_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(v_b_984_, v_a_983_, v___x_987_);
v___x_989_ = lean_unsigned_to_nat(1u);
v___x_990_ = lean_nat_add(v_a_983_, v___x_989_);
lean_dec(v_a_983_);
v_a_983_ = v___x_990_;
v_b_984_ = v___x_988_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg___boxed(lean_object* v_upperBound_992_, lean_object* v_fst_993_, lean_object* v___x_994_, lean_object* v_fst_995_, lean_object* v_a_996_, lean_object* v_b_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(v_upperBound_992_, v_fst_993_, v___x_994_, v_fst_995_, v_a_996_, v_b_997_);
lean_dec_ref(v_fst_995_);
lean_dec(v___x_994_);
lean_dec_ref(v_fst_993_);
lean_dec(v_upperBound_992_);
return v_res_998_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_999_ = lean_box(0);
v___x_1000_ = lean_unsigned_to_nat(16u);
v___x_1001_ = lean_mk_array(v___x_1000_, v___x_999_);
return v___x_1001_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1(void){
_start:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v_hist_1004_; 
v___x_1002_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__0);
v___x_1003_ = lean_unsigned_to_nat(0u);
v_hist_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_1004_, 0, v___x_1003_);
lean_ctor_set(v_hist_1004_, 1, v___x_1002_);
return v_hist_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(lean_object* v_left_1005_, lean_object* v_right_1006_){
_start:
{
lean_object* v___x_1007_; lean_object* v_snd_1008_; lean_object* v_fst_1009_; lean_object* v_fst_1010_; lean_object* v_snd_1011_; lean_object* v___x_1012_; lean_object* v_snd_1013_; lean_object* v_fst_1014_; lean_object* v_fst_1015_; lean_object* v_snd_1016_; lean_object* v_start_1017_; lean_object* v_stop_1018_; lean_object* v___x_1019_; lean_object* v_hist_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v_start_1023_; lean_object* v_stop_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v_buckets_1027_; lean_object* v___x_1028_; lean_object* v___y_1030_; lean_object* v___x_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v___x_1007_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__5(v_left_1005_, v_right_1006_);
v_snd_1008_ = lean_ctor_get(v___x_1007_, 1);
lean_inc(v_snd_1008_);
v_fst_1009_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_fst_1009_);
lean_dec_ref(v___x_1007_);
v_fst_1010_ = lean_ctor_get(v_snd_1008_, 0);
lean_inc(v_fst_1010_);
v_snd_1011_ = lean_ctor_get(v_snd_1008_, 1);
lean_inc(v_snd_1011_);
lean_dec(v_snd_1008_);
v___x_1012_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6(v_fst_1010_, v_snd_1011_);
v_snd_1013_ = lean_ctor_get(v___x_1012_, 1);
lean_inc(v_snd_1013_);
v_fst_1014_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_fst_1014_);
lean_dec_ref(v___x_1012_);
v_fst_1015_ = lean_ctor_get(v_snd_1013_, 0);
lean_inc(v_fst_1015_);
v_snd_1016_ = lean_ctor_get(v_snd_1013_, 1);
lean_inc(v_snd_1016_);
lean_dec(v_snd_1013_);
v_start_1017_ = lean_ctor_get(v_fst_1014_, 1);
v_stop_1018_ = lean_ctor_get(v_fst_1014_, 2);
v___x_1019_ = lean_unsigned_to_nat(0u);
v_hist_1020_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4___closed__1);
v___x_1021_ = lean_nat_sub(v_stop_1018_, v_start_1017_);
v___x_1022_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(v___x_1021_, v_fst_1015_, v___x_1021_, v_fst_1014_, v___x_1019_, v_hist_1020_);
v_start_1023_ = lean_ctor_get(v_fst_1015_, 1);
v_stop_1024_ = lean_ctor_get(v_fst_1015_, 2);
v___x_1025_ = lean_nat_sub(v_stop_1024_, v_start_1023_);
v___x_1026_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(v___x_1025_, v___x_1025_, v_fst_1015_, v___x_1021_, v___x_1019_, v___x_1022_);
lean_dec(v___x_1021_);
lean_dec(v___x_1025_);
v_buckets_1027_ = lean_ctor_get(v___x_1026_, 1);
lean_inc_ref(v_buckets_1027_);
lean_dec_ref(v___x_1026_);
v___x_1028_ = lean_box(0);
v___x_1056_ = lean_box(0);
v___x_1057_ = lean_array_get_size(v_buckets_1027_);
v___x_1058_ = lean_nat_dec_lt(v___x_1019_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_dec_ref(v_buckets_1027_);
v___y_1030_ = v___x_1056_;
goto v___jp_1029_;
}
else
{
size_t v___x_1059_; size_t v___x_1060_; lean_object* v___x_1061_; 
v___x_1059_ = lean_usize_of_nat(v___x_1057_);
v___x_1060_ = ((size_t)0ULL);
v___x_1061_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__9(v_buckets_1027_, v___x_1059_, v___x_1060_, v___x_1056_);
lean_dec_ref(v_buckets_1027_);
v___y_1030_ = v___x_1061_;
goto v___jp_1029_;
}
v___jp_1029_:
{
lean_object* v___x_1031_; 
v___x_1031_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(v___y_1030_, v___x_1028_);
lean_dec(v___y_1030_);
if (lean_obj_tag(v___x_1031_) == 1)
{
lean_object* v_val_1032_; lean_object* v_snd_1033_; lean_object* v_snd_1034_; lean_object* v_fst_1035_; lean_object* v_fst_1036_; lean_object* v_snd_1037_; lean_object* v___x_1038_; lean_object* v_fst_1039_; lean_object* v_snd_1040_; lean_object* v___x_1041_; lean_object* v_fst_1042_; lean_object* v_snd_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v_val_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_val_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v_snd_1033_ = lean_ctor_get(v_val_1032_, 1);
lean_inc(v_snd_1033_);
lean_dec(v_val_1032_);
v_snd_1034_ = lean_ctor_get(v_snd_1033_, 1);
lean_inc(v_snd_1034_);
v_fst_1035_ = lean_ctor_get(v_snd_1033_, 0);
lean_inc(v_fst_1035_);
lean_dec(v_snd_1033_);
v_fst_1036_ = lean_ctor_get(v_snd_1034_, 0);
lean_inc(v_fst_1036_);
v_snd_1037_ = lean_ctor_get(v_snd_1034_, 1);
lean_inc(v_snd_1037_);
lean_dec(v_snd_1034_);
v___x_1038_ = l_Subarray_split___redArg(v_fst_1014_, v_fst_1036_);
lean_dec(v_fst_1036_);
v_fst_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_fst_1039_);
v_snd_1040_ = lean_ctor_get(v___x_1038_, 1);
lean_inc(v_snd_1040_);
lean_dec_ref(v___x_1038_);
v___x_1041_ = l_Subarray_split___redArg(v_fst_1015_, v_snd_1037_);
lean_dec(v_snd_1037_);
v_fst_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_fst_1042_);
v_snd_1043_ = lean_ctor_get(v___x_1041_, 1);
lean_inc(v_snd_1043_);
lean_dec_ref(v___x_1041_);
v___x_1044_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v_fst_1039_, v_fst_1042_);
v___x_1045_ = l_Array_append___redArg(v_fst_1009_, v___x_1044_);
lean_dec_ref(v___x_1044_);
v___x_1046_ = lean_unsigned_to_nat(1u);
v___x_1047_ = lean_mk_empty_array_with_capacity(v___x_1046_);
v___x_1048_ = lean_array_push(v___x_1047_, v_fst_1035_);
v___x_1049_ = l_Array_append___redArg(v___x_1045_, v___x_1048_);
lean_dec_ref(v___x_1048_);
v___x_1050_ = l_Subarray_drop___redArg(v_snd_1040_, v___x_1046_);
v___x_1051_ = l_Subarray_drop___redArg(v_snd_1043_, v___x_1046_);
v___x_1052_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v___x_1050_, v___x_1051_);
v___x_1053_ = l_Array_append___redArg(v___x_1049_, v___x_1052_);
lean_dec_ref(v___x_1052_);
v___x_1054_ = l_Array_append___redArg(v___x_1053_, v_snd_1016_);
lean_dec(v_snd_1016_);
return v___x_1054_;
}
else
{
lean_object* v___x_1055_; 
lean_dec(v___x_1031_);
lean_dec(v_fst_1015_);
lean_dec(v_fst_1014_);
v___x_1055_ = l_Array_append___redArg(v_fst_1009_, v_snd_1016_);
lean_dec(v_snd_1016_);
return v___x_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(lean_object* v___x_1062_, lean_object* v_edited_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_fst_1065_; lean_object* v_snd_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1085_; 
v_fst_1065_ = lean_ctor_get(v_a_1064_, 0);
v_snd_1066_ = lean_ctor_get(v_a_1064_, 1);
v_isSharedCheck_1085_ = !lean_is_exclusive(v_a_1064_);
if (v_isSharedCheck_1085_ == 0)
{
v___x_1068_ = v_a_1064_;
v_isShared_1069_ = v_isSharedCheck_1085_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_snd_1066_);
lean_inc(v_fst_1065_);
lean_dec(v_a_1064_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1085_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
uint8_t v___x_1070_; 
v___x_1070_ = lean_nat_dec_lt(v_snd_1066_, v___x_1062_);
if (v___x_1070_ == 0)
{
lean_object* v___x_1072_; 
if (v_isShared_1069_ == 0)
{
v___x_1072_ = v___x_1068_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_fst_1065_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_snd_1066_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
else
{
uint8_t v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1078_; 
v___x_1074_ = 0;
v___x_1075_ = lean_array_fget_borrowed(v_edited_1063_, v_snd_1066_);
v___x_1076_ = lean_box(v___x_1074_);
lean_inc(v___x_1075_);
if (v_isShared_1069_ == 0)
{
lean_ctor_set(v___x_1068_, 1, v___x_1075_);
lean_ctor_set(v___x_1068_, 0, v___x_1076_);
v___x_1078_ = v___x_1068_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1084_; 
v_reuseFailAlloc_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1084_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1084_, 1, v___x_1075_);
v___x_1078_ = v_reuseFailAlloc_1084_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1079_ = lean_array_push(v_fst_1065_, v___x_1078_);
v___x_1080_ = lean_unsigned_to_nat(1u);
v___x_1081_ = lean_nat_add(v_snd_1066_, v___x_1080_);
lean_dec(v_snd_1066_);
v___x_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1079_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v_a_1064_ = v___x_1082_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg___boxed(lean_object* v___x_1086_, lean_object* v_edited_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1086_, v_edited_1087_, v_a_1088_);
lean_dec_ref(v_edited_1087_);
lean_dec(v___x_1086_);
return v_res_1089_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(size_t v_sz_1090_, size_t v_i_1091_, lean_object* v_bs_1092_){
_start:
{
uint8_t v___x_1093_; 
v___x_1093_ = lean_usize_dec_lt(v_i_1091_, v_sz_1090_);
if (v___x_1093_ == 0)
{
return v_bs_1092_;
}
else
{
lean_object* v_v_1094_; lean_object* v___x_1095_; lean_object* v_bs_x27_1096_; uint8_t v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; size_t v___x_1100_; size_t v___x_1101_; lean_object* v___x_1102_; 
v_v_1094_ = lean_array_uget(v_bs_1092_, v_i_1091_);
v___x_1095_ = lean_unsigned_to_nat(0u);
v_bs_x27_1096_ = lean_array_uset(v_bs_1092_, v_i_1091_, v___x_1095_);
v___x_1097_ = 1;
v___x_1098_ = lean_box(v___x_1097_);
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v_v_1094_);
v___x_1100_ = ((size_t)1ULL);
v___x_1101_ = lean_usize_add(v_i_1091_, v___x_1100_);
v___x_1102_ = lean_array_uset(v_bs_x27_1096_, v_i_1091_, v___x_1099_);
v_i_1091_ = v___x_1101_;
v_bs_1092_ = v___x_1102_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1090_ = stack[0].m_num;
size_t v_i_1091_ = stack[1].m_num;
lean_object* v_bs_1092_ = stack[2].m_obj;
lean_object* v_res_1104_;
v_res_1104_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(v_sz_1090_, v_i_1091_, v_bs_1092_);
stack->m_obj
 = v_res_1104_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8___boxed(lean_object* v_sz_1105_, lean_object* v_i_1106_, lean_object* v_bs_1107_){
_start:
{
size_t v_sz_boxed_1108_; size_t v_i_boxed_1109_; lean_object* v_res_1110_; 
v_sz_boxed_1108_ = lean_unbox_usize(v_sz_1105_);
lean_dec(v_sz_1105_);
v_i_boxed_1109_ = lean_unbox_usize(v_i_1106_);
lean_dec(v_i_1106_);
v_res_1110_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(v_sz_boxed_1108_, v_i_boxed_1109_, v_bs_1107_);
return v_res_1110_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed__const__1(void){
_start:
{
uint32_t v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = 65;
v___x_1112_ = lean_box_uint32(v___x_1111_);
return v___x_1112_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(lean_object* v___x_1113_, lean_object* v_original_1114_, uint32_t v_a_1115_, lean_object* v_a_1116_){
_start:
{
lean_object* v_fst_1117_; lean_object* v_snd_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1143_; 
v_fst_1117_ = lean_ctor_get(v_a_1116_, 0);
v_snd_1118_ = lean_ctor_get(v_a_1116_, 1);
v_isSharedCheck_1143_ = !lean_is_exclusive(v_a_1116_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1120_ = v_a_1116_;
v_isShared_1121_ = v_isSharedCheck_1143_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_snd_1118_);
lean_inc(v_fst_1117_);
lean_dec(v_a_1116_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1143_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
uint8_t v___x_1122_; 
v___x_1122_ = lean_nat_dec_lt(v_snd_1118_, v___x_1113_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1124_; 
if (v_isShared_1121_ == 0)
{
v___x_1124_ = v___x_1120_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_fst_1117_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_snd_1118_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
else
{
lean_object* v___x_1126_; lean_object* v___x_1127_; uint32_t v___x_1128_; uint8_t v___x_1129_; 
v___x_1126_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed__const__1;
v___x_1127_ = lean_array_get_borrowed(v___x_1126_, v_original_1114_, v_snd_1118_);
v___x_1128_ = lean_unbox_uint32(v___x_1127_);
v___x_1129_ = lean_uint32_dec_eq(v___x_1128_, v_a_1115_);
if (v___x_1129_ == 0)
{
uint8_t v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1130_ = 1;
v___x_1131_ = lean_box(v___x_1130_);
lean_inc(v___x_1127_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 1, v___x_1127_);
lean_ctor_set(v___x_1120_, 0, v___x_1131_);
v___x_1133_ = v___x_1120_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1139_, 1, v___x_1127_);
v___x_1133_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1134_ = lean_array_push(v_fst_1117_, v___x_1133_);
v___x_1135_ = lean_unsigned_to_nat(1u);
v___x_1136_ = lean_nat_add(v_snd_1118_, v___x_1135_);
lean_dec(v_snd_1118_);
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1134_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v_a_1116_ = v___x_1137_;
goto _start;
}
}
else
{
lean_object* v___x_1141_; 
if (v_isShared_1121_ == 0)
{
v___x_1141_ = v___x_1120_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_fst_1117_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_snd_1118_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1113_ = stack[0].m_obj;
lean_object* v_original_1114_ = stack[1].m_obj;
uint32_t v_a_1115_ = stack[2].m_num;
lean_object* v_a_1116_ = stack[3].m_obj;
lean_object* v_res_1144_;
v_res_1144_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1113_, v_original_1114_, v_a_1115_, v_a_1116_);
stack->m_obj
 = v_res_1144_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed(lean_object* v___x_1145_, lean_object* v_original_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
uint32_t v_a_boxed_1149_; lean_object* v_res_1150_; 
v_a_boxed_1149_ = lean_unbox_uint32(v_a_1147_);
lean_dec(v_a_1147_);
v_res_1150_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1145_, v_original_1146_, v_a_boxed_1149_, v_a_1148_);
lean_dec_ref(v_original_1146_);
lean_dec(v___x_1145_);
return v_res_1150_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(lean_object* v___x_1151_, lean_object* v_edited_1152_, uint32_t v_a_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v_fst_1155_; lean_object* v_snd_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1181_; 
v_fst_1155_ = lean_ctor_get(v_a_1154_, 0);
v_snd_1156_ = lean_ctor_get(v_a_1154_, 1);
v_isSharedCheck_1181_ = !lean_is_exclusive(v_a_1154_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1158_ = v_a_1154_;
v_isShared_1159_ = v_isSharedCheck_1181_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_snd_1156_);
lean_inc(v_fst_1155_);
lean_dec(v_a_1154_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1181_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
uint8_t v___x_1160_; 
v___x_1160_ = lean_nat_dec_lt(v_snd_1156_, v___x_1151_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1162_; 
if (v_isShared_1159_ == 0)
{
v___x_1162_ = v___x_1158_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_fst_1155_);
lean_ctor_set(v_reuseFailAlloc_1163_, 1, v_snd_1156_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1165_; uint32_t v___x_1166_; uint8_t v___x_1167_; 
v___x_1164_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg___boxed__const__1;
v___x_1165_ = lean_array_get_borrowed(v___x_1164_, v_edited_1152_, v_snd_1156_);
v___x_1166_ = lean_unbox_uint32(v___x_1165_);
v___x_1167_ = lean_uint32_dec_eq(v___x_1166_, v_a_1153_);
if (v___x_1167_ == 0)
{
uint8_t v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1171_; 
v___x_1168_ = 0;
v___x_1169_ = lean_box(v___x_1168_);
lean_inc(v___x_1165_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 1, v___x_1165_);
lean_ctor_set(v___x_1158_, 0, v___x_1169_);
v___x_1171_ = v___x_1158_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v___x_1169_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v___x_1165_);
v___x_1171_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1172_ = lean_array_push(v_fst_1155_, v___x_1171_);
v___x_1173_ = lean_unsigned_to_nat(1u);
v___x_1174_ = lean_nat_add(v_snd_1156_, v___x_1173_);
lean_dec(v_snd_1156_);
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1172_);
lean_ctor_set(v___x_1175_, 1, v___x_1174_);
v_a_1154_ = v___x_1175_;
goto _start;
}
}
else
{
lean_object* v___x_1179_; 
if (v_isShared_1159_ == 0)
{
v___x_1179_ = v___x_1158_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_fst_1155_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_snd_1156_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1151_ = stack[0].m_obj;
lean_object* v_edited_1152_ = stack[1].m_obj;
uint32_t v_a_1153_ = stack[2].m_num;
lean_object* v_a_1154_ = stack[3].m_obj;
lean_object* v_res_1182_;
v_res_1182_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1151_, v_edited_1152_, v_a_1153_, v_a_1154_);
stack->m_obj
 = v_res_1182_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg___boxed(lean_object* v___x_1183_, lean_object* v_edited_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
uint32_t v_a_boxed_1187_; lean_object* v_res_1188_; 
v_a_boxed_1187_ = lean_unbox_uint32(v_a_1185_);
lean_dec(v_a_1185_);
v_res_1188_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1183_, v_edited_1184_, v_a_boxed_1187_, v_a_1186_);
lean_dec_ref(v_edited_1184_);
lean_dec(v___x_1183_);
return v_res_1188_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(lean_object* v___x_1189_, lean_object* v_original_1190_, lean_object* v___x_1191_, lean_object* v_edited_1192_, lean_object* v_as_1193_, size_t v_sz_1194_, size_t v_i_1195_, lean_object* v_b_1196_){
_start:
{
uint8_t v___x_1197_; 
v___x_1197_ = lean_usize_dec_lt(v_i_1195_, v_sz_1194_);
if (v___x_1197_ == 0)
{
return v_b_1196_;
}
else
{
lean_object* v_snd_1198_; lean_object* v_fst_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1248_; 
v_snd_1198_ = lean_ctor_get(v_b_1196_, 1);
v_fst_1199_ = lean_ctor_get(v_b_1196_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_b_1196_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1201_ = v_b_1196_;
v_isShared_1202_ = v_isSharedCheck_1248_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_snd_1198_);
lean_inc(v_fst_1199_);
lean_dec(v_b_1196_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1248_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v_fst_1203_; lean_object* v_snd_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1247_; 
v_fst_1203_ = lean_ctor_get(v_snd_1198_, 0);
v_snd_1204_ = lean_ctor_get(v_snd_1198_, 1);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_snd_1198_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1206_ = v_snd_1198_;
v_isShared_1207_ = v_isSharedCheck_1247_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_snd_1204_);
lean_inc(v_fst_1203_);
lean_dec(v_snd_1198_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1247_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v_a_1208_; lean_object* v___x_1210_; 
v_a_1208_ = lean_array_uget_borrowed(v_as_1193_, v_i_1195_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 1, v_fst_1203_);
lean_ctor_set(v___x_1206_, 0, v_fst_1199_);
v___x_1210_ = v___x_1206_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_fst_1199_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_fst_1203_);
v___x_1210_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
uint32_t v___x_1211_; lean_object* v___x_1212_; lean_object* v_fst_1213_; lean_object* v_snd_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1245_; 
v___x_1211_ = lean_unbox_uint32(v_a_1208_);
v___x_1212_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1189_, v_original_1190_, v___x_1211_, v___x_1210_);
v_fst_1213_ = lean_ctor_get(v___x_1212_, 0);
v_snd_1214_ = lean_ctor_get(v___x_1212_, 1);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1216_ = v___x_1212_;
v_isShared_1217_ = v_isSharedCheck_1245_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_snd_1214_);
lean_inc(v_fst_1213_);
lean_dec(v___x_1212_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1245_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 1, v_snd_1204_);
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_fst_1213_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v_snd_1204_);
v___x_1219_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
uint32_t v___x_1220_; lean_object* v___x_1221_; lean_object* v_fst_1222_; lean_object* v_snd_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1243_; 
v___x_1220_ = lean_unbox_uint32(v_a_1208_);
v___x_1221_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1191_, v_edited_1192_, v___x_1220_, v___x_1219_);
v_fst_1222_ = lean_ctor_get(v___x_1221_, 0);
v_snd_1223_ = lean_ctor_get(v___x_1221_, 1);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1221_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1225_ = v___x_1221_;
v_isShared_1226_ = v_isSharedCheck_1243_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_snd_1223_);
lean_inc(v_fst_1222_);
lean_dec(v___x_1221_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1243_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
uint8_t v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1230_; 
v___x_1227_ = 2;
v___x_1228_ = lean_box(v___x_1227_);
lean_inc(v_a_1208_);
if (v_isShared_1226_ == 0)
{
lean_ctor_set(v___x_1225_, 1, v_a_1208_);
lean_ctor_set(v___x_1225_, 0, v___x_1228_);
v___x_1230_ = v___x_1225_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1228_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_a_1208_);
v___x_1230_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___x_1231_ = lean_array_push(v_fst_1222_, v___x_1230_);
v___x_1232_ = lean_unsigned_to_nat(1u);
v___x_1233_ = lean_nat_add(v_snd_1214_, v___x_1232_);
lean_dec(v_snd_1214_);
v___x_1234_ = lean_nat_add(v_snd_1223_, v___x_1232_);
lean_dec(v_snd_1223_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 1, v___x_1234_);
lean_ctor_set(v___x_1201_, 0, v___x_1233_);
v___x_1236_ = v___x_1201_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; size_t v___x_1238_; size_t v___x_1239_; 
v___x_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1231_);
lean_ctor_set(v___x_1237_, 1, v___x_1236_);
v___x_1238_ = ((size_t)1ULL);
v___x_1239_ = lean_usize_add(v_i_1195_, v___x_1238_);
v_i_1195_ = v___x_1239_;
v_b_1196_ = v___x_1237_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1189_ = stack[0].m_obj;
lean_object* v_original_1190_ = stack[1].m_obj;
lean_object* v___x_1191_ = stack[2].m_obj;
lean_object* v_edited_1192_ = stack[3].m_obj;
lean_object* v_as_1193_ = stack[4].m_obj;
size_t v_sz_1194_ = stack[5].m_num;
size_t v_i_1195_ = stack[6].m_num;
lean_object* v_b_1196_ = stack[7].m_obj;
lean_object* v_res_1249_;
v_res_1249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(v___x_1189_, v_original_1190_, v___x_1191_, v_edited_1192_, v_as_1193_, v_sz_1194_, v_i_1195_, v_b_1196_);
stack->m_obj
 = v_res_1249_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15___boxed(lean_object* v___x_1250_, lean_object* v_original_1251_, lean_object* v___x_1252_, lean_object* v_edited_1253_, lean_object* v_as_1254_, lean_object* v_sz_1255_, lean_object* v_i_1256_, lean_object* v_b_1257_){
_start:
{
size_t v_sz_boxed_1258_; size_t v_i_boxed_1259_; lean_object* v_res_1260_; 
v_sz_boxed_1258_ = lean_unbox_usize(v_sz_1255_);
lean_dec(v_sz_1255_);
v_i_boxed_1259_ = lean_unbox_usize(v_i_1256_);
lean_dec(v_i_1256_);
v_res_1260_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(v___x_1250_, v_original_1251_, v___x_1252_, v_edited_1253_, v_as_1254_, v_sz_boxed_1258_, v_i_boxed_1259_, v_b_1257_);
lean_dec_ref(v_as_1254_);
lean_dec_ref(v_edited_1253_);
lean_dec(v___x_1252_);
lean_dec_ref(v_original_1251_);
lean_dec(v___x_1250_);
return v_res_1260_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(lean_object* v___x_1261_, lean_object* v_edited_1262_, lean_object* v___x_1263_, lean_object* v_original_1264_, lean_object* v_as_1265_, size_t v_sz_1266_, size_t v_i_1267_, lean_object* v_b_1268_){
_start:
{
uint8_t v___x_1269_; 
v___x_1269_ = lean_usize_dec_lt(v_i_1267_, v_sz_1266_);
if (v___x_1269_ == 0)
{
return v_b_1268_;
}
else
{
lean_object* v_snd_1270_; lean_object* v_fst_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1320_; 
v_snd_1270_ = lean_ctor_get(v_b_1268_, 1);
v_fst_1271_ = lean_ctor_get(v_b_1268_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v_b_1268_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1273_ = v_b_1268_;
v_isShared_1274_ = v_isSharedCheck_1320_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_snd_1270_);
lean_inc(v_fst_1271_);
lean_dec(v_b_1268_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1320_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v_fst_1275_; lean_object* v_snd_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1319_; 
v_fst_1275_ = lean_ctor_get(v_snd_1270_, 0);
v_snd_1276_ = lean_ctor_get(v_snd_1270_, 1);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_snd_1270_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1278_ = v_snd_1270_;
v_isShared_1279_ = v_isSharedCheck_1319_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_snd_1276_);
lean_inc(v_fst_1275_);
lean_dec(v_snd_1270_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1319_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v_a_1280_; lean_object* v___x_1282_; 
v_a_1280_ = lean_array_uget_borrowed(v_as_1265_, v_i_1267_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 1, v_fst_1275_);
lean_ctor_set(v___x_1278_, 0, v_fst_1271_);
v___x_1282_ = v___x_1278_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_fst_1271_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v_fst_1275_);
v___x_1282_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
uint32_t v___x_1283_; lean_object* v___x_1284_; lean_object* v_fst_1285_; lean_object* v_snd_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1317_; 
v___x_1283_ = lean_unbox_uint32(v_a_1280_);
v___x_1284_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1263_, v_original_1264_, v___x_1283_, v___x_1282_);
v_fst_1285_ = lean_ctor_get(v___x_1284_, 0);
v_snd_1286_ = lean_ctor_get(v___x_1284_, 1);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1288_ = v___x_1284_;
v_isShared_1289_ = v_isSharedCheck_1317_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_snd_1286_);
lean_inc(v_fst_1285_);
lean_dec(v___x_1284_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1317_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 1, v_snd_1276_);
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_fst_1285_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v_snd_1276_);
v___x_1291_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
uint32_t v___x_1292_; lean_object* v___x_1293_; lean_object* v_fst_1294_; lean_object* v_snd_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1315_; 
v___x_1292_ = lean_unbox_uint32(v_a_1280_);
v___x_1293_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1261_, v_edited_1262_, v___x_1292_, v___x_1291_);
v_fst_1294_ = lean_ctor_get(v___x_1293_, 0);
v_snd_1295_ = lean_ctor_get(v___x_1293_, 1);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1297_ = v___x_1293_;
v_isShared_1298_ = v_isSharedCheck_1315_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_snd_1295_);
lean_inc(v_fst_1294_);
lean_dec(v___x_1293_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1315_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
uint8_t v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
v___x_1299_ = 2;
v___x_1300_ = lean_box(v___x_1299_);
lean_inc(v_a_1280_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 1, v_a_1280_);
lean_ctor_set(v___x_1297_, 0, v___x_1300_);
v___x_1302_ = v___x_1297_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1300_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v_a_1280_);
v___x_1302_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1303_ = lean_array_push(v_fst_1294_, v___x_1302_);
v___x_1304_ = lean_unsigned_to_nat(1u);
v___x_1305_ = lean_nat_add(v_snd_1286_, v___x_1304_);
lean_dec(v_snd_1286_);
v___x_1306_ = lean_nat_add(v_snd_1295_, v___x_1304_);
lean_dec(v_snd_1295_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 1, v___x_1306_);
lean_ctor_set(v___x_1273_, 0, v___x_1305_);
v___x_1308_ = v___x_1273_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1305_);
lean_ctor_set(v_reuseFailAlloc_1313_, 1, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
lean_object* v___x_1309_; size_t v___x_1310_; size_t v___x_1311_; lean_object* v___x_1312_; 
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1303_);
lean_ctor_set(v___x_1309_, 1, v___x_1308_);
v___x_1310_ = ((size_t)1ULL);
v___x_1311_ = lean_usize_add(v_i_1267_, v___x_1310_);
v___x_1312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_spec__15(v___x_1263_, v_original_1264_, v___x_1261_, v_edited_1262_, v_as_1265_, v_sz_1266_, v___x_1311_, v___x_1309_);
return v___x_1312_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1261_ = stack[0].m_obj;
lean_object* v_edited_1262_ = stack[1].m_obj;
lean_object* v___x_1263_ = stack[2].m_obj;
lean_object* v_original_1264_ = stack[3].m_obj;
lean_object* v_as_1265_ = stack[4].m_obj;
size_t v_sz_1266_ = stack[5].m_num;
size_t v_i_1267_ = stack[6].m_num;
lean_object* v_b_1268_ = stack[7].m_obj;
lean_object* v_res_1321_;
v_res_1321_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v___x_1261_, v_edited_1262_, v___x_1263_, v_original_1264_, v_as_1265_, v_sz_1266_, v_i_1267_, v_b_1268_);
stack->m_obj
 = v_res_1321_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5___boxed(lean_object* v___x_1322_, lean_object* v_edited_1323_, lean_object* v___x_1324_, lean_object* v_original_1325_, lean_object* v_as_1326_, lean_object* v_sz_1327_, lean_object* v_i_1328_, lean_object* v_b_1329_){
_start:
{
size_t v_sz_boxed_1330_; size_t v_i_boxed_1331_; lean_object* v_res_1332_; 
v_sz_boxed_1330_ = lean_unbox_usize(v_sz_1327_);
lean_dec(v_sz_1327_);
v_i_boxed_1331_ = lean_unbox_usize(v_i_1328_);
lean_dec(v_i_1328_);
v_res_1332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v___x_1322_, v_edited_1323_, v___x_1324_, v_original_1325_, v_as_1326_, v_sz_boxed_1330_, v_i_boxed_1331_, v_b_1329_);
lean_dec_ref(v_as_1326_);
lean_dec_ref(v_original_1325_);
lean_dec(v___x_1324_);
lean_dec_ref(v_edited_1323_);
lean_dec(v___x_1322_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(lean_object* v_original_1340_, lean_object* v_edited_1341_){
_start:
{
lean_object* v_i_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
v_i_1342_ = lean_unsigned_to_nat(0u);
v___x_1343_ = lean_array_get_size(v_original_1340_);
v___x_1344_ = lean_nat_dec_lt(v_i_1342_, v___x_1343_);
if (v___x_1344_ == 0)
{
size_t v_sz_1345_; size_t v___x_1346_; lean_object* v___x_1347_; 
lean_dec_ref(v_original_1340_);
v_sz_1345_ = lean_array_size(v_edited_1341_);
v___x_1346_ = ((size_t)0ULL);
v___x_1347_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__9(v_sz_1345_, v___x_1346_, v_edited_1341_);
return v___x_1347_;
}
else
{
lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1348_ = lean_array_get_size(v_edited_1341_);
v___x_1349_ = lean_nat_dec_lt(v_i_1342_, v___x_1348_);
if (v___x_1349_ == 0)
{
size_t v_sz_1350_; size_t v___x_1351_; lean_object* v___x_1352_; 
lean_dec_ref(v_edited_1341_);
v_sz_1350_ = lean_array_size(v_original_1340_);
v___x_1351_ = ((size_t)0ULL);
v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__8(v_sz_1350_, v___x_1351_, v_original_1340_);
return v___x_1352_;
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v_ds_1355_; lean_object* v___x_1356_; size_t v_sz_1357_; size_t v___x_1358_; lean_object* v___x_1359_; lean_object* v_snd_1360_; lean_object* v_fst_1361_; lean_object* v_fst_1362_; lean_object* v_snd_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1382_; 
lean_inc_ref(v_original_1340_);
v___x_1353_ = l_Array_toSubarray___redArg(v_original_1340_, v_i_1342_, v___x_1343_);
lean_inc_ref(v_edited_1341_);
v___x_1354_ = l_Array_toSubarray___redArg(v_edited_1341_, v_i_1342_, v___x_1348_);
v_ds_1355_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4(v___x_1353_, v___x_1354_);
v___x_1356_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__2));
v_sz_1357_ = lean_array_size(v_ds_1355_);
v___x_1358_ = ((size_t)0ULL);
v___x_1359_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__5(v___x_1348_, v_edited_1341_, v___x_1343_, v_original_1340_, v_ds_1355_, v_sz_1357_, v___x_1358_, v___x_1356_);
lean_dec_ref(v_ds_1355_);
v_snd_1360_ = lean_ctor_get(v___x_1359_, 1);
lean_inc(v_snd_1360_);
v_fst_1361_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_fst_1361_);
lean_dec_ref(v___x_1359_);
v_fst_1362_ = lean_ctor_get(v_snd_1360_, 0);
v_snd_1363_ = lean_ctor_get(v_snd_1360_, 1);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_snd_1360_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1365_ = v_snd_1360_;
v_isShared_1366_ = v_isSharedCheck_1382_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_snd_1363_);
lean_inc(v_fst_1362_);
lean_dec(v_snd_1360_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1382_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v_fst_1362_);
lean_ctor_set(v___x_1365_, 0, v_fst_1361_);
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_fst_1361_);
lean_ctor_set(v_reuseFailAlloc_1381_, 1, v_fst_1362_);
v___x_1368_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
lean_object* v___x_1369_; lean_object* v_fst_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1379_; 
v___x_1369_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_1343_, v_original_1340_, v___x_1368_);
lean_dec_ref(v_original_1340_);
v_fst_1370_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1379_ == 0)
{
lean_object* v_unused_1380_; 
v_unused_1380_ = lean_ctor_get(v___x_1369_, 1);
lean_dec(v_unused_1380_);
v___x_1372_ = v___x_1369_;
v_isShared_1373_ = v_isSharedCheck_1379_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_fst_1370_);
lean_dec(v___x_1369_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1379_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1375_; 
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 1, v_snd_1363_);
v___x_1375_ = v___x_1372_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_fst_1370_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_snd_1363_);
v___x_1375_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1376_; lean_object* v_fst_1377_; 
v___x_1376_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1348_, v_edited_1341_, v___x_1375_);
lean_dec_ref(v_edited_1341_);
v_fst_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_fst_1377_);
lean_dec_ref(v___x_1376_);
return v_fst_1377_;
}
}
}
}
}
}
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(lean_object* v_s_1383_, lean_object* v_a_1384_, uint8_t v_b_1385_){
_start:
{
lean_object* v_str_1386_; lean_object* v_startInclusive_1387_; lean_object* v_endExclusive_1388_; lean_object* v___x_1389_; uint8_t v_decide_1390_; 
v_str_1386_ = lean_ctor_get(v_s_1383_, 0);
v_startInclusive_1387_ = lean_ctor_get(v_s_1383_, 1);
v_endExclusive_1388_ = lean_ctor_get(v_s_1383_, 2);
v___x_1389_ = lean_nat_sub(v_endExclusive_1388_, v_startInclusive_1387_);
v_decide_1390_ = lean_nat_dec_eq(v_a_1384_, v___x_1389_);
lean_dec(v___x_1389_);
if (v_decide_1390_ == 0)
{
lean_object* v___x_1391_; uint32_t v___x_1392_; uint32_t v___x_1393_; uint8_t v___x_1394_; 
v___x_1391_ = lean_nat_add(v_startInclusive_1387_, v_a_1384_);
lean_dec(v_a_1384_);
v___x_1392_ = lean_string_utf8_get_fast(v_str_1386_, v___x_1391_);
v___x_1393_ = 10;
v___x_1394_ = lean_uint32_dec_eq(v___x_1392_, v___x_1393_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = lean_string_utf8_next_fast(v_str_1386_, v___x_1391_);
lean_dec(v___x_1391_);
v___x_1396_ = lean_nat_sub(v___x_1395_, v_startInclusive_1387_);
v_a_1384_ = v___x_1396_;
v_b_1385_ = v___x_1394_;
goto _start;
}
else
{
lean_dec(v___x_1391_);
return v___x_1394_;
}
}
else
{
lean_dec(v_a_1384_);
return v_b_1385_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1383_ = stack[0].m_obj;
lean_object* v_a_1384_ = stack[1].m_obj;
uint8_t v_b_1385_ = stack[2].m_num;
uint8_t v_res_1398_;
v_res_1398_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1383_, v_a_1384_, v_b_1385_);
stack->m_num = v_res_1398_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg___boxed(lean_object* v_s_1399_, lean_object* v_a_1400_, lean_object* v_b_1401_){
_start:
{
uint8_t v_b_boxed_1402_; uint8_t v_res_1403_; lean_object* v_r_1404_; 
v_b_boxed_1402_ = lean_unbox(v_b_1401_);
v_res_1403_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1399_, v_a_1400_, v_b_boxed_1402_);
lean_dec_ref(v_s_1399_);
v_r_1404_ = lean_box(v_res_1403_);
return v_r_1404_;
}
}
uint8_t l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(lean_object* v_s_1405_){
_start:
{
lean_object* v_searcher_1406_; uint8_t v___x_1407_; uint8_t v___x_1408_; 
v_searcher_1406_ = lean_unsigned_to_nat(0u);
v___x_1407_ = 0;
v___x_1408_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1405_, v_searcher_1406_, v___x_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT void l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1405_ = stack[0].m_obj;
uint8_t v_res_1409_;
v_res_1409_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v_s_1405_);
stack->m_num = v_res_1409_;
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0___boxed(lean_object* v_s_1410_){
_start:
{
uint8_t v_res_1411_; lean_object* v_r_1412_; 
v_res_1411_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v_s_1410_);
lean_dec_ref(v_s_1410_);
v_r_1412_ = lean_box(v_res_1411_);
return v_r_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(lean_object* v_oldWs_1413_, lean_object* v_newWs_1414_){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v___x_1415_ = lean_unsigned_to_nat(0u);
v___x_1416_ = lean_string_utf8_byte_size(v_oldWs_1413_);
lean_inc_ref(v_oldWs_1413_);
v___x_1417_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1417_, 0, v_oldWs_1413_);
lean_ctor_set(v___x_1417_, 1, v___x_1415_);
lean_ctor_set(v___x_1417_, 2, v___x_1416_);
v___x_1418_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_1417_);
lean_dec_ref_known(v___x_1417_, 3);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1419_ = l_String_toListImpl(v_oldWs_1413_);
v___x_1420_ = lean_array_mk(v___x_1419_);
v___x_1421_ = l_String_toListImpl(v_newWs_1414_);
v___x_1422_ = lean_array_mk(v___x_1421_);
v___x_1423_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_1420_, v___x_1422_);
v___x_1424_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_1423_);
lean_dec_ref(v___x_1423_);
return v___x_1424_;
}
else
{
uint8_t v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
lean_dec_ref(v_oldWs_1413_);
v___x_1425_ = 2;
v___x_1426_ = lean_box(v___x_1425_);
v___x_1427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
lean_ctor_set(v___x_1427_, 1, v_newWs_1414_);
v___x_1428_ = lean_unsigned_to_nat(1u);
v___x_1429_ = lean_mk_empty_array_with_capacity(v___x_1428_);
v___x_1430_ = lean_array_push(v___x_1429_, v___x_1427_);
return v___x_1430_;
}
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(lean_object* v_s_1431_, lean_object* v_inst_1432_, lean_object* v_R_1433_, lean_object* v_a_1434_, uint8_t v_b_1435_, lean_object* v_c_1436_){
_start:
{
uint8_t v___x_1437_; 
v___x_1437_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___redArg(v_s_1431_, v_a_1434_, v_b_1435_);
return v___x_1437_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1431_ = stack[0].m_obj;
lean_object* v_a_1434_ = stack[3].m_obj;
uint8_t v_b_1435_ = stack[4].m_num;
uint8_t v_res_1438_;
v_res_1438_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(v_s_1431_, lean_box(0), lean_box(0), v_a_1434_, v_b_1435_, lean_box(0));
stack->m_num = v_res_1438_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0___boxed(lean_object* v_s_1439_, lean_object* v_inst_1440_, lean_object* v_R_1441_, lean_object* v_a_1442_, lean_object* v_b_1443_, lean_object* v_c_1444_){
_start:
{
uint8_t v_b_boxed_1445_; uint8_t v_res_1446_; lean_object* v_r_1447_; 
v_b_boxed_1445_ = lean_unbox(v_b_1443_);
v_res_1446_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0_spec__0(v_s_1439_, v_inst_1440_, v_R_1441_, v_a_1442_, v_b_boxed_1445_, v_c_1444_);
lean_dec_ref(v_s_1439_);
v_r_1447_ = lean_box(v_res_1446_);
return v_r_1447_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(lean_object* v___x_1448_, lean_object* v_original_1449_, uint32_t v_a_1450_, lean_object* v_inst_1451_, lean_object* v_a_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___redArg(v___x_1448_, v_original_1449_, v_a_1450_, v_a_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1448_ = stack[0].m_obj;
lean_object* v_original_1449_ = stack[1].m_obj;
uint32_t v_a_1450_ = stack[2].m_num;
lean_object* v_a_1452_ = stack[4].m_obj;
lean_object* v_res_1454_;
v_res_1454_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v___x_1448_, v_original_1449_, v_a_1450_, lean_box(0), v_a_1452_);
stack->m_obj
 = v_res_1454_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2___boxed(lean_object* v___x_1455_, lean_object* v_original_1456_, lean_object* v_a_1457_, lean_object* v_inst_1458_, lean_object* v_a_1459_){
_start:
{
uint32_t v_a_boxed_1460_; lean_object* v_res_1461_; 
v_a_boxed_1460_ = lean_unbox_uint32(v_a_1457_);
lean_dec(v_a_1457_);
v_res_1461_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__2(v___x_1455_, v_original_1456_, v_a_boxed_1460_, v_inst_1458_, v_a_1459_);
lean_dec_ref(v_original_1456_);
lean_dec(v___x_1455_);
return v_res_1461_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(lean_object* v___x_1462_, lean_object* v_edited_1463_, uint32_t v_a_1464_, lean_object* v_inst_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___redArg(v___x_1462_, v_edited_1463_, v_a_1464_, v_a_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1462_ = stack[0].m_obj;
lean_object* v_edited_1463_ = stack[1].m_obj;
uint32_t v_a_1464_ = stack[2].m_num;
lean_object* v_a_1466_ = stack[4].m_obj;
lean_object* v_res_1468_;
v_res_1468_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(v___x_1462_, v_edited_1463_, v_a_1464_, lean_box(0), v_a_1466_);
stack->m_obj
 = v_res_1468_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3___boxed(lean_object* v___x_1469_, lean_object* v_edited_1470_, lean_object* v_a_1471_, lean_object* v_inst_1472_, lean_object* v_a_1473_){
_start:
{
uint32_t v_a_boxed_1474_; lean_object* v_res_1475_; 
v_a_boxed_1474_ = lean_unbox_uint32(v_a_1471_);
lean_dec(v_a_1471_);
v_res_1475_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__3(v___x_1469_, v_edited_1470_, v_a_boxed_1474_, v_inst_1472_, v_a_1473_);
lean_dec_ref(v_edited_1470_);
lean_dec(v___x_1469_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(lean_object* v___x_1476_, lean_object* v_original_1477_, lean_object* v_inst_1478_, lean_object* v_a_1479_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___redArg(v___x_1476_, v_original_1477_, v_a_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6___boxed(lean_object* v___x_1481_, lean_object* v_original_1482_, lean_object* v_inst_1483_, lean_object* v_a_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__6(v___x_1481_, v_original_1482_, v_inst_1483_, v_a_1484_);
lean_dec_ref(v_original_1482_);
lean_dec(v___x_1481_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(lean_object* v___x_1486_, lean_object* v_edited_1487_, lean_object* v_inst_1488_, lean_object* v_a_1489_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___redArg(v___x_1486_, v_edited_1487_, v_a_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7___boxed(lean_object* v___x_1491_, lean_object* v_edited_1492_, lean_object* v_inst_1493_, lean_object* v_a_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__7(v___x_1491_, v_edited_1492_, v_inst_1493_, v_a_1494_);
lean_dec_ref(v_edited_1492_);
lean_dec(v___x_1491_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7(lean_object* v_as_1496_, lean_object* v_as_x27_1497_, lean_object* v_b_1498_, lean_object* v_a_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___redArg(v_as_x27_1497_, v_b_1498_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7___boxed(lean_object* v_as_1501_, lean_object* v_as_x27_1502_, lean_object* v_b_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__7(v_as_1501_, v_as_x27_1502_, v_b_1503_, v_a_1504_);
lean_dec(v_as_x27_1502_);
lean_dec(v_as_1501_);
return v_res_1505_;
}
}
lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10(lean_object* v_lsize_1506_, lean_object* v_rsize_1507_, lean_object* v_histogram_1508_, lean_object* v_index_1509_, uint32_t v_val_1510_){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___redArg(v_histogram_1508_, v_index_1509_, v_val_1510_);
return v___x_1511_;
}
}
LEAN_EXPORT void l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_lsize_1506_ = stack[0].m_obj;
lean_object* v_rsize_1507_ = stack[1].m_obj;
lean_object* v_histogram_1508_ = stack[2].m_obj;
lean_object* v_index_1509_ = stack[3].m_obj;
uint32_t v_val_1510_ = stack[4].m_num;
lean_object* v_res_1512_;
v_res_1512_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10(v_lsize_1506_, v_rsize_1507_, v_histogram_1508_, v_index_1509_, v_val_1510_);
stack->m_obj
 = v_res_1512_;
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10___boxed(lean_object* v_lsize_1513_, lean_object* v_rsize_1514_, lean_object* v_histogram_1515_, lean_object* v_index_1516_, lean_object* v_val_1517_){
_start:
{
uint32_t v_val_boxed_1518_; lean_object* v_res_1519_; 
v_val_boxed_1518_ = lean_unbox_uint32(v_val_1517_);
lean_dec(v_val_1517_);
v_res_1519_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10(v_lsize_1513_, v_rsize_1514_, v_histogram_1515_, v_index_1516_, v_val_boxed_1518_);
lean_dec(v_rsize_1514_);
lean_dec(v_lsize_1513_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11(lean_object* v_upperBound_1520_, lean_object* v___x_1521_, lean_object* v_fst_1522_, lean_object* v___x_1523_, lean_object* v_inst_1524_, lean_object* v_R_1525_, lean_object* v_a_1526_, lean_object* v_b_1527_, lean_object* v_c_1528_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___redArg(v_upperBound_1520_, v___x_1521_, v_fst_1522_, v___x_1523_, v_a_1526_, v_b_1527_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11___boxed(lean_object* v_upperBound_1530_, lean_object* v___x_1531_, lean_object* v_fst_1532_, lean_object* v___x_1533_, lean_object* v_inst_1534_, lean_object* v_R_1535_, lean_object* v_a_1536_, lean_object* v_b_1537_, lean_object* v_c_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__11(v_upperBound_1530_, v___x_1531_, v_fst_1532_, v___x_1533_, v_inst_1534_, v_R_1535_, v_a_1536_, v_b_1537_, v_c_1538_);
lean_dec(v___x_1533_);
lean_dec_ref(v_fst_1532_);
lean_dec(v___x_1531_);
lean_dec(v_upperBound_1530_);
return v_res_1539_;
}
}
lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12(lean_object* v_lsize_1540_, lean_object* v_rsize_1541_, lean_object* v_histogram_1542_, lean_object* v_index_1543_, uint32_t v_val_1544_){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___redArg(v_histogram_1542_, v_index_1543_, v_val_1544_);
return v___x_1545_;
}
}
LEAN_EXPORT void l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_lsize_1540_ = stack[0].m_obj;
lean_object* v_rsize_1541_ = stack[1].m_obj;
lean_object* v_histogram_1542_ = stack[2].m_obj;
lean_object* v_index_1543_ = stack[3].m_obj;
uint32_t v_val_1544_ = stack[4].m_num;
lean_object* v_res_1546_;
v_res_1546_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12(v_lsize_1540_, v_rsize_1541_, v_histogram_1542_, v_index_1543_, v_val_1544_);
stack->m_obj
 = v_res_1546_;
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12___boxed(lean_object* v_lsize_1547_, lean_object* v_rsize_1548_, lean_object* v_histogram_1549_, lean_object* v_index_1550_, lean_object* v_val_1551_){
_start:
{
uint32_t v_val_boxed_1552_; lean_object* v_res_1553_; 
v_val_boxed_1552_ = lean_unbox_uint32(v_val_1551_);
lean_dec(v_val_1551_);
v_res_1553_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__12(v_lsize_1547_, v_rsize_1548_, v_histogram_1549_, v_index_1550_, v_val_boxed_1552_);
lean_dec(v_rsize_1548_);
lean_dec(v_lsize_1547_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13(lean_object* v_upperBound_1554_, lean_object* v_fst_1555_, lean_object* v___x_1556_, lean_object* v_fst_1557_, lean_object* v_inst_1558_, lean_object* v_R_1559_, lean_object* v_a_1560_, lean_object* v_b_1561_, lean_object* v_c_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___redArg(v_upperBound_1554_, v_fst_1555_, v___x_1556_, v_fst_1557_, v_a_1560_, v_b_1561_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13___boxed(lean_object* v_upperBound_1564_, lean_object* v_fst_1565_, lean_object* v___x_1566_, lean_object* v_fst_1567_, lean_object* v_inst_1568_, lean_object* v_R_1569_, lean_object* v_a_1570_, lean_object* v_b_1571_, lean_object* v_c_1572_){
_start:
{
lean_object* v_res_1573_; 
v_res_1573_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__13(v_upperBound_1564_, v_fst_1565_, v___x_1566_, v_fst_1567_, v_inst_1568_, v_R_1569_, v_a_1570_, v_b_1571_, v_c_1572_);
lean_dec_ref(v_fst_1567_);
lean_dec(v___x_1566_);
lean_dec_ref(v_fst_1565_);
lean_dec(v_upperBound_1564_);
return v_res_1573_;
}
}
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13(lean_object* v_00_u03b2_1574_, lean_object* v_m_1575_, uint32_t v_a_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___redArg(v_m_1575_, v_a_1576_);
return v___x_1577_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1575_ = stack[1].m_obj;
uint32_t v_a_1576_ = stack[2].m_num;
lean_object* v_res_1578_;
v_res_1578_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13(lean_box(0), v_m_1575_, v_a_1576_);
stack->m_obj
 = v_res_1578_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13___boxed(lean_object* v_00_u03b2_1579_, lean_object* v_m_1580_, lean_object* v_a_1581_){
_start:
{
uint32_t v_a_boxed_1582_; lean_object* v_res_1583_; 
v_a_boxed_1582_ = lean_unbox_uint32(v_a_1581_);
lean_dec(v_a_1581_);
v_res_1583_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13(v_00_u03b2_1579_, v_m_1580_, v_a_boxed_1582_);
lean_dec_ref(v_m_1580_);
return v_res_1583_;
}
}
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14(lean_object* v_00_u03b2_1584_, lean_object* v_m_1585_, uint32_t v_a_1586_, lean_object* v_b_1587_){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___redArg(v_m_1585_, v_a_1586_, v_b_1587_);
return v___x_1588_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1585_ = stack[1].m_obj;
uint32_t v_a_1586_ = stack[2].m_num;
lean_object* v_b_1587_ = stack[3].m_obj;
lean_object* v_res_1589_;
v_res_1589_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14(lean_box(0), v_m_1585_, v_a_1586_, v_b_1587_);
stack->m_obj
 = v_res_1589_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14___boxed(lean_object* v_00_u03b2_1590_, lean_object* v_m_1591_, lean_object* v_a_1592_, lean_object* v_b_1593_){
_start:
{
uint32_t v_a_boxed_1594_; lean_object* v_res_1595_; 
v_a_boxed_1594_ = lean_unbox_uint32(v_a_1592_);
lean_dec(v_a_1592_);
v_res_1595_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14(v_00_u03b2_1590_, v_m_1591_, v_a_boxed_1594_, v_b_1593_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14(lean_object* v_inst_1596_, lean_object* v_R_1597_, lean_object* v_a_1598_, lean_object* v_b_1599_){
_start:
{
lean_object* v___x_1600_; 
v___x_1600_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__6_spec__8_spec__14___redArg(v_a_1598_, v_b_1599_);
return v___x_1600_;
}
}
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20(lean_object* v_00_u03b2_1601_, uint32_t v_a_1602_, lean_object* v_x_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___redArg(v_a_1602_, v_x_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_1602_ = stack[1].m_num;
lean_object* v_x_1603_ = stack[2].m_obj;
lean_object* v_res_1605_;
v_res_1605_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20(lean_box(0), v_a_1602_, v_x_1603_);
stack->m_obj
 = v_res_1605_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20___boxed(lean_object* v_00_u03b2_1606_, lean_object* v_a_1607_, lean_object* v_x_1608_){
_start:
{
uint32_t v_a_boxed_1609_; lean_object* v_res_1610_; 
v_a_boxed_1609_ = lean_unbox_uint32(v_a_1607_);
lean_dec(v_a_1607_);
v_res_1610_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__13_spec__20(v_00_u03b2_1606_, v_a_boxed_1609_, v_x_1608_);
lean_dec(v_x_1608_);
return v_res_1610_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22(lean_object* v_00_u03b2_1611_, uint32_t v_a_1612_, lean_object* v_x_1613_){
_start:
{
uint8_t v___x_1614_; 
v___x_1614_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___redArg(v_a_1612_, v_x_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_1612_ = stack[1].m_num;
lean_object* v_x_1613_ = stack[2].m_obj;
uint8_t v_res_1615_;
v_res_1615_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22(lean_box(0), v_a_1612_, v_x_1613_);
stack->m_num = v_res_1615_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22___boxed(lean_object* v_00_u03b2_1616_, lean_object* v_a_1617_, lean_object* v_x_1618_){
_start:
{
uint32_t v_a_boxed_1619_; uint8_t v_res_1620_; lean_object* v_r_1621_; 
v_a_boxed_1619_ = lean_unbox_uint32(v_a_1617_);
lean_dec(v_a_1617_);
v_res_1620_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__22(v_00_u03b2_1616_, v_a_boxed_1619_, v_x_1618_);
lean_dec(v_x_1618_);
v_r_1621_ = lean_box(v_res_1620_);
return v_r_1621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23(lean_object* v_00_u03b2_1622_, lean_object* v_data_1623_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23___redArg(v_data_1623_);
return v___x_1624_;
}
}
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24(lean_object* v_00_u03b2_1625_, uint32_t v_a_1626_, lean_object* v_b_1627_, lean_object* v_x_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___redArg(v_a_1626_, v_b_1627_, v_x_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_1626_ = stack[1].m_num;
lean_object* v_b_1627_ = stack[2].m_obj;
lean_object* v_x_1628_ = stack[3].m_obj;
lean_object* v_res_1630_;
v_res_1630_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24(lean_box(0), v_a_1626_, v_b_1627_, v_x_1628_);
stack->m_obj
 = v_res_1630_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24___boxed(lean_object* v_00_u03b2_1631_, lean_object* v_a_1632_, lean_object* v_b_1633_, lean_object* v_x_1634_){
_start:
{
uint32_t v_a_boxed_1635_; lean_object* v_res_1636_; 
v_a_boxed_1635_ = lean_unbox_uint32(v_a_1632_);
lean_dec(v_a_1632_);
v_res_1636_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__24(v_00_u03b2_1631_, v_a_boxed_1635_, v_b_1633_, v_x_1634_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28(lean_object* v_00_u03b2_1637_, lean_object* v_i_1638_, lean_object* v_source_1639_, lean_object* v_target_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28___redArg(v_i_1638_, v_source_1639_, v_target_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_1642_, lean_object* v_x_1643_, lean_object* v_x_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1_spec__4_spec__10_spec__14_spec__23_spec__28_spec__29___redArg(v_x_1643_, v_x_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(lean_object* v_s_1646_, lean_object* v_stopPos_1647_, lean_object* v_i_1648_){
_start:
{
uint8_t v___y_1650_; lean_object* v___x_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1653_ = lean_unsigned_to_nat(1u);
v___x_1654_ = lean_nat_add(v_i_1648_, v___x_1653_);
v___x_1655_ = lean_nat_dec_le(v___x_1654_, v_stopPos_1647_);
lean_dec(v___x_1654_);
if (v___x_1655_ == 0)
{
return v_i_1648_;
}
else
{
if (v___x_1655_ == 0)
{
v___y_1650_ = v___x_1655_;
goto v___jp_1649_;
}
else
{
uint32_t v___x_1656_; uint32_t v___x_1657_; uint8_t v___x_1658_; 
v___x_1656_ = lean_string_utf8_get(v_s_1646_, v_i_1648_);
v___x_1657_ = 32;
v___x_1658_ = lean_uint32_dec_eq(v___x_1656_, v___x_1657_);
if (v___x_1658_ == 0)
{
uint32_t v___x_1659_; uint8_t v___x_1660_; 
v___x_1659_ = 9;
v___x_1660_ = lean_uint32_dec_eq(v___x_1656_, v___x_1659_);
if (v___x_1660_ == 0)
{
uint32_t v___x_1661_; uint8_t v___x_1662_; 
v___x_1661_ = 13;
v___x_1662_ = lean_uint32_dec_eq(v___x_1656_, v___x_1661_);
if (v___x_1662_ == 0)
{
uint32_t v___x_1663_; uint8_t v___x_1664_; 
v___x_1663_ = 10;
v___x_1664_ = lean_uint32_dec_eq(v___x_1656_, v___x_1663_);
v___y_1650_ = v___x_1664_;
goto v___jp_1649_;
}
else
{
v___y_1650_ = v___x_1662_;
goto v___jp_1649_;
}
}
else
{
v___y_1650_ = v___x_1660_;
goto v___jp_1649_;
}
}
else
{
v___y_1650_ = v___x_1658_;
goto v___jp_1649_;
}
}
}
v___jp_1649_:
{
if (v___y_1650_ == 0)
{
return v_i_1648_;
}
else
{
lean_object* v___x_1651_; 
v___x_1651_ = lean_string_utf8_next(v_s_1646_, v_i_1648_);
lean_dec(v_i_1648_);
v_i_1648_ = v___x_1651_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0___boxed(lean_object* v_s_1665_, lean_object* v_stopPos_1666_, lean_object* v_i_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1665_, v_stopPos_1666_, v_i_1667_);
lean_dec(v_stopPos_1666_);
lean_dec_ref(v_s_1665_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(lean_object* v_s_1669_, lean_object* v_b_1670_, lean_object* v_i_1671_, lean_object* v_r_1672_, lean_object* v_ws_1673_){
_start:
{
uint8_t v___x_1682_; 
v___x_1682_ = lean_string_utf8_at_end(v_s_1669_, v_i_1671_);
if (v___x_1682_ == 0)
{
uint32_t v___x_1683_; uint32_t v___x_1684_; uint8_t v___x_1685_; 
v___x_1683_ = lean_string_utf8_get(v_s_1669_, v_i_1671_);
v___x_1684_ = 32;
v___x_1685_ = lean_uint32_dec_eq(v___x_1683_, v___x_1684_);
if (v___x_1685_ == 0)
{
uint32_t v___x_1686_; uint8_t v___x_1687_; 
v___x_1686_ = 9;
v___x_1687_ = lean_uint32_dec_eq(v___x_1683_, v___x_1686_);
if (v___x_1687_ == 0)
{
uint32_t v___x_1688_; uint8_t v___x_1689_; 
v___x_1688_ = 13;
v___x_1689_ = lean_uint32_dec_eq(v___x_1683_, v___x_1688_);
if (v___x_1689_ == 0)
{
uint32_t v___x_1690_; uint8_t v___x_1691_; 
v___x_1690_ = 10;
v___x_1691_ = lean_uint32_dec_eq(v___x_1683_, v___x_1690_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_string_utf8_next(v_s_1669_, v_i_1671_);
lean_dec(v_i_1671_);
v_i_1671_ = v___x_1692_;
goto _start;
}
else
{
goto v___jp_1674_;
}
}
else
{
goto v___jp_1674_;
}
}
else
{
goto v___jp_1674_;
}
}
else
{
goto v___jp_1674_;
}
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1694_ = lean_string_utf8_extract(v_s_1669_, v_b_1670_, v_i_1671_);
lean_dec(v_i_1671_);
lean_dec(v_b_1670_);
v___x_1695_ = lean_array_push(v_r_1672_, v___x_1694_);
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1695_);
lean_ctor_set(v___x_1696_, 1, v_ws_1673_);
return v___x_1696_;
}
v___jp_1674_:
{
lean_object* v___x_1675_; lean_object* v_e_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1675_ = lean_string_utf8_byte_size(v_s_1669_);
lean_inc(v_i_1671_);
v_e_1676_ = l_Substring_Raw_takeWhileAux___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux_spec__0(v_s_1669_, v___x_1675_, v_i_1671_);
v___x_1677_ = lean_string_utf8_extract(v_s_1669_, v_b_1670_, v_i_1671_);
lean_dec(v_b_1670_);
v___x_1678_ = lean_array_push(v_r_1672_, v___x_1677_);
v___x_1679_ = lean_string_utf8_extract(v_s_1669_, v_i_1671_, v_e_1676_);
lean_dec(v_i_1671_);
v___x_1680_ = lean_array_push(v_ws_1673_, v___x_1679_);
lean_inc(v_e_1676_);
v_b_1670_ = v_e_1676_;
v_i_1671_ = v_e_1676_;
v_r_1672_ = v___x_1678_;
v_ws_1673_ = v___x_1680_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux___boxed(lean_object* v_s_1697_, lean_object* v_b_1698_, lean_object* v_i_1699_, lean_object* v_r_1700_, lean_object* v_ws_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1697_, v_b_1698_, v_i_1699_, v_r_1700_, v_ws_1701_);
lean_dec_ref(v_s_1697_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(lean_object* v_s_1705_){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1706_ = lean_unsigned_to_nat(0u);
v___x_1707_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_1708_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWordsAux(v_s_1705_, v___x_1706_, v___x_1706_, v___x_1707_, v___x_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___boxed(lean_object* v_s_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_1709_);
lean_dec_ref(v_s_1709_);
return v_res_1710_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(size_t v_sz_1711_, size_t v_i_1712_, lean_object* v_bs_1713_){
_start:
{
uint8_t v___x_1714_; 
v___x_1714_ = lean_usize_dec_lt(v_i_1712_, v_sz_1711_);
if (v___x_1714_ == 0)
{
return v_bs_1713_;
}
else
{
lean_object* v_v_1715_; lean_object* v_fst_1716_; lean_object* v_snd_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1751_; 
v_v_1715_ = lean_array_uget(v_bs_1713_, v_i_1712_);
v_fst_1716_ = lean_ctor_get(v_v_1715_, 0);
v_snd_1717_ = lean_ctor_get(v_v_1715_, 1);
v_isSharedCheck_1751_ = !lean_is_exclusive(v_v_1715_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1719_ = v_v_1715_;
v_isShared_1720_ = v_isSharedCheck_1751_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_snd_1717_);
lean_inc(v_fst_1716_);
lean_dec(v_v_1715_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1751_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1721_; lean_object* v_bs_x27_1722_; lean_object* v___y_1724_; lean_object* v___x_1729_; lean_object* v___x_1730_; uint8_t v___x_1731_; 
v___x_1721_ = lean_unsigned_to_nat(0u);
v_bs_x27_1722_ = lean_array_uset(v_bs_1713_, v_i_1712_, v___x_1721_);
v___x_1729_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_1730_ = lean_array_get_size(v_snd_1717_);
v___x_1731_ = lean_nat_dec_lt(v___x_1721_, v___x_1730_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1733_; 
lean_dec(v_snd_1717_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 1, v___x_1729_);
v___x_1733_ = v___x_1719_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_fst_1716_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v___x_1729_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
v___y_1724_ = v___x_1733_;
goto v___jp_1723_;
}
}
else
{
uint8_t v___x_1735_; 
v___x_1735_ = lean_nat_dec_le(v___x_1730_, v___x_1730_);
if (v___x_1735_ == 0)
{
if (v___x_1731_ == 0)
{
lean_object* v___x_1737_; 
lean_dec(v_snd_1717_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 1, v___x_1729_);
v___x_1737_ = v___x_1719_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_fst_1716_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v___x_1729_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
v___y_1724_ = v___x_1737_;
goto v___jp_1723_;
}
}
else
{
size_t v___x_1739_; size_t v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1743_; 
v___x_1739_ = ((size_t)0ULL);
v___x_1740_ = lean_usize_of_nat(v___x_1730_);
v___x_1741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_1717_, v___x_1739_, v___x_1740_, v___x_1729_);
lean_dec(v_snd_1717_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 1, v___x_1741_);
v___x_1743_ = v___x_1719_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_fst_1716_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v___x_1741_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
v___y_1724_ = v___x_1743_;
goto v___jp_1723_;
}
}
}
else
{
size_t v___x_1745_; size_t v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1745_ = ((size_t)0ULL);
v___x_1746_ = lean_usize_of_nat(v___x_1730_);
v___x_1747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString_spec__3(v_snd_1717_, v___x_1745_, v___x_1746_, v___x_1729_);
lean_dec(v_snd_1717_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 1, v___x_1747_);
v___x_1749_ = v___x_1719_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_fst_1716_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v___x_1747_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
v___y_1724_ = v___x_1749_;
goto v___jp_1723_;
}
}
}
v___jp_1723_:
{
size_t v___x_1725_; size_t v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = ((size_t)1ULL);
v___x_1726_ = lean_usize_add(v_i_1712_, v___x_1725_);
v___x_1727_ = lean_array_uset(v_bs_x27_1722_, v_i_1712_, v___y_1724_);
v_i_1712_ = v___x_1726_;
v_bs_1713_ = v___x_1727_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1711_ = stack[0].m_num;
size_t v_i_1712_ = stack[1].m_num;
lean_object* v_bs_1713_ = stack[2].m_obj;
lean_object* v_res_1752_;
v_res_1752_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_1711_, v_i_1712_, v_bs_1713_);
stack->m_obj
 = v_res_1752_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0___boxed(lean_object* v_sz_1753_, lean_object* v_i_1754_, lean_object* v_bs_1755_){
_start:
{
size_t v_sz_boxed_1756_; size_t v_i_boxed_1757_; lean_object* v_res_1758_; 
v_sz_boxed_1756_ = lean_unbox_usize(v_sz_1753_);
lean_dec(v_sz_1753_);
v_i_boxed_1757_ = lean_unbox_usize(v_i_1754_);
lean_dec(v_i_1754_);
v_res_1758_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_boxed_1756_, v_i_boxed_1757_, v_bs_1755_);
return v_res_1758_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(size_t v_sz_1759_, size_t v_i_1760_, lean_object* v_bs_1761_){
_start:
{
uint8_t v___x_1762_; 
v___x_1762_ = lean_usize_dec_lt(v_i_1760_, v_sz_1759_);
if (v___x_1762_ == 0)
{
return v_bs_1761_;
}
else
{
lean_object* v_v_1763_; lean_object* v___x_1764_; lean_object* v_bs_x27_1765_; uint8_t v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; size_t v___x_1769_; size_t v___x_1770_; lean_object* v___x_1771_; 
v_v_1763_ = lean_array_uget(v_bs_1761_, v_i_1760_);
v___x_1764_ = lean_unsigned_to_nat(0u);
v_bs_x27_1765_ = lean_array_uset(v_bs_1761_, v_i_1760_, v___x_1764_);
v___x_1766_ = 0;
v___x_1767_ = lean_box(v___x_1766_);
v___x_1768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1768_, 0, v___x_1767_);
lean_ctor_set(v___x_1768_, 1, v_v_1763_);
v___x_1769_ = ((size_t)1ULL);
v___x_1770_ = lean_usize_add(v_i_1760_, v___x_1769_);
v___x_1771_ = lean_array_uset(v_bs_x27_1765_, v_i_1760_, v___x_1768_);
v_i_1760_ = v___x_1770_;
v_bs_1761_ = v___x_1771_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1759_ = stack[0].m_num;
size_t v_i_1760_ = stack[1].m_num;
lean_object* v_bs_1761_ = stack[2].m_obj;
lean_object* v_res_1773_;
v_res_1773_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_1759_, v_i_1760_, v_bs_1761_);
stack->m_obj
 = v_res_1773_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8___boxed(lean_object* v_sz_1774_, lean_object* v_i_1775_, lean_object* v_bs_1776_){
_start:
{
size_t v_sz_boxed_1777_; size_t v_i_boxed_1778_; lean_object* v_res_1779_; 
v_sz_boxed_1777_ = lean_unbox_usize(v_sz_1774_);
lean_dec(v_sz_1774_);
v_i_boxed_1778_ = lean_unbox_usize(v_i_1775_);
lean_dec(v_i_1775_);
v_res_1779_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_boxed_1777_, v_i_boxed_1778_, v_bs_1776_);
return v_res_1779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(lean_object* v_x_1780_, lean_object* v_x_1781_){
_start:
{
if (lean_obj_tag(v_x_1781_) == 0)
{
lean_inc(v_x_1780_);
return v_x_1780_;
}
else
{
lean_object* v_key_1782_; lean_object* v_value_1783_; lean_object* v_tail_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v_key_1782_ = lean_ctor_get(v_x_1781_, 0);
v_value_1783_ = lean_ctor_get(v_x_1781_, 1);
v_tail_1784_ = lean_ctor_get(v_x_1781_, 2);
v___x_1785_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(v_x_1780_, v_tail_1784_);
lean_inc(v_value_1783_);
lean_inc(v_key_1782_);
v___x_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1786_, 0, v_key_1782_);
lean_ctor_set(v___x_1786_, 1, v_value_1783_);
v___x_1787_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
lean_ctor_set(v___x_1787_, 1, v___x_1785_);
return v___x_1787_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7___boxed(lean_object* v_x_1788_, lean_object* v_x_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(v_x_1788_, v_x_1789_);
lean_dec(v_x_1789_);
lean_dec(v_x_1788_);
return v_res_1790_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8(lean_object* v_as_1791_, size_t v_i_1792_, size_t v_stop_1793_, lean_object* v_b_1794_){
_start:
{
uint8_t v___x_1795_; 
v___x_1795_ = lean_usize_dec_eq(v_i_1792_, v_stop_1793_);
if (v___x_1795_ == 0)
{
size_t v___x_1796_; size_t v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v___x_1796_ = ((size_t)1ULL);
v___x_1797_ = lean_usize_sub(v_i_1792_, v___x_1796_);
v___x_1798_ = lean_array_uget_borrowed(v_as_1791_, v___x_1797_);
v___x_1799_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__7(v_b_1794_, v___x_1798_);
lean_dec(v_b_1794_);
v_i_1792_ = v___x_1797_;
v_b_1794_ = v___x_1799_;
goto _start;
}
else
{
return v_b_1794_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1791_ = stack[0].m_obj;
size_t v_i_1792_ = stack[1].m_num;
size_t v_stop_1793_ = stack[2].m_num;
lean_object* v_b_1794_ = stack[3].m_obj;
lean_object* v_res_1801_;
v_res_1801_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8(v_as_1791_, v_i_1792_, v_stop_1793_, v_b_1794_);
stack->m_obj
 = v_res_1801_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8___boxed(lean_object* v_as_1802_, lean_object* v_i_1803_, lean_object* v_stop_1804_, lean_object* v_b_1805_){
_start:
{
size_t v_i_boxed_1806_; size_t v_stop_boxed_1807_; lean_object* v_res_1808_; 
v_i_boxed_1806_ = lean_unbox_usize(v_i_1803_);
lean_dec(v_i_1803_);
v_stop_boxed_1807_ = lean_unbox_usize(v_stop_1804_);
lean_dec(v_stop_1804_);
v_res_1808_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8(v_as_1802_, v_i_boxed_1806_, v_stop_boxed_1807_, v_b_1805_);
lean_dec_ref(v_as_1802_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4_spec__6(lean_object* v_left_1809_, lean_object* v_right_1810_, lean_object* v_pref_1811_){
_start:
{
lean_object* v_start_1812_; lean_object* v_stop_1813_; lean_object* v_i_1814_; lean_object* v___x_1820_; uint8_t v___x_1821_; 
v_start_1812_ = lean_ctor_get(v_left_1809_, 1);
v_stop_1813_ = lean_ctor_get(v_left_1809_, 2);
v_i_1814_ = lean_array_get_size(v_pref_1811_);
v___x_1820_ = lean_nat_sub(v_stop_1813_, v_start_1812_);
v___x_1821_ = lean_nat_dec_lt(v_i_1814_, v___x_1820_);
lean_dec(v___x_1820_);
if (v___x_1821_ == 0)
{
goto v___jp_1815_;
}
else
{
lean_object* v_start_1822_; lean_object* v_stop_1823_; lean_object* v___x_1824_; uint8_t v___x_1825_; 
v_start_1822_ = lean_ctor_get(v_right_1810_, 1);
v_stop_1823_ = lean_ctor_get(v_right_1810_, 2);
v___x_1824_ = lean_nat_sub(v_stop_1823_, v_start_1822_);
v___x_1825_ = lean_nat_dec_lt(v_i_1814_, v___x_1824_);
lean_dec(v___x_1824_);
if (v___x_1825_ == 0)
{
goto v___jp_1815_;
}
else
{
lean_object* v___x_1826_; lean_object* v___x_1827_; uint8_t v___x_1828_; 
v___x_1826_ = l_Subarray_get___redArg(v_left_1809_, v_i_1814_);
v___x_1827_ = l_Subarray_get___redArg(v_right_1810_, v_i_1814_);
v___x_1828_ = lean_string_dec_eq(v___x_1826_, v___x_1827_);
lean_dec(v___x_1827_);
if (v___x_1828_ == 0)
{
lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
lean_dec(v___x_1826_);
v___x_1829_ = l_Subarray_drop___redArg(v_left_1809_, v_i_1814_);
v___x_1830_ = l_Subarray_drop___redArg(v_right_1810_, v_i_1814_);
v___x_1831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1829_);
lean_ctor_set(v___x_1831_, 1, v___x_1830_);
v___x_1832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1832_, 0, v_pref_1811_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
return v___x_1832_;
}
else
{
lean_object* v___x_1833_; 
v___x_1833_ = lean_array_push(v_pref_1811_, v___x_1826_);
v_pref_1811_ = v___x_1833_;
goto _start;
}
}
}
v___jp_1815_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1816_ = l_Subarray_drop___redArg(v_left_1809_, v_i_1814_);
v___x_1817_ = l_Subarray_drop___redArg(v_right_1810_, v_i_1814_);
v___x_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1816_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
v___x_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1819_, 0, v_pref_1811_);
lean_ctor_set(v___x_1819_, 1, v___x_1818_);
return v___x_1819_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4(lean_object* v_left_1835_, lean_object* v_right_1836_){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_1838_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchPrefix_go___at___00Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4_spec__6(v_left_1835_, v_right_1836_, v___x_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(lean_object* v_a_1839_, lean_object* v_x_1840_){
_start:
{
if (lean_obj_tag(v_x_1840_) == 0)
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_box(0);
return v___x_1841_;
}
else
{
lean_object* v_key_1842_; lean_object* v_value_1843_; lean_object* v_tail_1844_; uint8_t v___x_1845_; 
v_key_1842_ = lean_ctor_get(v_x_1840_, 0);
v_value_1843_ = lean_ctor_get(v_x_1840_, 1);
v_tail_1844_ = lean_ctor_get(v_x_1840_, 2);
v___x_1845_ = lean_string_dec_eq(v_key_1842_, v_a_1839_);
if (v___x_1845_ == 0)
{
v_x_1840_ = v_tail_1844_;
goto _start;
}
else
{
lean_object* v___x_1847_; 
lean_inc(v_value_1843_);
v___x_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_value_1843_);
return v___x_1847_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg___boxed(lean_object* v_a_1848_, lean_object* v_x_1849_){
_start:
{
lean_object* v_res_1850_; 
v_res_1850_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(v_a_1848_, v_x_1849_);
lean_dec(v_x_1849_);
lean_dec_ref(v_a_1848_);
return v_res_1850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(lean_object* v_m_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v_buckets_1853_; lean_object* v___x_1854_; uint64_t v___x_1855_; uint64_t v___x_1856_; uint64_t v___x_1857_; uint64_t v_fold_1858_; uint64_t v___x_1859_; uint64_t v___x_1860_; uint64_t v___x_1861_; size_t v___x_1862_; size_t v___x_1863_; size_t v___x_1864_; size_t v___x_1865_; size_t v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v_buckets_1853_ = lean_ctor_get(v_m_1851_, 1);
v___x_1854_ = lean_array_get_size(v_buckets_1853_);
v___x_1855_ = lean_string_hash(v_a_1852_);
v___x_1856_ = 32ULL;
v___x_1857_ = lean_uint64_shift_right(v___x_1855_, v___x_1856_);
v_fold_1858_ = lean_uint64_xor(v___x_1855_, v___x_1857_);
v___x_1859_ = 16ULL;
v___x_1860_ = lean_uint64_shift_right(v_fold_1858_, v___x_1859_);
v___x_1861_ = lean_uint64_xor(v_fold_1858_, v___x_1860_);
v___x_1862_ = lean_uint64_to_usize(v___x_1861_);
v___x_1863_ = lean_usize_of_nat(v___x_1854_);
v___x_1864_ = ((size_t)1ULL);
v___x_1865_ = lean_usize_sub(v___x_1863_, v___x_1864_);
v___x_1866_ = lean_usize_land(v___x_1862_, v___x_1865_);
v___x_1867_ = lean_array_uget_borrowed(v_buckets_1853_, v___x_1866_);
v___x_1868_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(v_a_1852_, v___x_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg___boxed(lean_object* v_m_1869_, lean_object* v_a_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_m_1869_, v_a_1870_);
lean_dec_ref(v_a_1870_);
lean_dec_ref(v_m_1869_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29___redArg(lean_object* v_x_1872_, lean_object* v_x_1873_){
_start:
{
if (lean_obj_tag(v_x_1873_) == 0)
{
return v_x_1872_;
}
else
{
lean_object* v_key_1874_; lean_object* v_value_1875_; lean_object* v_tail_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1899_; 
v_key_1874_ = lean_ctor_get(v_x_1873_, 0);
v_value_1875_ = lean_ctor_get(v_x_1873_, 1);
v_tail_1876_ = lean_ctor_get(v_x_1873_, 2);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_x_1873_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1878_ = v_x_1873_;
v_isShared_1879_ = v_isSharedCheck_1899_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_tail_1876_);
lean_inc(v_value_1875_);
lean_inc(v_key_1874_);
lean_dec(v_x_1873_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1899_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; uint64_t v___x_1881_; uint64_t v___x_1882_; uint64_t v___x_1883_; uint64_t v_fold_1884_; uint64_t v___x_1885_; uint64_t v___x_1886_; uint64_t v___x_1887_; size_t v___x_1888_; size_t v___x_1889_; size_t v___x_1890_; size_t v___x_1891_; size_t v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1895_; 
v___x_1880_ = lean_array_get_size(v_x_1872_);
v___x_1881_ = lean_string_hash(v_key_1874_);
v___x_1882_ = 32ULL;
v___x_1883_ = lean_uint64_shift_right(v___x_1881_, v___x_1882_);
v_fold_1884_ = lean_uint64_xor(v___x_1881_, v___x_1883_);
v___x_1885_ = 16ULL;
v___x_1886_ = lean_uint64_shift_right(v_fold_1884_, v___x_1885_);
v___x_1887_ = lean_uint64_xor(v_fold_1884_, v___x_1886_);
v___x_1888_ = lean_uint64_to_usize(v___x_1887_);
v___x_1889_ = lean_usize_of_nat(v___x_1880_);
v___x_1890_ = ((size_t)1ULL);
v___x_1891_ = lean_usize_sub(v___x_1889_, v___x_1890_);
v___x_1892_ = lean_usize_land(v___x_1888_, v___x_1891_);
v___x_1893_ = lean_array_uget_borrowed(v_x_1872_, v___x_1892_);
lean_inc(v___x_1893_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 2, v___x_1893_);
v___x_1895_ = v___x_1878_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_key_1874_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v_value_1875_);
lean_ctor_set(v_reuseFailAlloc_1898_, 2, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
lean_object* v___x_1896_; 
v___x_1896_ = lean_array_uset(v_x_1872_, v___x_1892_, v___x_1895_);
v_x_1872_ = v___x_1896_;
v_x_1873_ = v_tail_1876_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28___redArg(lean_object* v_i_1900_, lean_object* v_source_1901_, lean_object* v_target_1902_){
_start:
{
lean_object* v___x_1903_; uint8_t v___x_1904_; 
v___x_1903_ = lean_array_get_size(v_source_1901_);
v___x_1904_ = lean_nat_dec_lt(v_i_1900_, v___x_1903_);
if (v___x_1904_ == 0)
{
lean_dec_ref(v_source_1901_);
lean_dec(v_i_1900_);
return v_target_1902_;
}
else
{
lean_object* v_es_1905_; lean_object* v___x_1906_; lean_object* v_source_1907_; lean_object* v_target_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v_es_1905_ = lean_array_fget(v_source_1901_, v_i_1900_);
v___x_1906_ = lean_box(0);
v_source_1907_ = lean_array_fset(v_source_1901_, v_i_1900_, v___x_1906_);
v_target_1908_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29___redArg(v_target_1902_, v_es_1905_);
v___x_1909_ = lean_unsigned_to_nat(1u);
v___x_1910_ = lean_nat_add(v_i_1900_, v___x_1909_);
lean_dec(v_i_1900_);
v_i_1900_ = v___x_1910_;
v_source_1901_ = v_source_1907_;
v_target_1902_ = v_target_1908_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23___redArg(lean_object* v_data_1912_){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v_nbuckets_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1913_ = lean_array_get_size(v_data_1912_);
v___x_1914_ = lean_unsigned_to_nat(2u);
v_nbuckets_1915_ = lean_nat_mul(v___x_1913_, v___x_1914_);
v___x_1916_ = lean_unsigned_to_nat(0u);
v___x_1917_ = lean_box(0);
v___x_1918_ = lean_mk_array(v_nbuckets_1915_, v___x_1917_);
v___x_1919_ = lean_array_propagate_mark(v_data_1912_, v___x_1918_);
v___x_1920_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28___redArg(v___x_1916_, v_data_1912_, v___x_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(lean_object* v_a_1921_, lean_object* v_b_1922_, lean_object* v_x_1923_){
_start:
{
if (lean_obj_tag(v_x_1923_) == 0)
{
lean_dec(v_b_1922_);
lean_dec_ref(v_a_1921_);
return v_x_1923_;
}
else
{
lean_object* v_key_1924_; lean_object* v_value_1925_; lean_object* v_tail_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1938_; 
v_key_1924_ = lean_ctor_get(v_x_1923_, 0);
v_value_1925_ = lean_ctor_get(v_x_1923_, 1);
v_tail_1926_ = lean_ctor_get(v_x_1923_, 2);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_x_1923_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1928_ = v_x_1923_;
v_isShared_1929_ = v_isSharedCheck_1938_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_tail_1926_);
lean_inc(v_value_1925_);
lean_inc(v_key_1924_);
lean_dec(v_x_1923_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1938_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
uint8_t v___x_1930_; 
v___x_1930_ = lean_string_dec_eq(v_key_1924_, v_a_1921_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; lean_object* v___x_1933_; 
v___x_1931_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(v_a_1921_, v_b_1922_, v_tail_1926_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 2, v___x_1931_);
v___x_1933_ = v___x_1928_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_key_1924_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_value_1925_);
lean_ctor_set(v_reuseFailAlloc_1934_, 2, v___x_1931_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
else
{
lean_object* v___x_1936_; 
lean_dec(v_value_1925_);
lean_dec(v_key_1924_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 1, v_b_1922_);
lean_ctor_set(v___x_1928_, 0, v_a_1921_);
v___x_1936_ = v___x_1928_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1921_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_b_1922_);
lean_ctor_set(v_reuseFailAlloc_1937_, 2, v_tail_1926_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(lean_object* v_a_1939_, lean_object* v_x_1940_){
_start:
{
if (lean_obj_tag(v_x_1940_) == 0)
{
uint8_t v___x_1941_; 
v___x_1941_ = 0;
return v___x_1941_;
}
else
{
lean_object* v_key_1942_; lean_object* v_tail_1943_; uint8_t v___x_1944_; 
v_key_1942_ = lean_ctor_get(v_x_1940_, 0);
v_tail_1943_ = lean_ctor_get(v_x_1940_, 2);
v___x_1944_ = lean_string_dec_eq(v_key_1942_, v_a_1939_);
if (v___x_1944_ == 0)
{
v_x_1940_ = v_tail_1943_;
goto _start;
}
else
{
return v___x_1944_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1939_ = stack[0].m_obj;
lean_object* v_x_1940_ = stack[1].m_obj;
uint8_t v_res_1946_;
v_res_1946_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(v_a_1939_, v_x_1940_);
stack->m_num = v_res_1946_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg___boxed(lean_object* v_a_1947_, lean_object* v_x_1948_){
_start:
{
uint8_t v_res_1949_; lean_object* v_r_1950_; 
v_res_1949_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(v_a_1947_, v_x_1948_);
lean_dec(v_x_1948_);
lean_dec_ref(v_a_1947_);
v_r_1950_ = lean_box(v_res_1949_);
return v_r_1950_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(lean_object* v_m_1951_, lean_object* v_a_1952_, lean_object* v_b_1953_){
_start:
{
lean_object* v_size_1954_; lean_object* v_buckets_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1998_; 
v_size_1954_ = lean_ctor_get(v_m_1951_, 0);
v_buckets_1955_ = lean_ctor_get(v_m_1951_, 1);
v_isSharedCheck_1998_ = !lean_is_exclusive(v_m_1951_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1957_ = v_m_1951_;
v_isShared_1958_ = v_isSharedCheck_1998_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_buckets_1955_);
lean_inc(v_size_1954_);
lean_dec(v_m_1951_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1998_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1959_; uint64_t v___x_1960_; uint64_t v___x_1961_; uint64_t v___x_1962_; uint64_t v_fold_1963_; uint64_t v___x_1964_; uint64_t v___x_1965_; uint64_t v___x_1966_; size_t v___x_1967_; size_t v___x_1968_; size_t v___x_1969_; size_t v___x_1970_; size_t v___x_1971_; lean_object* v_bkt_1972_; uint8_t v___x_1973_; 
v___x_1959_ = lean_array_get_size(v_buckets_1955_);
v___x_1960_ = lean_string_hash(v_a_1952_);
v___x_1961_ = 32ULL;
v___x_1962_ = lean_uint64_shift_right(v___x_1960_, v___x_1961_);
v_fold_1963_ = lean_uint64_xor(v___x_1960_, v___x_1962_);
v___x_1964_ = 16ULL;
v___x_1965_ = lean_uint64_shift_right(v_fold_1963_, v___x_1964_);
v___x_1966_ = lean_uint64_xor(v_fold_1963_, v___x_1965_);
v___x_1967_ = lean_uint64_to_usize(v___x_1966_);
v___x_1968_ = lean_usize_of_nat(v___x_1959_);
v___x_1969_ = ((size_t)1ULL);
v___x_1970_ = lean_usize_sub(v___x_1968_, v___x_1969_);
v___x_1971_ = lean_usize_land(v___x_1967_, v___x_1970_);
v_bkt_1972_ = lean_array_uget_borrowed(v_buckets_1955_, v___x_1971_);
v___x_1973_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(v_a_1952_, v_bkt_1972_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; lean_object* v_size_x27_1975_; lean_object* v___x_1976_; lean_object* v_buckets_x27_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; 
v___x_1974_ = lean_unsigned_to_nat(1u);
v_size_x27_1975_ = lean_nat_add(v_size_1954_, v___x_1974_);
lean_dec(v_size_1954_);
lean_inc(v_bkt_1972_);
v___x_1976_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1976_, 0, v_a_1952_);
lean_ctor_set(v___x_1976_, 1, v_b_1953_);
lean_ctor_set(v___x_1976_, 2, v_bkt_1972_);
v_buckets_x27_1977_ = lean_array_uset(v_buckets_1955_, v___x_1971_, v___x_1976_);
v___x_1978_ = lean_unsigned_to_nat(4u);
v___x_1979_ = lean_nat_mul(v_size_x27_1975_, v___x_1978_);
v___x_1980_ = lean_unsigned_to_nat(3u);
v___x_1981_ = lean_nat_div(v___x_1979_, v___x_1980_);
lean_dec(v___x_1979_);
v___x_1982_ = lean_array_get_size(v_buckets_x27_1977_);
v___x_1983_ = lean_nat_dec_le(v___x_1981_, v___x_1982_);
lean_dec(v___x_1981_);
if (v___x_1983_ == 0)
{
lean_object* v_val_1984_; lean_object* v___x_1986_; 
v_val_1984_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23___redArg(v_buckets_x27_1977_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 1, v_val_1984_);
lean_ctor_set(v___x_1957_, 0, v_size_x27_1975_);
v___x_1986_ = v___x_1957_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_size_x27_1975_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_val_1984_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
else
{
lean_object* v___x_1989_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 1, v_buckets_x27_1977_);
lean_ctor_set(v___x_1957_, 0, v_size_x27_1975_);
v___x_1989_ = v___x_1957_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_size_x27_1975_);
lean_ctor_set(v_reuseFailAlloc_1990_, 1, v_buckets_x27_1977_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
else
{
lean_object* v___x_1991_; lean_object* v_buckets_x27_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1996_; 
lean_inc(v_bkt_1972_);
v___x_1991_ = lean_box(0);
v_buckets_x27_1992_ = lean_array_uset(v_buckets_1955_, v___x_1971_, v___x_1991_);
v___x_1993_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(v_a_1952_, v_b_1953_, v_bkt_1972_);
v___x_1994_ = lean_array_uset(v_buckets_x27_1992_, v___x_1971_, v___x_1993_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 1, v___x_1994_);
v___x_1996_ = v___x_1957_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_size_1954_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v___x_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___redArg(lean_object* v_histogram_1999_, lean_object* v_index_2000_, lean_object* v_val_2001_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_histogram_1999_, v_val_2001_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2003_ = lean_unsigned_to_nat(0u);
v___x_2004_ = lean_box(0);
v___x_2005_ = lean_unsigned_to_nat(1u);
v___x_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2006_, 0, v_index_2000_);
v___x_2007_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2003_);
lean_ctor_set(v___x_2007_, 1, v___x_2004_);
lean_ctor_set(v___x_2007_, 2, v___x_2005_);
lean_ctor_set(v___x_2007_, 3, v___x_2006_);
v___x_2008_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_1999_, v_val_2001_, v___x_2007_);
return v___x_2008_;
}
else
{
lean_object* v_val_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2030_; 
v_val_2009_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2011_ = v___x_2002_;
v_isShared_2012_ = v_isSharedCheck_2030_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_val_2009_);
lean_dec(v___x_2002_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2030_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v_leftCount_2013_; lean_object* v_leftIndex_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2027_; 
v_leftCount_2013_ = lean_ctor_get(v_val_2009_, 0);
v_leftIndex_2014_ = lean_ctor_get(v_val_2009_, 1);
v_isSharedCheck_2027_ = !lean_is_exclusive(v_val_2009_);
if (v_isSharedCheck_2027_ == 0)
{
lean_object* v_unused_2028_; lean_object* v_unused_2029_; 
v_unused_2028_ = lean_ctor_get(v_val_2009_, 3);
lean_dec(v_unused_2028_);
v_unused_2029_ = lean_ctor_get(v_val_2009_, 2);
lean_dec(v_unused_2029_);
v___x_2016_ = v_val_2009_;
v_isShared_2017_ = v_isSharedCheck_2027_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_leftIndex_2014_);
lean_inc(v_leftCount_2013_);
lean_dec(v_val_2009_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2027_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2021_; 
v___x_2018_ = lean_unsigned_to_nat(1u);
v___x_2019_ = lean_nat_add(v_leftCount_2013_, v___x_2018_);
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v_index_2000_);
v___x_2021_ = v___x_2011_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v_index_2000_);
v___x_2021_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2023_; 
if (v_isShared_2017_ == 0)
{
lean_ctor_set(v___x_2016_, 3, v___x_2021_);
lean_ctor_set(v___x_2016_, 2, v___x_2019_);
v___x_2023_ = v___x_2016_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_leftCount_2013_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_leftIndex_2014_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2025_, 3, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_1999_, v_val_2001_, v___x_2023_);
return v___x_2024_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(lean_object* v_upperBound_2031_, lean_object* v___x_2032_, lean_object* v_fst_2033_, lean_object* v___x_2034_, lean_object* v_a_2035_, lean_object* v_b_2036_){
_start:
{
uint8_t v___x_2037_; 
v___x_2037_ = lean_nat_dec_lt(v_a_2035_, v_upperBound_2031_);
if (v___x_2037_ == 0)
{
lean_dec(v_a_2035_);
return v_b_2036_;
}
else
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2038_ = l_Subarray_get___redArg(v_fst_2033_, v_a_2035_);
lean_inc(v_a_2035_);
v___x_2039_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___redArg(v_b_2036_, v_a_2035_, v___x_2038_);
v___x_2040_ = lean_unsigned_to_nat(1u);
v___x_2041_ = lean_nat_add(v_a_2035_, v___x_2040_);
lean_dec(v_a_2035_);
v_a_2035_ = v___x_2041_;
v_b_2036_ = v___x_2039_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg___boxed(lean_object* v_upperBound_2043_, lean_object* v___x_2044_, lean_object* v_fst_2045_, lean_object* v___x_2046_, lean_object* v_a_2047_, lean_object* v_b_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(v_upperBound_2043_, v___x_2044_, v_fst_2045_, v___x_2046_, v_a_2047_, v_b_2048_);
lean_dec(v___x_2046_);
lean_dec_ref(v_fst_2045_);
lean_dec(v___x_2044_);
lean_dec(v_upperBound_2043_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(lean_object* v_as_x27_2050_, lean_object* v_b_2051_){
_start:
{
if (lean_obj_tag(v_as_x27_2050_) == 0)
{
return v_b_2051_;
}
else
{
lean_object* v_head_2052_; lean_object* v_snd_2053_; lean_object* v_leftIndex_2054_; 
v_head_2052_ = lean_ctor_get(v_as_x27_2050_, 0);
v_snd_2053_ = lean_ctor_get(v_head_2052_, 1);
v_leftIndex_2054_ = lean_ctor_get(v_snd_2053_, 1);
if (lean_obj_tag(v_leftIndex_2054_) == 1)
{
lean_object* v_rightIndex_2055_; 
v_rightIndex_2055_ = lean_ctor_get(v_snd_2053_, 3);
if (lean_obj_tag(v_rightIndex_2055_) == 1)
{
if (lean_obj_tag(v_b_2051_) == 0)
{
lean_object* v_tail_2056_; lean_object* v_fst_2057_; lean_object* v_leftCount_2058_; lean_object* v_rightCount_2059_; lean_object* v_val_2060_; lean_object* v_val_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v_tail_2056_ = lean_ctor_get(v_as_x27_2050_, 1);
v_fst_2057_ = lean_ctor_get(v_head_2052_, 0);
v_leftCount_2058_ = lean_ctor_get(v_snd_2053_, 0);
v_rightCount_2059_ = lean_ctor_get(v_snd_2053_, 2);
v_val_2060_ = lean_ctor_get(v_leftIndex_2054_, 0);
v_val_2061_ = lean_ctor_get(v_rightIndex_2055_, 0);
v___x_2062_ = lean_nat_add(v_leftCount_2058_, v_rightCount_2059_);
lean_inc(v_val_2061_);
lean_inc(v_val_2060_);
v___x_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2063_, 0, v_val_2060_);
lean_ctor_set(v___x_2063_, 1, v_val_2061_);
lean_inc(v_fst_2057_);
v___x_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2064_, 0, v_fst_2057_);
lean_ctor_set(v___x_2064_, 1, v___x_2063_);
v___x_2065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2062_);
lean_ctor_set(v___x_2065_, 1, v___x_2064_);
v___x_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
v_as_x27_2050_ = v_tail_2056_;
v_b_2051_ = v___x_2066_;
goto _start;
}
else
{
lean_object* v_val_2068_; lean_object* v_tail_2069_; lean_object* v_fst_2070_; lean_object* v_leftCount_2071_; lean_object* v_rightCount_2072_; lean_object* v_val_2073_; lean_object* v_val_2074_; lean_object* v_fst_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2096_; 
v_val_2068_ = lean_ctor_get(v_b_2051_, 0);
lean_inc(v_val_2068_);
v_tail_2069_ = lean_ctor_get(v_as_x27_2050_, 1);
v_fst_2070_ = lean_ctor_get(v_head_2052_, 0);
v_leftCount_2071_ = lean_ctor_get(v_snd_2053_, 0);
v_rightCount_2072_ = lean_ctor_get(v_snd_2053_, 2);
v_val_2073_ = lean_ctor_get(v_leftIndex_2054_, 0);
v_val_2074_ = lean_ctor_get(v_rightIndex_2055_, 0);
v_fst_2075_ = lean_ctor_get(v_val_2068_, 0);
v_isSharedCheck_2096_ = !lean_is_exclusive(v_val_2068_);
if (v_isSharedCheck_2096_ == 0)
{
lean_object* v_unused_2097_; 
v_unused_2097_ = lean_ctor_get(v_val_2068_, 1);
lean_dec(v_unused_2097_);
v___x_2077_ = v_val_2068_;
v_isShared_2078_ = v_isSharedCheck_2096_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_fst_2075_);
lean_dec(v_val_2068_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2096_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2079_; uint8_t v___x_2080_; 
v___x_2079_ = lean_nat_add(v_leftCount_2071_, v_rightCount_2072_);
v___x_2080_ = lean_nat_dec_lt(v___x_2079_, v_fst_2075_);
lean_dec(v_fst_2075_);
if (v___x_2080_ == 0)
{
lean_dec(v___x_2079_);
lean_del_object(v___x_2077_);
v_as_x27_2050_ = v_tail_2069_;
goto _start;
}
else
{
lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2094_; 
v_isSharedCheck_2094_ = !lean_is_exclusive(v_b_2051_);
if (v_isSharedCheck_2094_ == 0)
{
lean_object* v_unused_2095_; 
v_unused_2095_ = lean_ctor_get(v_b_2051_, 0);
lean_dec(v_unused_2095_);
v___x_2083_ = v_b_2051_;
v_isShared_2084_ = v_isSharedCheck_2094_;
goto v_resetjp_2082_;
}
else
{
lean_dec(v_b_2051_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2094_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2086_; 
lean_inc(v_val_2074_);
lean_inc(v_val_2073_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 1, v_val_2074_);
lean_ctor_set(v___x_2077_, 0, v_val_2073_);
v___x_2086_ = v___x_2077_;
goto v_reusejp_2085_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_val_2073_);
lean_ctor_set(v_reuseFailAlloc_2093_, 1, v_val_2074_);
v___x_2086_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2085_;
}
v_reusejp_2085_:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2090_; 
lean_inc(v_fst_2070_);
v___x_2087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2087_, 0, v_fst_2070_);
lean_ctor_set(v___x_2087_, 1, v___x_2086_);
v___x_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2079_);
lean_ctor_set(v___x_2088_, 1, v___x_2087_);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 0, v___x_2088_);
v___x_2090_ = v___x_2083_;
goto v_reusejp_2089_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v___x_2088_);
v___x_2090_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2089_;
}
v_reusejp_2089_:
{
v_as_x27_2050_ = v_tail_2069_;
v_b_2051_ = v___x_2090_;
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
lean_object* v_tail_2098_; 
v_tail_2098_ = lean_ctor_get(v_as_x27_2050_, 1);
v_as_x27_2050_ = v_tail_2098_;
goto _start;
}
}
else
{
lean_object* v_tail_2100_; 
v_tail_2100_ = lean_ctor_get(v_as_x27_2050_, 1);
v_as_x27_2050_ = v_tail_2100_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_as_x27_2102_, lean_object* v_b_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(v_as_x27_2102_, v_b_2103_);
lean_dec(v_as_x27_2102_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(lean_object* v_a_2105_, lean_object* v_b_2106_){
_start:
{
lean_object* v_array_2107_; lean_object* v_start_2108_; lean_object* v_stop_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2122_; 
v_array_2107_ = lean_ctor_get(v_a_2105_, 0);
v_start_2108_ = lean_ctor_get(v_a_2105_, 1);
v_stop_2109_ = lean_ctor_get(v_a_2105_, 2);
v_isSharedCheck_2122_ = !lean_is_exclusive(v_a_2105_);
if (v_isSharedCheck_2122_ == 0)
{
v___x_2111_ = v_a_2105_;
v_isShared_2112_ = v_isSharedCheck_2122_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_stop_2109_);
lean_inc(v_start_2108_);
lean_inc(v_array_2107_);
lean_dec(v_a_2105_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2122_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
uint8_t v___x_2113_; 
v___x_2113_ = lean_nat_dec_lt(v_start_2108_, v_stop_2109_);
if (v___x_2113_ == 0)
{
lean_del_object(v___x_2111_);
lean_dec(v_stop_2109_);
lean_dec(v_start_2108_);
lean_dec_ref(v_array_2107_);
return v_b_2106_;
}
else
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2117_; 
v___x_2114_ = lean_unsigned_to_nat(1u);
v___x_2115_ = lean_nat_add(v_start_2108_, v___x_2114_);
lean_inc_ref(v_array_2107_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 1, v___x_2115_);
v___x_2117_ = v___x_2111_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2121_; 
v_reuseFailAlloc_2121_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2121_, 0, v_array_2107_);
lean_ctor_set(v_reuseFailAlloc_2121_, 1, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2121_, 2, v_stop_2109_);
v___x_2117_ = v_reuseFailAlloc_2121_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = lean_array_fget(v_array_2107_, v_start_2108_);
lean_dec(v_start_2108_);
lean_dec_ref(v_array_2107_);
v___x_2119_ = lean_array_push(v_b_2106_, v___x_2118_);
v_a_2105_ = v___x_2117_;
v_b_2106_ = v___x_2119_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8(lean_object* v_left_2123_, lean_object* v_right_2124_, lean_object* v_i_2125_){
_start:
{
lean_object* v_start_2126_; lean_object* v_stop_2127_; lean_object* v___x_2128_; uint8_t v___x_2142_; 
v_start_2126_ = lean_ctor_get(v_left_2123_, 1);
v_stop_2127_ = lean_ctor_get(v_left_2123_, 2);
v___x_2128_ = lean_nat_sub(v_stop_2127_, v_start_2126_);
v___x_2142_ = lean_nat_dec_lt(v_i_2125_, v___x_2128_);
if (v___x_2142_ == 0)
{
goto v___jp_2129_;
}
else
{
lean_object* v_start_2143_; lean_object* v_stop_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
v_start_2143_ = lean_ctor_get(v_right_2124_, 1);
v_stop_2144_ = lean_ctor_get(v_right_2124_, 2);
v___x_2145_ = lean_nat_sub(v_stop_2144_, v_start_2143_);
v___x_2146_ = lean_nat_dec_lt(v_i_2125_, v___x_2145_);
if (v___x_2146_ == 0)
{
lean_dec(v___x_2145_);
goto v___jp_2129_;
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; uint8_t v___x_2154_; 
v___x_2147_ = lean_nat_sub(v___x_2128_, v_i_2125_);
lean_dec(v___x_2128_);
v___x_2148_ = lean_unsigned_to_nat(1u);
v___x_2149_ = lean_nat_sub(v___x_2147_, v___x_2148_);
v___x_2150_ = l_Subarray_get___redArg(v_left_2123_, v___x_2149_);
lean_dec(v___x_2149_);
v___x_2151_ = lean_nat_sub(v___x_2145_, v_i_2125_);
lean_dec(v___x_2145_);
v___x_2152_ = lean_nat_sub(v___x_2151_, v___x_2148_);
v___x_2153_ = l_Subarray_get___redArg(v_right_2124_, v___x_2152_);
lean_dec(v___x_2152_);
v___x_2154_ = lean_string_dec_eq(v___x_2150_, v___x_2153_);
lean_dec(v___x_2153_);
lean_dec(v___x_2150_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
lean_dec(v_i_2125_);
lean_inc_ref(v_left_2123_);
v___x_2155_ = l_Subarray_take___redArg(v_left_2123_, v___x_2147_);
v___x_2156_ = l_Subarray_take___redArg(v_right_2124_, v___x_2151_);
lean_dec(v___x_2151_);
v___x_2157_ = l_Subarray_drop___redArg(v_left_2123_, v___x_2147_);
lean_dec(v___x_2147_);
v___x_2158_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2159_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(v___x_2157_, v___x_2158_);
v___x_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2156_);
lean_ctor_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2155_);
lean_ctor_set(v___x_2161_, 1, v___x_2160_);
return v___x_2161_;
}
else
{
lean_object* v___x_2162_; 
lean_dec(v___x_2151_);
lean_dec(v___x_2147_);
v___x_2162_ = lean_nat_add(v_i_2125_, v___x_2148_);
lean_dec(v_i_2125_);
v_i_2125_ = v___x_2162_;
goto _start;
}
}
}
v___jp_2129_:
{
lean_object* v_start_2130_; lean_object* v_stop_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v_start_2130_ = lean_ctor_get(v_right_2124_, 1);
v_stop_2131_ = lean_ctor_get(v_right_2124_, 2);
v___x_2132_ = lean_nat_sub(v___x_2128_, v_i_2125_);
lean_dec(v___x_2128_);
lean_inc_ref(v_left_2123_);
v___x_2133_ = l_Subarray_take___redArg(v_left_2123_, v___x_2132_);
v___x_2134_ = lean_nat_sub(v_stop_2131_, v_start_2130_);
v___x_2135_ = lean_nat_sub(v___x_2134_, v_i_2125_);
lean_dec(v_i_2125_);
lean_dec(v___x_2134_);
v___x_2136_ = l_Subarray_take___redArg(v_right_2124_, v___x_2135_);
lean_dec(v___x_2135_);
v___x_2137_ = l_Subarray_drop___redArg(v_left_2123_, v___x_2132_);
lean_dec(v___x_2132_);
v___x_2138_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords___closed__0));
v___x_2139_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(v___x_2137_, v___x_2138_);
v___x_2140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2136_);
lean_ctor_set(v___x_2140_, 1, v___x_2139_);
v___x_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2133_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
return v___x_2141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5(lean_object* v_left_2164_, lean_object* v_right_2165_){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2166_ = lean_unsigned_to_nat(0u);
v___x_2167_ = l___private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8(v_left_2164_, v_right_2165_, v___x_2166_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___redArg(lean_object* v_histogram_2168_, lean_object* v_index_2169_, lean_object* v_val_2170_){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_histogram_2168_, v_val_2170_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2172_ = lean_unsigned_to_nat(1u);
v___x_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2173_, 0, v_index_2169_);
v___x_2174_ = lean_unsigned_to_nat(0u);
v___x_2175_ = lean_box(0);
v___x_2176_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2172_);
lean_ctor_set(v___x_2176_, 1, v___x_2173_);
lean_ctor_set(v___x_2176_, 2, v___x_2174_);
lean_ctor_set(v___x_2176_, 3, v___x_2175_);
v___x_2177_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_2168_, v_val_2170_, v___x_2176_);
return v___x_2177_;
}
else
{
lean_object* v_val_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2199_; 
v_val_2178_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2180_ = v___x_2171_;
v_isShared_2181_ = v_isSharedCheck_2199_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_val_2178_);
lean_dec(v___x_2171_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2199_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v_leftCount_2182_; lean_object* v_rightCount_2183_; lean_object* v_rightIndex_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2197_; 
v_leftCount_2182_ = lean_ctor_get(v_val_2178_, 0);
v_rightCount_2183_ = lean_ctor_get(v_val_2178_, 2);
v_rightIndex_2184_ = lean_ctor_get(v_val_2178_, 3);
v_isSharedCheck_2197_ = !lean_is_exclusive(v_val_2178_);
if (v_isSharedCheck_2197_ == 0)
{
lean_object* v_unused_2198_; 
v_unused_2198_ = lean_ctor_get(v_val_2178_, 1);
lean_dec(v_unused_2198_);
v___x_2186_ = v_val_2178_;
v_isShared_2187_ = v_isSharedCheck_2197_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_rightIndex_2184_);
lean_inc(v_rightCount_2183_);
lean_inc(v_leftCount_2182_);
lean_dec(v_val_2178_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2197_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2191_; 
v___x_2188_ = lean_unsigned_to_nat(1u);
v___x_2189_ = lean_nat_add(v_leftCount_2182_, v___x_2188_);
lean_dec(v_leftCount_2182_);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v_index_2169_);
v___x_2191_ = v___x_2180_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_index_2169_);
v___x_2191_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
lean_object* v___x_2193_; 
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 1, v___x_2191_);
lean_ctor_set(v___x_2186_, 0, v___x_2189_);
v___x_2193_ = v___x_2186_;
goto v_reusejp_2192_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v___x_2191_);
lean_ctor_set(v_reuseFailAlloc_2195_, 2, v_rightCount_2183_);
lean_ctor_set(v_reuseFailAlloc_2195_, 3, v_rightIndex_2184_);
v___x_2193_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2192_;
}
v_reusejp_2192_:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_histogram_2168_, v_val_2170_, v___x_2193_);
return v___x_2194_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(lean_object* v_upperBound_2200_, lean_object* v_fst_2201_, lean_object* v___x_2202_, lean_object* v_fst_2203_, lean_object* v_a_2204_, lean_object* v_b_2205_){
_start:
{
uint8_t v___x_2206_; 
v___x_2206_ = lean_nat_dec_lt(v_a_2204_, v_upperBound_2200_);
if (v___x_2206_ == 0)
{
lean_dec(v_a_2204_);
return v_b_2205_;
}
else
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2207_ = l_Subarray_get___redArg(v_fst_2203_, v_a_2204_);
lean_inc(v_a_2204_);
v___x_2208_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___redArg(v_b_2205_, v_a_2204_, v___x_2207_);
v___x_2209_ = lean_unsigned_to_nat(1u);
v___x_2210_ = lean_nat_add(v_a_2204_, v___x_2209_);
lean_dec(v_a_2204_);
v_a_2204_ = v___x_2210_;
v_b_2205_ = v___x_2208_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg___boxed(lean_object* v_upperBound_2212_, lean_object* v_fst_2213_, lean_object* v___x_2214_, lean_object* v_fst_2215_, lean_object* v_a_2216_, lean_object* v_b_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(v_upperBound_2212_, v_fst_2213_, v___x_2214_, v_fst_2215_, v_a_2216_, v_b_2217_);
lean_dec_ref(v_fst_2215_);
lean_dec(v___x_2214_);
lean_dec_ref(v_fst_2213_);
lean_dec(v_upperBound_2212_);
return v_res_2218_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2219_ = lean_box(0);
v___x_2220_ = lean_unsigned_to_nat(16u);
v___x_2221_ = lean_mk_array(v___x_2220_, v___x_2219_);
return v___x_2221_;
}
}
static lean_object* _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1(void){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v_hist_2224_; 
v___x_2222_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__0);
v___x_2223_ = lean_unsigned_to_nat(0u);
v_hist_2224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_hist_2224_, 0, v___x_2223_);
lean_ctor_set(v_hist_2224_, 1, v___x_2222_);
return v_hist_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(lean_object* v_left_2225_, lean_object* v_right_2226_){
_start:
{
lean_object* v___x_2227_; lean_object* v_snd_2228_; lean_object* v_fst_2229_; lean_object* v_fst_2230_; lean_object* v_snd_2231_; lean_object* v___x_2232_; lean_object* v_snd_2233_; lean_object* v_fst_2234_; lean_object* v_fst_2235_; lean_object* v_snd_2236_; lean_object* v_start_2237_; lean_object* v_stop_2238_; lean_object* v___x_2239_; lean_object* v_hist_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v_start_2243_; lean_object* v_stop_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v_buckets_2247_; lean_object* v___x_2248_; lean_object* v___y_2250_; lean_object* v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; 
v___x_2227_ = l_Lean_Diff_matchPrefix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__4(v_left_2225_, v_right_2226_);
v_snd_2228_ = lean_ctor_get(v___x_2227_, 1);
lean_inc(v_snd_2228_);
v_fst_2229_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_fst_2229_);
lean_dec_ref(v___x_2227_);
v_fst_2230_ = lean_ctor_get(v_snd_2228_, 0);
lean_inc(v_fst_2230_);
v_snd_2231_ = lean_ctor_get(v_snd_2228_, 1);
lean_inc(v_snd_2231_);
lean_dec(v_snd_2228_);
v___x_2232_ = l_Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5(v_fst_2230_, v_snd_2231_);
v_snd_2233_ = lean_ctor_get(v___x_2232_, 1);
lean_inc(v_snd_2233_);
v_fst_2234_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_fst_2234_);
lean_dec_ref(v___x_2232_);
v_fst_2235_ = lean_ctor_get(v_snd_2233_, 0);
lean_inc(v_fst_2235_);
v_snd_2236_ = lean_ctor_get(v_snd_2233_, 1);
lean_inc(v_snd_2236_);
lean_dec(v_snd_2233_);
v_start_2237_ = lean_ctor_get(v_fst_2234_, 1);
v_stop_2238_ = lean_ctor_get(v_fst_2234_, 2);
v___x_2239_ = lean_unsigned_to_nat(0u);
v_hist_2240_ = lean_obj_once(&l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1, &l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1_once, _init_l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3___closed__1);
v___x_2241_ = lean_nat_sub(v_stop_2238_, v_start_2237_);
v___x_2242_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(v___x_2241_, v_fst_2235_, v___x_2241_, v_fst_2234_, v___x_2239_, v_hist_2240_);
v_start_2243_ = lean_ctor_get(v_fst_2235_, 1);
v_stop_2244_ = lean_ctor_get(v_fst_2235_, 2);
v___x_2245_ = lean_nat_sub(v_stop_2244_, v_start_2243_);
v___x_2246_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(v___x_2245_, v___x_2245_, v_fst_2235_, v___x_2241_, v___x_2239_, v___x_2242_);
lean_dec(v___x_2241_);
lean_dec(v___x_2245_);
v_buckets_2247_ = lean_ctor_get(v___x_2246_, 1);
lean_inc_ref(v_buckets_2247_);
lean_dec_ref(v___x_2246_);
v___x_2248_ = lean_box(0);
v___x_2276_ = lean_box(0);
v___x_2277_ = lean_array_get_size(v_buckets_2247_);
v___x_2278_ = lean_nat_dec_lt(v___x_2239_, v___x_2277_);
if (v___x_2278_ == 0)
{
lean_dec_ref(v_buckets_2247_);
v___y_2250_ = v___x_2276_;
goto v___jp_2249_;
}
else
{
size_t v___x_2279_; size_t v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = lean_usize_of_nat(v___x_2277_);
v___x_2280_ = ((size_t)0ULL);
v___x_2281_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__8(v_buckets_2247_, v___x_2279_, v___x_2280_, v___x_2276_);
lean_dec_ref(v_buckets_2247_);
v___y_2250_ = v___x_2281_;
goto v___jp_2249_;
}
v___jp_2249_:
{
lean_object* v___x_2251_; 
v___x_2251_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(v___y_2250_, v___x_2248_);
lean_dec(v___y_2250_);
if (lean_obj_tag(v___x_2251_) == 1)
{
lean_object* v_val_2252_; lean_object* v_snd_2253_; lean_object* v_snd_2254_; lean_object* v_fst_2255_; lean_object* v_fst_2256_; lean_object* v_snd_2257_; lean_object* v___x_2258_; lean_object* v_fst_2259_; lean_object* v_snd_2260_; lean_object* v___x_2261_; lean_object* v_fst_2262_; lean_object* v_snd_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v_val_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_val_2252_);
lean_dec_ref_known(v___x_2251_, 1);
v_snd_2253_ = lean_ctor_get(v_val_2252_, 1);
lean_inc(v_snd_2253_);
lean_dec(v_val_2252_);
v_snd_2254_ = lean_ctor_get(v_snd_2253_, 1);
lean_inc(v_snd_2254_);
v_fst_2255_ = lean_ctor_get(v_snd_2253_, 0);
lean_inc(v_fst_2255_);
lean_dec(v_snd_2253_);
v_fst_2256_ = lean_ctor_get(v_snd_2254_, 0);
lean_inc(v_fst_2256_);
v_snd_2257_ = lean_ctor_get(v_snd_2254_, 1);
lean_inc(v_snd_2257_);
lean_dec(v_snd_2254_);
v___x_2258_ = l_Subarray_split___redArg(v_fst_2234_, v_fst_2256_);
lean_dec(v_fst_2256_);
v_fst_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_fst_2259_);
v_snd_2260_ = lean_ctor_get(v___x_2258_, 1);
lean_inc(v_snd_2260_);
lean_dec_ref(v___x_2258_);
v___x_2261_ = l_Subarray_split___redArg(v_fst_2235_, v_snd_2257_);
lean_dec(v_snd_2257_);
v_fst_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_fst_2262_);
v_snd_2263_ = lean_ctor_get(v___x_2261_, 1);
lean_inc(v_snd_2263_);
lean_dec_ref(v___x_2261_);
v___x_2264_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v_fst_2259_, v_fst_2262_);
v___x_2265_ = l_Array_append___redArg(v_fst_2229_, v___x_2264_);
lean_dec_ref(v___x_2264_);
v___x_2266_ = lean_unsigned_to_nat(1u);
v___x_2267_ = lean_mk_empty_array_with_capacity(v___x_2266_);
v___x_2268_ = lean_array_push(v___x_2267_, v_fst_2255_);
v___x_2269_ = l_Array_append___redArg(v___x_2265_, v___x_2268_);
lean_dec_ref(v___x_2268_);
v___x_2270_ = l_Subarray_drop___redArg(v_snd_2260_, v___x_2266_);
v___x_2271_ = l_Subarray_drop___redArg(v_snd_2263_, v___x_2266_);
v___x_2272_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v___x_2270_, v___x_2271_);
v___x_2273_ = l_Array_append___redArg(v___x_2269_, v___x_2272_);
lean_dec_ref(v___x_2272_);
v___x_2274_ = l_Array_append___redArg(v___x_2273_, v_snd_2236_);
lean_dec(v_snd_2236_);
return v___x_2274_;
}
else
{
lean_object* v___x_2275_; 
lean_dec(v___x_2251_);
lean_dec(v_fst_2235_);
lean_dec(v_fst_2234_);
v___x_2275_ = l_Array_append___redArg(v_fst_2229_, v_snd_2236_);
lean_dec(v_snd_2236_);
return v___x_2275_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(lean_object* v___x_2282_, lean_object* v_original_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v_fst_2285_; lean_object* v_snd_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2305_; 
v_fst_2285_ = lean_ctor_get(v_a_2284_, 0);
v_snd_2286_ = lean_ctor_get(v_a_2284_, 1);
v_isSharedCheck_2305_ = !lean_is_exclusive(v_a_2284_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2288_ = v_a_2284_;
v_isShared_2289_ = v_isSharedCheck_2305_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_snd_2286_);
lean_inc(v_fst_2285_);
lean_dec(v_a_2284_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2305_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
uint8_t v___x_2290_; 
v___x_2290_ = lean_nat_dec_lt(v_snd_2286_, v___x_2282_);
if (v___x_2290_ == 0)
{
lean_object* v___x_2292_; 
if (v_isShared_2289_ == 0)
{
v___x_2292_ = v___x_2288_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_fst_2285_);
lean_ctor_set(v_reuseFailAlloc_2293_, 1, v_snd_2286_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
else
{
uint8_t v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2298_; 
v___x_2294_ = 1;
v___x_2295_ = lean_array_fget_borrowed(v_original_2283_, v_snd_2286_);
v___x_2296_ = lean_box(v___x_2294_);
lean_inc(v___x_2295_);
if (v_isShared_2289_ == 0)
{
lean_ctor_set(v___x_2288_, 1, v___x_2295_);
lean_ctor_set(v___x_2288_, 0, v___x_2296_);
v___x_2298_ = v___x_2288_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v___x_2296_);
lean_ctor_set(v_reuseFailAlloc_2304_, 1, v___x_2295_);
v___x_2298_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2299_ = lean_array_push(v_fst_2285_, v___x_2298_);
v___x_2300_ = lean_unsigned_to_nat(1u);
v___x_2301_ = lean_nat_add(v_snd_2286_, v___x_2300_);
lean_dec(v_snd_2286_);
v___x_2302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2299_);
lean_ctor_set(v___x_2302_, 1, v___x_2301_);
v_a_2284_ = v___x_2302_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg___boxed(lean_object* v___x_2306_, lean_object* v_original_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v_res_2309_; 
v_res_2309_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2306_, v_original_2307_, v_a_2308_);
lean_dec_ref(v_original_2307_);
lean_dec(v___x_2306_);
return v_res_2309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(lean_object* v___x_2310_, lean_object* v_edited_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v_fst_2313_; lean_object* v_snd_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2333_; 
v_fst_2313_ = lean_ctor_get(v_a_2312_, 0);
v_snd_2314_ = lean_ctor_get(v_a_2312_, 1);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_a_2312_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2316_ = v_a_2312_;
v_isShared_2317_ = v_isSharedCheck_2333_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_snd_2314_);
lean_inc(v_fst_2313_);
lean_dec(v_a_2312_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2333_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
uint8_t v___x_2318_; 
v___x_2318_ = lean_nat_dec_lt(v_snd_2314_, v___x_2310_);
if (v___x_2318_ == 0)
{
lean_object* v___x_2320_; 
if (v_isShared_2317_ == 0)
{
v___x_2320_ = v___x_2316_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_fst_2313_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_snd_2314_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
else
{
uint8_t v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2326_; 
v___x_2322_ = 0;
v___x_2323_ = lean_array_fget_borrowed(v_edited_2311_, v_snd_2314_);
v___x_2324_ = lean_box(v___x_2322_);
lean_inc(v___x_2323_);
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 1, v___x_2323_);
lean_ctor_set(v___x_2316_, 0, v___x_2324_);
v___x_2326_ = v___x_2316_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2324_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v___x_2323_);
v___x_2326_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2327_ = lean_array_push(v_fst_2313_, v___x_2326_);
v___x_2328_ = lean_unsigned_to_nat(1u);
v___x_2329_ = lean_nat_add(v_snd_2314_, v___x_2328_);
lean_dec(v_snd_2314_);
v___x_2330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2327_);
lean_ctor_set(v___x_2330_, 1, v___x_2329_);
v_a_2312_ = v___x_2330_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg___boxed(lean_object* v___x_2334_, lean_object* v_edited_2335_, lean_object* v_a_2336_){
_start:
{
lean_object* v_res_2337_; 
v_res_2337_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2334_, v_edited_2335_, v_a_2336_);
lean_dec_ref(v_edited_2335_);
lean_dec(v___x_2334_);
return v_res_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(lean_object* v___x_2338_, lean_object* v_original_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_){
_start:
{
lean_object* v_fst_2342_; lean_object* v_snd_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2367_; 
v_fst_2342_ = lean_ctor_get(v_a_2341_, 0);
v_snd_2343_ = lean_ctor_get(v_a_2341_, 1);
v_isSharedCheck_2367_ = !lean_is_exclusive(v_a_2341_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2345_ = v_a_2341_;
v_isShared_2346_ = v_isSharedCheck_2367_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_snd_2343_);
lean_inc(v_fst_2342_);
lean_dec(v_a_2341_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2367_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
uint8_t v___x_2347_; 
v___x_2347_ = lean_nat_dec_lt(v_snd_2343_, v___x_2338_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2349_; 
if (v_isShared_2346_ == 0)
{
v___x_2349_ = v___x_2345_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_fst_2342_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v_snd_2343_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
else
{
lean_object* v___x_2351_; lean_object* v___x_2352_; uint8_t v___x_2353_; 
v___x_2351_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2352_ = lean_array_get_borrowed(v___x_2351_, v_original_2339_, v_snd_2343_);
v___x_2353_ = lean_string_dec_eq(v___x_2352_, v_a_2340_);
if (v___x_2353_ == 0)
{
uint8_t v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2357_; 
v___x_2354_ = 1;
v___x_2355_ = lean_box(v___x_2354_);
lean_inc(v___x_2352_);
if (v_isShared_2346_ == 0)
{
lean_ctor_set(v___x_2345_, 1, v___x_2352_);
lean_ctor_set(v___x_2345_, 0, v___x_2355_);
v___x_2357_ = v___x_2345_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2355_);
lean_ctor_set(v_reuseFailAlloc_2363_, 1, v___x_2352_);
v___x_2357_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2358_ = lean_array_push(v_fst_2342_, v___x_2357_);
v___x_2359_ = lean_unsigned_to_nat(1u);
v___x_2360_ = lean_nat_add(v_snd_2343_, v___x_2359_);
lean_dec(v_snd_2343_);
v___x_2361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2358_);
lean_ctor_set(v___x_2361_, 1, v___x_2360_);
v_a_2341_ = v___x_2361_;
goto _start;
}
}
else
{
lean_object* v___x_2365_; 
if (v_isShared_2346_ == 0)
{
v___x_2365_ = v___x_2345_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_fst_2342_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v_snd_2343_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg___boxed(lean_object* v___x_2368_, lean_object* v_original_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2368_, v_original_2369_, v_a_2370_, v_a_2371_);
lean_dec_ref(v_a_2370_);
lean_dec_ref(v_original_2369_);
lean_dec(v___x_2368_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(lean_object* v___x_2373_, lean_object* v_edited_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
lean_object* v_fst_2377_; lean_object* v_snd_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2402_; 
v_fst_2377_ = lean_ctor_get(v_a_2376_, 0);
v_snd_2378_ = lean_ctor_get(v_a_2376_, 1);
v_isSharedCheck_2402_ = !lean_is_exclusive(v_a_2376_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2380_ = v_a_2376_;
v_isShared_2381_ = v_isSharedCheck_2402_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_snd_2378_);
lean_inc(v_fst_2377_);
lean_dec(v_a_2376_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2402_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
uint8_t v___x_2382_; 
v___x_2382_ = lean_nat_dec_lt(v_snd_2378_, v___x_2373_);
if (v___x_2382_ == 0)
{
lean_object* v___x_2384_; 
if (v_isShared_2381_ == 0)
{
v___x_2384_ = v___x_2380_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_fst_2377_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_snd_2378_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
else
{
lean_object* v___x_2386_; lean_object* v___x_2387_; uint8_t v___x_2388_; 
v___x_2386_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2387_ = lean_array_get_borrowed(v___x_2386_, v_edited_2374_, v_snd_2378_);
v___x_2388_ = lean_string_dec_eq(v___x_2387_, v_a_2375_);
if (v___x_2388_ == 0)
{
uint8_t v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2392_; 
v___x_2389_ = 0;
v___x_2390_ = lean_box(v___x_2389_);
lean_inc(v___x_2387_);
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 1, v___x_2387_);
lean_ctor_set(v___x_2380_, 0, v___x_2390_);
v___x_2392_ = v___x_2380_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2390_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v___x_2387_);
v___x_2392_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2393_ = lean_array_push(v_fst_2377_, v___x_2392_);
v___x_2394_ = lean_unsigned_to_nat(1u);
v___x_2395_ = lean_nat_add(v_snd_2378_, v___x_2394_);
lean_dec(v_snd_2378_);
v___x_2396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2393_);
lean_ctor_set(v___x_2396_, 1, v___x_2395_);
v_a_2376_ = v___x_2396_;
goto _start;
}
}
else
{
lean_object* v___x_2400_; 
if (v_isShared_2381_ == 0)
{
v___x_2400_ = v___x_2380_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_fst_2377_);
lean_ctor_set(v_reuseFailAlloc_2401_, 1, v_snd_2378_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg___boxed(lean_object* v___x_2403_, lean_object* v_edited_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2403_, v_edited_2404_, v_a_2405_, v_a_2406_);
lean_dec_ref(v_a_2405_);
lean_dec_ref(v_edited_2404_);
lean_dec(v___x_2403_);
return v_res_2407_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(lean_object* v___x_2408_, lean_object* v_original_2409_, lean_object* v___x_2410_, lean_object* v_edited_2411_, lean_object* v_as_2412_, size_t v_sz_2413_, size_t v_i_2414_, lean_object* v_b_2415_){
_start:
{
uint8_t v___x_2416_; 
v___x_2416_ = lean_usize_dec_lt(v_i_2414_, v_sz_2413_);
if (v___x_2416_ == 0)
{
return v_b_2415_;
}
else
{
lean_object* v_snd_2417_; lean_object* v_fst_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2465_; 
v_snd_2417_ = lean_ctor_get(v_b_2415_, 1);
v_fst_2418_ = lean_ctor_get(v_b_2415_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v_b_2415_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2420_ = v_b_2415_;
v_isShared_2421_ = v_isSharedCheck_2465_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_snd_2417_);
lean_inc(v_fst_2418_);
lean_dec(v_b_2415_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2465_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v_fst_2422_; lean_object* v_snd_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2464_; 
v_fst_2422_ = lean_ctor_get(v_snd_2417_, 0);
v_snd_2423_ = lean_ctor_get(v_snd_2417_, 1);
v_isSharedCheck_2464_ = !lean_is_exclusive(v_snd_2417_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2425_ = v_snd_2417_;
v_isShared_2426_ = v_isSharedCheck_2464_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_snd_2423_);
lean_inc(v_fst_2422_);
lean_dec(v_snd_2417_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2464_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v_a_2427_; lean_object* v___x_2429_; 
v_a_2427_ = lean_array_uget_borrowed(v_as_2412_, v_i_2414_);
if (v_isShared_2426_ == 0)
{
lean_ctor_set(v___x_2425_, 1, v_fst_2422_);
lean_ctor_set(v___x_2425_, 0, v_fst_2418_);
v___x_2429_ = v___x_2425_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_fst_2418_);
lean_ctor_set(v_reuseFailAlloc_2463_, 1, v_fst_2422_);
v___x_2429_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
lean_object* v___x_2430_; lean_object* v_fst_2431_; lean_object* v_snd_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2462_; 
v___x_2430_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2408_, v_original_2409_, v_a_2427_, v___x_2429_);
v_fst_2431_ = lean_ctor_get(v___x_2430_, 0);
v_snd_2432_ = lean_ctor_get(v___x_2430_, 1);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2434_ = v___x_2430_;
v_isShared_2435_ = v_isSharedCheck_2462_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_snd_2432_);
lean_inc(v_fst_2431_);
lean_dec(v___x_2430_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2462_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 1, v_snd_2423_);
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_fst_2431_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v_snd_2423_);
v___x_2437_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
lean_object* v___x_2438_; lean_object* v_fst_2439_; lean_object* v_snd_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2460_; 
v___x_2438_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2410_, v_edited_2411_, v_a_2427_, v___x_2437_);
v_fst_2439_ = lean_ctor_get(v___x_2438_, 0);
v_snd_2440_ = lean_ctor_get(v___x_2438_, 1);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2442_ = v___x_2438_;
v_isShared_2443_ = v_isSharedCheck_2460_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_snd_2440_);
lean_inc(v_fst_2439_);
lean_dec(v___x_2438_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2460_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
uint8_t v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2447_; 
v___x_2444_ = 2;
v___x_2445_ = lean_box(v___x_2444_);
lean_inc(v_a_2427_);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 1, v_a_2427_);
lean_ctor_set(v___x_2442_, 0, v___x_2445_);
v___x_2447_ = v___x_2442_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v___x_2445_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v_a_2427_);
v___x_2447_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2453_; 
v___x_2448_ = lean_array_push(v_fst_2439_, v___x_2447_);
v___x_2449_ = lean_unsigned_to_nat(1u);
v___x_2450_ = lean_nat_add(v_snd_2432_, v___x_2449_);
lean_dec(v_snd_2432_);
v___x_2451_ = lean_nat_add(v_snd_2440_, v___x_2449_);
lean_dec(v_snd_2440_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 1, v___x_2451_);
lean_ctor_set(v___x_2420_, 0, v___x_2450_);
v___x_2453_ = v___x_2420_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2450_);
lean_ctor_set(v_reuseFailAlloc_2458_, 1, v___x_2451_);
v___x_2453_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
lean_object* v___x_2454_; size_t v___x_2455_; size_t v___x_2456_; 
v___x_2454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2454_, 0, v___x_2448_);
lean_ctor_set(v___x_2454_, 1, v___x_2453_);
v___x_2455_ = ((size_t)1ULL);
v___x_2456_ = lean_usize_add(v_i_2414_, v___x_2455_);
v_i_2414_ = v___x_2456_;
v_b_2415_ = v___x_2454_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2408_ = stack[0].m_obj;
lean_object* v_original_2409_ = stack[1].m_obj;
lean_object* v___x_2410_ = stack[2].m_obj;
lean_object* v_edited_2411_ = stack[3].m_obj;
lean_object* v_as_2412_ = stack[4].m_obj;
size_t v_sz_2413_ = stack[5].m_num;
size_t v_i_2414_ = stack[6].m_num;
lean_object* v_b_2415_ = stack[7].m_obj;
lean_object* v_res_2466_;
v_res_2466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v___x_2408_, v_original_2409_, v___x_2410_, v_edited_2411_, v_as_2412_, v_sz_2413_, v_i_2414_, v_b_2415_);
stack->m_obj
 = v_res_2466_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14___boxed(lean_object* v___x_2467_, lean_object* v_original_2468_, lean_object* v___x_2469_, lean_object* v_edited_2470_, lean_object* v_as_2471_, lean_object* v_sz_2472_, lean_object* v_i_2473_, lean_object* v_b_2474_){
_start:
{
size_t v_sz_boxed_2475_; size_t v_i_boxed_2476_; lean_object* v_res_2477_; 
v_sz_boxed_2475_ = lean_unbox_usize(v_sz_2472_);
lean_dec(v_sz_2472_);
v_i_boxed_2476_ = lean_unbox_usize(v_i_2473_);
lean_dec(v_i_2473_);
v_res_2477_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v___x_2467_, v_original_2468_, v___x_2469_, v_edited_2470_, v_as_2471_, v_sz_boxed_2475_, v_i_boxed_2476_, v_b_2474_);
lean_dec_ref(v_as_2471_);
lean_dec_ref(v_edited_2470_);
lean_dec(v___x_2469_);
lean_dec_ref(v_original_2468_);
lean_dec(v___x_2467_);
return v_res_2477_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(lean_object* v___x_2478_, lean_object* v_edited_2479_, lean_object* v___x_2480_, lean_object* v_original_2481_, lean_object* v_as_2482_, size_t v_sz_2483_, size_t v_i_2484_, lean_object* v_b_2485_){
_start:
{
uint8_t v___x_2486_; 
v___x_2486_ = lean_usize_dec_lt(v_i_2484_, v_sz_2483_);
if (v___x_2486_ == 0)
{
return v_b_2485_;
}
else
{
lean_object* v_snd_2487_; lean_object* v_fst_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2535_; 
v_snd_2487_ = lean_ctor_get(v_b_2485_, 1);
v_fst_2488_ = lean_ctor_get(v_b_2485_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v_b_2485_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2490_ = v_b_2485_;
v_isShared_2491_ = v_isSharedCheck_2535_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_snd_2487_);
lean_inc(v_fst_2488_);
lean_dec(v_b_2485_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2535_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v_fst_2492_; lean_object* v_snd_2493_; lean_object* v___x_2495_; uint8_t v_isShared_2496_; uint8_t v_isSharedCheck_2534_; 
v_fst_2492_ = lean_ctor_get(v_snd_2487_, 0);
v_snd_2493_ = lean_ctor_get(v_snd_2487_, 1);
v_isSharedCheck_2534_ = !lean_is_exclusive(v_snd_2487_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2495_ = v_snd_2487_;
v_isShared_2496_ = v_isSharedCheck_2534_;
goto v_resetjp_2494_;
}
else
{
lean_inc(v_snd_2493_);
lean_inc(v_fst_2492_);
lean_dec(v_snd_2487_);
v___x_2495_ = lean_box(0);
v_isShared_2496_ = v_isSharedCheck_2534_;
goto v_resetjp_2494_;
}
v_resetjp_2494_:
{
lean_object* v_a_2497_; lean_object* v___x_2499_; 
v_a_2497_ = lean_array_uget_borrowed(v_as_2482_, v_i_2484_);
if (v_isShared_2496_ == 0)
{
lean_ctor_set(v___x_2495_, 1, v_fst_2492_);
lean_ctor_set(v___x_2495_, 0, v_fst_2488_);
v___x_2499_ = v___x_2495_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_fst_2488_);
lean_ctor_set(v_reuseFailAlloc_2533_, 1, v_fst_2492_);
v___x_2499_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
lean_object* v___x_2500_; lean_object* v_fst_2501_; lean_object* v_snd_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2532_; 
v___x_2500_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2480_, v_original_2481_, v_a_2497_, v___x_2499_);
v_fst_2501_ = lean_ctor_get(v___x_2500_, 0);
v_snd_2502_ = lean_ctor_get(v___x_2500_, 1);
v_isSharedCheck_2532_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2504_ = v___x_2500_;
v_isShared_2505_ = v_isSharedCheck_2532_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_snd_2502_);
lean_inc(v_fst_2501_);
lean_dec(v___x_2500_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2532_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 1, v_snd_2493_);
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_fst_2501_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_snd_2493_);
v___x_2507_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
lean_object* v___x_2508_; lean_object* v_fst_2509_; lean_object* v_snd_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2530_; 
v___x_2508_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2478_, v_edited_2479_, v_a_2497_, v___x_2507_);
v_fst_2509_ = lean_ctor_get(v___x_2508_, 0);
v_snd_2510_ = lean_ctor_get(v___x_2508_, 1);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2512_ = v___x_2508_;
v_isShared_2513_ = v_isSharedCheck_2530_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_snd_2510_);
lean_inc(v_fst_2509_);
lean_dec(v___x_2508_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2530_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
uint8_t v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2517_; 
v___x_2514_ = 2;
v___x_2515_ = lean_box(v___x_2514_);
lean_inc(v_a_2497_);
if (v_isShared_2513_ == 0)
{
lean_ctor_set(v___x_2512_, 1, v_a_2497_);
lean_ctor_set(v___x_2512_, 0, v___x_2515_);
v___x_2517_ = v___x_2512_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___x_2515_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v_a_2497_);
v___x_2517_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2523_; 
v___x_2518_ = lean_array_push(v_fst_2509_, v___x_2517_);
v___x_2519_ = lean_unsigned_to_nat(1u);
v___x_2520_ = lean_nat_add(v_snd_2502_, v___x_2519_);
lean_dec(v_snd_2502_);
v___x_2521_ = lean_nat_add(v_snd_2510_, v___x_2519_);
lean_dec(v_snd_2510_);
if (v_isShared_2491_ == 0)
{
lean_ctor_set(v___x_2490_, 1, v___x_2521_);
lean_ctor_set(v___x_2490_, 0, v___x_2520_);
v___x_2523_ = v___x_2490_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v___x_2520_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v___x_2521_);
v___x_2523_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
lean_object* v___x_2524_; size_t v___x_2525_; size_t v___x_2526_; lean_object* v___x_2527_; 
v___x_2524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2518_);
lean_ctor_set(v___x_2524_, 1, v___x_2523_);
v___x_2525_ = ((size_t)1ULL);
v___x_2526_ = lean_usize_add(v_i_2484_, v___x_2525_);
v___x_2527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_spec__14(v___x_2480_, v_original_2481_, v___x_2478_, v_edited_2479_, v_as_2482_, v_sz_2483_, v___x_2526_, v___x_2524_);
return v___x_2527_;
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2478_ = stack[0].m_obj;
lean_object* v_edited_2479_ = stack[1].m_obj;
lean_object* v___x_2480_ = stack[2].m_obj;
lean_object* v_original_2481_ = stack[3].m_obj;
lean_object* v_as_2482_ = stack[4].m_obj;
size_t v_sz_2483_ = stack[5].m_num;
size_t v_i_2484_ = stack[6].m_num;
lean_object* v_b_2485_ = stack[7].m_obj;
lean_object* v_res_2536_;
v_res_2536_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v___x_2478_, v_edited_2479_, v___x_2480_, v_original_2481_, v_as_2482_, v_sz_2483_, v_i_2484_, v_b_2485_);
stack->m_obj
 = v_res_2536_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4___boxed(lean_object* v___x_2537_, lean_object* v_edited_2538_, lean_object* v___x_2539_, lean_object* v_original_2540_, lean_object* v_as_2541_, lean_object* v_sz_2542_, lean_object* v_i_2543_, lean_object* v_b_2544_){
_start:
{
size_t v_sz_boxed_2545_; size_t v_i_boxed_2546_; lean_object* v_res_2547_; 
v_sz_boxed_2545_ = lean_unbox_usize(v_sz_2542_);
lean_dec(v_sz_2542_);
v_i_boxed_2546_ = lean_unbox_usize(v_i_2543_);
lean_dec(v_i_2543_);
v_res_2547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v___x_2537_, v_edited_2538_, v___x_2539_, v_original_2540_, v_as_2541_, v_sz_boxed_2545_, v_i_boxed_2546_, v_b_2544_);
lean_dec_ref(v_as_2541_);
lean_dec_ref(v_original_2540_);
lean_dec(v___x_2539_);
lean_dec_ref(v_edited_2538_);
lean_dec(v___x_2537_);
return v_res_2547_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(size_t v_sz_2548_, size_t v_i_2549_, lean_object* v_bs_2550_){
_start:
{
uint8_t v___x_2551_; 
v___x_2551_ = lean_usize_dec_lt(v_i_2549_, v_sz_2548_);
if (v___x_2551_ == 0)
{
return v_bs_2550_;
}
else
{
lean_object* v_v_2552_; lean_object* v___x_2553_; lean_object* v_bs_x27_2554_; uint8_t v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; size_t v___x_2558_; size_t v___x_2559_; lean_object* v___x_2560_; 
v_v_2552_ = lean_array_uget(v_bs_2550_, v_i_2549_);
v___x_2553_ = lean_unsigned_to_nat(0u);
v_bs_x27_2554_ = lean_array_uset(v_bs_2550_, v_i_2549_, v___x_2553_);
v___x_2555_ = 1;
v___x_2556_ = lean_box(v___x_2555_);
v___x_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2556_);
lean_ctor_set(v___x_2557_, 1, v_v_2552_);
v___x_2558_ = ((size_t)1ULL);
v___x_2559_ = lean_usize_add(v_i_2549_, v___x_2558_);
v___x_2560_ = lean_array_uset(v_bs_x27_2554_, v_i_2549_, v___x_2557_);
v_i_2549_ = v___x_2559_;
v_bs_2550_ = v___x_2560_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2548_ = stack[0].m_num;
size_t v_i_2549_ = stack[1].m_num;
lean_object* v_bs_2550_ = stack[2].m_obj;
lean_object* v_res_2562_;
v_res_2562_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_2548_, v_i_2549_, v_bs_2550_);
stack->m_obj
 = v_res_2562_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7___boxed(lean_object* v_sz_2563_, lean_object* v_i_2564_, lean_object* v_bs_2565_){
_start:
{
size_t v_sz_boxed_2566_; size_t v_i_boxed_2567_; lean_object* v_res_2568_; 
v_sz_boxed_2566_ = lean_unbox_usize(v_sz_2563_);
lean_dec(v_sz_2563_);
v_i_boxed_2567_ = lean_unbox_usize(v_i_2564_);
lean_dec(v_i_2564_);
v_res_2568_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_boxed_2566_, v_i_boxed_2567_, v_bs_2565_);
return v_res_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(lean_object* v_original_2574_, lean_object* v_edited_2575_){
_start:
{
lean_object* v_i_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; 
v_i_2576_ = lean_unsigned_to_nat(0u);
v___x_2577_ = lean_array_get_size(v_original_2574_);
v___x_2578_ = lean_nat_dec_lt(v_i_2576_, v___x_2577_);
if (v___x_2578_ == 0)
{
size_t v_sz_2579_; size_t v___x_2580_; lean_object* v___x_2581_; 
lean_dec_ref(v_original_2574_);
v_sz_2579_ = lean_array_size(v_edited_2575_);
v___x_2580_ = ((size_t)0ULL);
v___x_2581_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__8(v_sz_2579_, v___x_2580_, v_edited_2575_);
return v___x_2581_;
}
else
{
lean_object* v___x_2582_; uint8_t v___x_2583_; 
v___x_2582_ = lean_array_get_size(v_edited_2575_);
v___x_2583_ = lean_nat_dec_lt(v_i_2576_, v___x_2582_);
if (v___x_2583_ == 0)
{
size_t v_sz_2584_; size_t v___x_2585_; lean_object* v___x_2586_; 
lean_dec_ref(v_edited_2575_);
v_sz_2584_ = lean_array_size(v_original_2574_);
v___x_2585_ = ((size_t)0ULL);
v___x_2586_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__7(v_sz_2584_, v___x_2585_, v_original_2574_);
return v___x_2586_;
}
else
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v_ds_2589_; lean_object* v___x_2590_; size_t v_sz_2591_; size_t v___x_2592_; lean_object* v___x_2593_; lean_object* v_snd_2594_; lean_object* v_fst_2595_; lean_object* v_fst_2596_; lean_object* v_snd_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2616_; 
lean_inc_ref(v_original_2574_);
v___x_2587_ = l_Array_toSubarray___redArg(v_original_2574_, v_i_2576_, v___x_2577_);
lean_inc_ref(v_edited_2575_);
v___x_2588_ = l_Array_toSubarray___redArg(v_edited_2575_, v_i_2576_, v___x_2582_);
v_ds_2589_ = l_Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3(v___x_2587_, v___x_2588_);
v___x_2590_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1___closed__1));
v_sz_2591_ = lean_array_size(v_ds_2589_);
v___x_2592_ = ((size_t)0ULL);
v___x_2593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__4(v___x_2582_, v_edited_2575_, v___x_2577_, v_original_2574_, v_ds_2589_, v_sz_2591_, v___x_2592_, v___x_2590_);
lean_dec_ref(v_ds_2589_);
v_snd_2594_ = lean_ctor_get(v___x_2593_, 1);
lean_inc(v_snd_2594_);
v_fst_2595_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_fst_2595_);
lean_dec_ref(v___x_2593_);
v_fst_2596_ = lean_ctor_get(v_snd_2594_, 0);
v_snd_2597_ = lean_ctor_get(v_snd_2594_, 1);
v_isSharedCheck_2616_ = !lean_is_exclusive(v_snd_2594_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2599_ = v_snd_2594_;
v_isShared_2600_ = v_isSharedCheck_2616_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_snd_2597_);
lean_inc(v_fst_2596_);
lean_dec(v_snd_2594_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2616_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 1, v_fst_2596_);
lean_ctor_set(v___x_2599_, 0, v_fst_2595_);
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_fst_2595_);
lean_ctor_set(v_reuseFailAlloc_2615_, 1, v_fst_2596_);
v___x_2602_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
lean_object* v___x_2603_; lean_object* v_fst_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2613_; 
v___x_2603_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2577_, v_original_2574_, v___x_2602_);
lean_dec_ref(v_original_2574_);
v_fst_2604_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2613_ == 0)
{
lean_object* v_unused_2614_; 
v_unused_2614_ = lean_ctor_get(v___x_2603_, 1);
lean_dec(v_unused_2614_);
v___x_2606_ = v___x_2603_;
v_isShared_2607_ = v_isSharedCheck_2613_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_fst_2604_);
lean_dec(v___x_2603_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2613_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v___x_2609_; 
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 1, v_snd_2597_);
v___x_2609_ = v___x_2606_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_fst_2604_);
lean_ctor_set(v_reuseFailAlloc_2612_, 1, v_snd_2597_);
v___x_2609_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
lean_object* v___x_2610_; lean_object* v_fst_2611_; 
v___x_2610_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2582_, v_edited_2575_, v___x_2609_);
lean_dec_ref(v_edited_2575_);
v_fst_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_fst_2611_);
lean_dec_ref(v___x_2610_);
return v_fst_2611_;
}
}
}
}
}
}
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(lean_object* v___x_2617_, uint8_t v_inSubst_2618_, lean_object* v___x_2619_, lean_object* v_____r_2620_, lean_object* v_wssIdx_2621_){
_start:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
v___x_2622_ = lean_box(v_inSubst_2618_);
v___x_2623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2617_);
lean_ctor_set(v___x_2623_, 1, v___x_2622_);
v___x_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2624_, 0, v_wssIdx_2621_);
lean_ctor_set(v___x_2624_, 1, v___x_2623_);
v___x_2625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2625_, 0, v___x_2619_);
lean_ctor_set(v___x_2625_, 1, v___x_2624_);
v___x_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
return v___x_2626_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2617_ = stack[0].m_obj;
uint8_t v_inSubst_2618_ = stack[1].m_num;
lean_object* v___x_2619_ = stack[2].m_obj;
lean_object* v_____r_2620_ = stack[3].m_obj;
lean_object* v_wssIdx_2621_ = stack[4].m_obj;
lean_object* v_res_2627_;
v_res_2627_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2617_, v_inSubst_2618_, v___x_2619_, v_____r_2620_, v_wssIdx_2621_);
stack->m_obj
 = v_res_2627_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1___boxed(lean_object* v___x_2628_, lean_object* v_inSubst_2629_, lean_object* v___x_2630_, lean_object* v_____r_2631_, lean_object* v_wssIdx_2632_){
_start:
{
uint8_t v_inSubst_boxed_2633_; lean_object* v_res_2634_; 
v_inSubst_boxed_2633_ = lean_unbox(v_inSubst_2629_);
v_res_2634_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2628_, v_inSubst_boxed_2633_, v___x_2630_, v_____r_2631_, v_wssIdx_2632_);
return v_res_2634_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(lean_object* v_fst_2635_, uint8_t v___x_2636_, lean_object* v_fst_2637_, lean_object* v___x_2638_, lean_object* v_00___2639_){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2640_ = lean_box(v___x_2636_);
v___x_2641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2641_, 0, v_fst_2635_);
lean_ctor_set(v___x_2641_, 1, v___x_2640_);
v___x_2642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2642_, 0, v_fst_2637_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
v___x_2643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2638_);
lean_ctor_set(v___x_2643_, 1, v___x_2642_);
v___x_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2643_);
return v___x_2644_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_2635_ = stack[0].m_obj;
uint8_t v___x_2636_ = stack[1].m_num;
lean_object* v_fst_2637_ = stack[2].m_obj;
lean_object* v___x_2638_ = stack[3].m_obj;
lean_object* v_00___2639_ = stack[4].m_obj;
lean_object* v_res_2645_;
v_res_2645_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2635_, v___x_2636_, v_fst_2637_, v___x_2638_, v_00___2639_);
stack->m_obj
 = v_res_2645_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0___boxed(lean_object* v_fst_2646_, lean_object* v___x_2647_, lean_object* v_fst_2648_, lean_object* v___x_2649_, lean_object* v_00___2650_){
_start:
{
uint8_t v___x_9824__boxed_2651_; lean_object* v_res_2652_; 
v___x_9824__boxed_2651_ = lean_unbox(v___x_2647_);
v_res_2652_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2646_, v___x_9824__boxed_2651_, v_fst_2648_, v___x_2649_, v_00___2650_);
return v_res_2652_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(uint8_t v_inSubst_2653_, lean_object* v_snd_2654_, lean_object* v_fst_2655_, lean_object* v_____r_2656_, lean_object* v_withWs_2657_, lean_object* v_wssIdx_2658_){
_start:
{
lean_object* v_wss_x27Idx_2660_; uint8_t v___x_2666_; 
v___x_2666_ = lean_unbox(v_snd_2654_);
if (v___x_2666_ == 0)
{
v_wss_x27Idx_2660_ = v_fst_2655_;
goto v___jp_2659_;
}
else
{
lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2667_ = lean_unsigned_to_nat(1u);
v___x_2668_ = lean_nat_add(v_fst_2655_, v___x_2667_);
lean_dec(v_fst_2655_);
v_wss_x27Idx_2660_ = v___x_2668_;
goto v___jp_2659_;
}
v___jp_2659_:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2661_ = lean_box(v_inSubst_2653_);
v___x_2662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2662_, 0, v_wss_x27Idx_2660_);
lean_ctor_set(v___x_2662_, 1, v___x_2661_);
v___x_2663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2663_, 0, v_wssIdx_2658_);
lean_ctor_set(v___x_2663_, 1, v___x_2662_);
v___x_2664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2664_, 0, v_withWs_2657_);
lean_ctor_set(v___x_2664_, 1, v___x_2663_);
v___x_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2665_, 0, v___x_2664_);
return v___x_2665_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v_inSubst_2653_ = stack[0].m_num;
lean_object* v_snd_2654_ = stack[1].m_obj;
lean_object* v_fst_2655_ = stack[2].m_obj;
lean_object* v_____r_2656_ = stack[3].m_obj;
lean_object* v_withWs_2657_ = stack[4].m_obj;
lean_object* v_wssIdx_2658_ = stack[5].m_obj;
lean_object* v_res_2669_;
v_res_2669_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2653_, v_snd_2654_, v_fst_2655_, v_____r_2656_, v_withWs_2657_, v_wssIdx_2658_);
stack->m_obj
 = v_res_2669_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2___boxed(lean_object* v_inSubst_2670_, lean_object* v_snd_2671_, lean_object* v_fst_2672_, lean_object* v_____r_2673_, lean_object* v_withWs_2674_, lean_object* v_wssIdx_2675_){
_start:
{
uint8_t v_inSubst_boxed_2676_; lean_object* v_res_2677_; 
v_inSubst_boxed_2676_ = lean_unbox(v_inSubst_2670_);
v_res_2677_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_boxed_2676_, v_snd_2671_, v_fst_2672_, v_____r_2673_, v_withWs_2674_, v_wssIdx_2675_);
lean_dec(v_snd_2671_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(lean_object* v_upperBound_2678_, lean_object* v_diff_2679_, lean_object* v_snd_2680_, lean_object* v_snd_2681_, lean_object* v_a_2682_, lean_object* v_b_2683_){
_start:
{
lean_object* v_a_2685_; lean_object* v___y_2690_; uint8_t v___x_2693_; 
v___x_2693_ = lean_nat_dec_lt(v_a_2682_, v_upperBound_2678_);
if (v___x_2693_ == 0)
{
lean_dec(v_a_2682_);
return v_b_2683_;
}
else
{
lean_object* v___x_2694_; lean_object* v_snd_2695_; lean_object* v_snd_2696_; lean_object* v_fst_2697_; lean_object* v_fst_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2838_; 
v___x_2694_ = lean_array_fget_borrowed(v_diff_2679_, v_a_2682_);
v_snd_2695_ = lean_ctor_get(v_b_2683_, 1);
lean_inc(v_snd_2695_);
v_snd_2696_ = lean_ctor_get(v_snd_2695_, 1);
lean_inc(v_snd_2696_);
v_fst_2697_ = lean_ctor_get(v___x_2694_, 0);
v_fst_2698_ = lean_ctor_get(v_b_2683_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v_b_2683_);
if (v_isSharedCheck_2838_ == 0)
{
lean_object* v_unused_2839_; 
v_unused_2839_ = lean_ctor_get(v_b_2683_, 1);
lean_dec(v_unused_2839_);
v___x_2700_ = v_b_2683_;
v_isShared_2701_ = v_isSharedCheck_2838_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_fst_2698_);
lean_dec(v_b_2683_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2838_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v_fst_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2836_; 
v_fst_2702_ = lean_ctor_get(v_snd_2695_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v_snd_2695_);
if (v_isSharedCheck_2836_ == 0)
{
lean_object* v_unused_2837_; 
v_unused_2837_ = lean_ctor_get(v_snd_2695_, 1);
lean_dec(v_unused_2837_);
v___x_2704_ = v_snd_2695_;
v_isShared_2705_ = v_isSharedCheck_2836_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_fst_2702_);
lean_dec(v_snd_2695_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2836_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v_fst_2706_; lean_object* v_snd_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2835_; 
v_fst_2706_ = lean_ctor_get(v_snd_2696_, 0);
v_snd_2707_ = lean_ctor_get(v_snd_2696_, 1);
v_isSharedCheck_2835_ = !lean_is_exclusive(v_snd_2696_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2709_ = v_snd_2696_;
v_isShared_2710_ = v_isSharedCheck_2835_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_snd_2707_);
lean_inc(v_fst_2706_);
lean_dec(v_snd_2696_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2835_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2711_; lean_object* v___y_2713_; lean_object* v___y_2728_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; uint8_t v___x_2739_; 
lean_inc(v___x_2694_);
v___x_2711_ = lean_array_push(v_fst_2698_, v___x_2694_);
v___x_2736_ = lean_unsigned_to_nat(1u);
v___x_2737_ = lean_nat_add(v_a_2682_, v___x_2736_);
v___x_2738_ = lean_array_get_size(v_diff_2679_);
v___x_2739_ = lean_nat_dec_lt(v___x_2737_, v___x_2738_);
if (v___x_2739_ == 0)
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
lean_dec(v___x_2737_);
lean_del_object(v___x_2709_);
lean_del_object(v___x_2704_);
lean_del_object(v___x_2700_);
v___x_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2740_, 0, v_fst_2706_);
lean_ctor_set(v___x_2740_, 1, v_snd_2707_);
v___x_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2741_, 0, v_fst_2702_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v___x_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2711_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v_a_2685_ = v___x_2742_;
goto v___jp_2684_;
}
else
{
lean_object* v___x_2743_; lean_object* v_fst_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2833_; 
v___x_2743_ = lean_array_fget(v_diff_2679_, v___x_2737_);
lean_dec(v___x_2737_);
v_fst_2744_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2833_ == 0)
{
lean_object* v_unused_2834_; 
v_unused_2834_ = lean_ctor_get(v___x_2743_, 1);
lean_dec(v_unused_2834_);
v___x_2746_ = v___x_2743_;
v_isShared_2747_ = v_isSharedCheck_2833_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_fst_2744_);
lean_dec(v___x_2743_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2833_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
uint8_t v_inSubst_2748_; lean_object* v___y_2750_; lean_object* v___x_2759_; uint8_t v___x_2760_; 
v_inSubst_2748_ = 0;
v___x_2759_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_2760_ = lean_unbox(v_fst_2697_);
switch(v___x_2760_)
{
case 0:
{
uint8_t v___x_2761_; 
lean_del_object(v___x_2709_);
lean_del_object(v___x_2704_);
lean_del_object(v___x_2700_);
v___x_2761_ = lean_unbox(v_fst_2744_);
switch(v___x_2761_)
{
case 0:
{
lean_object* v___x_2762_; lean_object* v___x_2764_; 
v___x_2762_ = lean_array_get_borrowed(v___x_2759_, v_snd_2680_, v_fst_2706_);
lean_inc(v___x_2762_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 1, v___x_2762_);
v___x_2764_ = v___x_2746_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_fst_2744_);
lean_ctor_set(v_reuseFailAlloc_2770_, 1, v___x_2762_);
v___x_2764_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2765_ = lean_array_push(v___x_2711_, v___x_2764_);
v___x_2766_ = lean_nat_add(v_fst_2706_, v___x_2736_);
lean_dec(v_fst_2706_);
v___x_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2767_, 0, v___x_2766_);
lean_ctor_set(v___x_2767_, 1, v_snd_2707_);
v___x_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2768_, 0, v_fst_2702_);
lean_ctor_set(v___x_2768_, 1, v___x_2767_);
v___x_2769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2765_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
v_a_2685_ = v___x_2769_;
goto v___jp_2684_;
}
}
case 1:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
lean_del_object(v___x_2746_);
lean_dec(v_fst_2744_);
lean_dec(v_snd_2707_);
v___x_2771_ = lean_box(0);
v___x_2772_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2706_, v___x_2693_, v_fst_2702_, v___x_2711_, v___x_2771_);
v___y_2690_ = v___x_2772_;
goto v___jp_2689_;
}
default: 
{
lean_object* v___x_2773_; uint8_t v___x_2774_; 
lean_dec(v_fst_2744_);
v___x_2773_ = lean_array_get_borrowed(v___x_2759_, v_snd_2680_, v_fst_2706_);
v___x_2774_ = lean_unbox(v_snd_2707_);
if (v___x_2774_ == 0)
{
lean_object* v___x_2776_; 
lean_inc(v___x_2773_);
lean_inc(v_fst_2697_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 1, v___x_2773_);
lean_ctor_set(v___x_2746_, 0, v_fst_2697_);
v___x_2776_ = v___x_2746_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_fst_2697_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v___x_2773_);
v___x_2776_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2777_ = lean_mk_empty_array_with_capacity(v___x_2736_);
v___x_2778_ = lean_array_push(v___x_2777_, v___x_2776_);
v___y_2750_ = v___x_2778_;
goto v___jp_2749_;
}
}
else
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
lean_del_object(v___x_2746_);
v___x_2780_ = lean_array_get_borrowed(v___x_2759_, v_snd_2681_, v_fst_2702_);
lean_inc(v___x_2773_);
lean_inc(v___x_2780_);
v___x_2781_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2780_, v___x_2773_);
v___y_2750_ = v___x_2781_;
goto v___jp_2749_;
}
}
}
}
case 1:
{
uint8_t v___x_2782_; 
lean_del_object(v___x_2709_);
lean_del_object(v___x_2704_);
lean_del_object(v___x_2700_);
v___x_2782_ = lean_unbox(v_fst_2744_);
switch(v___x_2782_)
{
case 0:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
lean_del_object(v___x_2746_);
lean_dec(v_fst_2744_);
lean_dec(v_snd_2707_);
v___x_2783_ = lean_box(0);
v___x_2784_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__0(v_fst_2706_, v___x_2693_, v_fst_2702_, v___x_2711_, v___x_2783_);
v___y_2690_ = v___x_2784_;
goto v___jp_2689_;
}
case 1:
{
lean_object* v___x_2785_; lean_object* v___x_2787_; 
v___x_2785_ = lean_array_get_borrowed(v___x_2759_, v_snd_2681_, v_fst_2702_);
lean_inc(v___x_2785_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 1, v___x_2785_);
v___x_2787_ = v___x_2746_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_fst_2744_);
lean_ctor_set(v_reuseFailAlloc_2793_, 1, v___x_2785_);
v___x_2787_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2788_ = lean_array_push(v___x_2711_, v___x_2787_);
v___x_2789_ = lean_nat_add(v_fst_2702_, v___x_2736_);
lean_dec(v_fst_2702_);
v___x_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2790_, 0, v_fst_2706_);
lean_ctor_set(v___x_2790_, 1, v_snd_2707_);
v___x_2791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2789_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
v___x_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2788_);
lean_ctor_set(v___x_2792_, 1, v___x_2791_);
v_a_2685_ = v___x_2792_;
goto v___jp_2684_;
}
}
default: 
{
uint8_t v___x_2797_; 
lean_dec(v_fst_2744_);
v___x_2797_ = lean_unbox(v_snd_2707_);
if (v___x_2797_ == 0)
{
lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; uint8_t v___x_2802_; 
v___x_2798_ = lean_array_get_borrowed(v___x_2759_, v_snd_2681_, v_fst_2702_);
v___x_2799_ = lean_unsigned_to_nat(0u);
v___x_2800_ = lean_string_utf8_byte_size(v___x_2798_);
lean_inc(v___x_2798_);
v___x_2801_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2798_);
lean_ctor_set(v___x_2801_, 1, v___x_2799_);
lean_ctor_set(v___x_2801_, 2, v___x_2800_);
v___x_2802_ = l_String_Slice_contains___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__0(v___x_2801_);
lean_dec_ref_known(v___x_2801_, 3);
if (v___x_2802_ == 0)
{
lean_object* v___x_2804_; 
lean_inc(v___x_2798_);
lean_inc(v_fst_2697_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 1, v___x_2798_);
lean_ctor_set(v___x_2746_, 0, v_fst_2697_);
v___x_2804_ = v___x_2746_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_fst_2697_);
lean_ctor_set(v_reuseFailAlloc_2809_, 1, v___x_2798_);
v___x_2804_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v___x_2805_ = lean_array_push(v___x_2711_, v___x_2804_);
v___x_2806_ = lean_nat_add(v_fst_2702_, v___x_2736_);
lean_dec(v_fst_2702_);
v___x_2807_ = lean_box(0);
v___x_2808_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2748_, v_snd_2707_, v_fst_2706_, v___x_2807_, v___x_2805_, v___x_2806_);
lean_dec(v_snd_2707_);
v___y_2690_ = v___x_2808_;
goto v___jp_2689_;
}
}
else
{
lean_del_object(v___x_2746_);
goto v___jp_2794_;
}
}
else
{
lean_del_object(v___x_2746_);
goto v___jp_2794_;
}
v___jp_2794_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2795_ = lean_box(0);
v___x_2796_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__2(v_inSubst_2748_, v_snd_2707_, v_fst_2706_, v___x_2795_, v___x_2711_, v_fst_2702_);
lean_dec(v_snd_2707_);
v___y_2690_ = v___x_2796_;
goto v___jp_2689_;
}
}
}
}
default: 
{
uint8_t v___x_2810_; 
v___x_2810_ = lean_unbox(v_fst_2744_);
if (v___x_2810_ == 1)
{
lean_object* v___x_2811_; lean_object* v___x_2812_; uint8_t v___x_2813_; 
v___x_2811_ = lean_array_get_borrowed(v___x_2759_, v_snd_2681_, v_fst_2702_);
v___x_2812_ = lean_array_get_size(v_snd_2680_);
v___x_2813_ = lean_nat_dec_lt(v_fst_2706_, v___x_2812_);
if (v___x_2813_ == 0)
{
lean_object* v___x_2815_; 
lean_inc(v___x_2811_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 1, v___x_2811_);
v___x_2815_ = v___x_2746_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_fst_2744_);
lean_ctor_set(v_reuseFailAlloc_2818_, 1, v___x_2811_);
v___x_2815_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2816_ = lean_mk_empty_array_with_capacity(v___x_2736_);
v___x_2817_ = lean_array_push(v___x_2816_, v___x_2815_);
v___y_2713_ = v___x_2817_;
goto v___jp_2712_;
}
}
else
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
lean_del_object(v___x_2746_);
lean_dec(v_fst_2744_);
v___x_2819_ = lean_array_fget_borrowed(v_snd_2680_, v_fst_2706_);
lean_inc(v___x_2819_);
lean_inc(v___x_2811_);
v___x_2820_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2811_, v___x_2819_);
v___y_2713_ = v___x_2820_;
goto v___jp_2712_;
}
}
else
{
lean_object* v___x_2821_; lean_object* v___x_2822_; uint8_t v___x_2823_; 
lean_dec(v_fst_2744_);
lean_del_object(v___x_2709_);
lean_del_object(v___x_2704_);
lean_del_object(v___x_2700_);
v___x_2821_ = lean_array_get_borrowed(v___x_2759_, v_snd_2680_, v_fst_2706_);
v___x_2822_ = lean_array_get_size(v_snd_2681_);
v___x_2823_ = lean_nat_dec_lt(v_fst_2702_, v___x_2822_);
if (v___x_2823_ == 0)
{
uint8_t v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2827_; 
v___x_2824_ = 0;
v___x_2825_ = lean_box(v___x_2824_);
lean_inc(v___x_2821_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 1, v___x_2821_);
lean_ctor_set(v___x_2746_, 0, v___x_2825_);
v___x_2827_ = v___x_2746_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2825_);
lean_ctor_set(v_reuseFailAlloc_2830_, 1, v___x_2821_);
v___x_2827_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = lean_mk_empty_array_with_capacity(v___x_2736_);
v___x_2829_ = lean_array_push(v___x_2828_, v___x_2827_);
v___y_2728_ = v___x_2829_;
goto v___jp_2727_;
}
}
else
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
lean_del_object(v___x_2746_);
v___x_2831_ = lean_array_fget_borrowed(v_snd_2681_, v_fst_2702_);
lean_inc(v___x_2821_);
lean_inc(v___x_2831_);
v___x_2832_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff(v___x_2831_, v___x_2821_);
v___y_2728_ = v___x_2832_;
goto v___jp_2727_;
}
}
}
}
v___jp_2749_:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; uint8_t v___x_2753_; 
v___x_2751_ = l_Array_append___redArg(v___x_2711_, v___y_2750_);
lean_dec_ref(v___y_2750_);
v___x_2752_ = lean_nat_add(v_fst_2706_, v___x_2736_);
lean_dec(v_fst_2706_);
v___x_2753_ = lean_unbox(v_snd_2707_);
lean_dec(v_snd_2707_);
if (v___x_2753_ == 0)
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2754_ = lean_box(0);
v___x_2755_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2752_, v_inSubst_2748_, v___x_2751_, v___x_2754_, v_fst_2702_);
v___y_2690_ = v___x_2755_;
goto v___jp_2689_;
}
else
{
lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2756_ = lean_nat_add(v_fst_2702_, v___x_2736_);
lean_dec(v_fst_2702_);
v___x_2757_ = lean_box(0);
v___x_2758_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___lam__1(v___x_2752_, v_inSubst_2748_, v___x_2751_, v___x_2757_, v___x_2756_);
v___y_2690_ = v___x_2758_;
goto v___jp_2689_;
}
}
}
}
v___jp_2712_:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2719_; 
v___x_2714_ = l_Array_append___redArg(v___x_2711_, v___y_2713_);
lean_dec_ref(v___y_2713_);
v___x_2715_ = lean_unsigned_to_nat(1u);
v___x_2716_ = lean_nat_add(v_fst_2702_, v___x_2715_);
lean_dec(v_fst_2702_);
v___x_2717_ = lean_nat_add(v_fst_2706_, v___x_2715_);
lean_dec(v_fst_2706_);
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 0, v___x_2717_);
v___x_2719_ = v___x_2709_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2717_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v_snd_2707_);
v___x_2719_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
lean_object* v___x_2721_; 
if (v_isShared_2705_ == 0)
{
lean_ctor_set(v___x_2704_, 1, v___x_2719_);
lean_ctor_set(v___x_2704_, 0, v___x_2716_);
v___x_2721_ = v___x_2704_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2716_);
lean_ctor_set(v_reuseFailAlloc_2725_, 1, v___x_2719_);
v___x_2721_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
lean_object* v___x_2723_; 
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 1, v___x_2721_);
lean_ctor_set(v___x_2700_, 0, v___x_2714_);
v___x_2723_ = v___x_2700_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2714_);
lean_ctor_set(v_reuseFailAlloc_2724_, 1, v___x_2721_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
v_a_2685_ = v___x_2723_;
goto v___jp_2684_;
}
}
}
}
v___jp_2727_:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2729_ = l_Array_append___redArg(v___x_2711_, v___y_2728_);
lean_dec_ref(v___y_2728_);
v___x_2730_ = lean_unsigned_to_nat(1u);
v___x_2731_ = lean_nat_add(v_fst_2702_, v___x_2730_);
lean_dec(v_fst_2702_);
v___x_2732_ = lean_nat_add(v_fst_2706_, v___x_2730_);
lean_dec(v_fst_2706_);
v___x_2733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2733_, 0, v___x_2732_);
lean_ctor_set(v___x_2733_, 1, v_snd_2707_);
v___x_2734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2734_, 0, v___x_2731_);
lean_ctor_set(v___x_2734_, 1, v___x_2733_);
v___x_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2729_);
lean_ctor_set(v___x_2735_, 1, v___x_2734_);
v_a_2685_ = v___x_2735_;
goto v___jp_2684_;
}
}
}
}
}
v___jp_2684_:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2686_ = lean_unsigned_to_nat(1u);
v___x_2687_ = lean_nat_add(v_a_2682_, v___x_2686_);
lean_dec(v_a_2682_);
v_a_2682_ = v___x_2687_;
v_b_2683_ = v_a_2685_;
goto _start;
}
v___jp_2689_:
{
if (lean_obj_tag(v___y_2690_) == 0)
{
lean_object* v_a_2691_; 
lean_dec(v_a_2682_);
v_a_2691_ = lean_ctor_get(v___y_2690_, 0);
lean_inc(v_a_2691_);
lean_dec_ref_known(v___y_2690_, 1);
return v_a_2691_;
}
else
{
lean_object* v_a_2692_; 
v_a_2692_ = lean_ctor_get(v___y_2690_, 0);
lean_inc(v_a_2692_);
lean_dec_ref_known(v___y_2690_, 1);
v_a_2685_ = v_a_2692_;
goto v___jp_2684_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg___boxed(lean_object* v_upperBound_2840_, lean_object* v_diff_2841_, lean_object* v_snd_2842_, lean_object* v_snd_2843_, lean_object* v_a_2844_, lean_object* v_b_2845_){
_start:
{
lean_object* v_res_2846_; 
v_res_2846_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2840_, v_diff_2841_, v_snd_2842_, v_snd_2843_, v_a_2844_, v_b_2845_);
lean_dec_ref(v_snd_2843_);
lean_dec_ref(v_snd_2842_);
lean_dec_ref(v_diff_2841_);
lean_dec(v_upperBound_2840_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(lean_object* v_s_2857_, lean_object* v_s_x27_2858_){
_start:
{
lean_object* v___x_2859_; lean_object* v_fst_2860_; lean_object* v_snd_2861_; lean_object* v___x_2862_; lean_object* v_fst_2863_; lean_object* v_snd_2864_; lean_object* v_diff_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v_fst_2870_; lean_object* v___x_2871_; size_t v_sz_2872_; size_t v___x_2873_; lean_object* v___x_2874_; 
v___x_2859_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_2857_);
v_fst_2860_ = lean_ctor_get(v___x_2859_, 0);
lean_inc(v_fst_2860_);
v_snd_2861_ = lean_ctor_get(v___x_2859_, 1);
lean_inc(v_snd_2861_);
lean_dec_ref(v___x_2859_);
v___x_2862_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitWords(v_s_x27_2858_);
v_fst_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_fst_2863_);
v_snd_2864_ = lean_ctor_get(v___x_2862_, 1);
lean_inc(v_snd_2864_);
lean_dec_ref(v___x_2862_);
v_diff_2865_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1(v_fst_2860_, v_fst_2863_);
v___x_2866_ = lean_unsigned_to_nat(0u);
v___x_2867_ = lean_array_get_size(v_diff_2865_);
v___x_2868_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___closed__2));
v___x_2869_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v___x_2867_, v_diff_2865_, v_snd_2864_, v_snd_2861_, v___x_2866_, v___x_2868_);
lean_dec(v_snd_2861_);
lean_dec(v_snd_2864_);
lean_dec_ref(v_diff_2865_);
v_fst_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_fst_2870_);
lean_dec_ref(v___x_2869_);
v___x_2871_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v_fst_2870_);
lean_dec(v_fst_2870_);
v_sz_2872_ = lean_array_size(v___x_2871_);
v___x_2873_ = ((size_t)0ULL);
v___x_2874_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__0(v_sz_2872_, v___x_2873_, v___x_2871_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff___boxed(lean_object* v_s_2875_, lean_object* v_s_x27_2876_){
_start:
{
lean_object* v_res_2877_; 
v_res_2877_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_2875_, v_s_x27_2876_);
lean_dec_ref(v_s_x27_2876_);
lean_dec_ref(v_s_2875_);
return v_res_2877_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(lean_object* v_upperBound_2878_, lean_object* v_diff_2879_, lean_object* v_snd_2880_, lean_object* v_snd_2881_, lean_object* v_inst_2882_, lean_object* v_R_2883_, lean_object* v_a_2884_, lean_object* v_b_2885_, lean_object* v_c_2886_){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___redArg(v_upperBound_2878_, v_diff_2879_, v_snd_2880_, v_snd_2881_, v_a_2884_, v_b_2885_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2___boxed(lean_object* v_upperBound_2888_, lean_object* v_diff_2889_, lean_object* v_snd_2890_, lean_object* v_snd_2891_, lean_object* v_inst_2892_, lean_object* v_R_2893_, lean_object* v_a_2894_, lean_object* v_b_2895_, lean_object* v_c_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__2(v_upperBound_2888_, v_diff_2889_, v_snd_2890_, v_snd_2891_, v_inst_2892_, v_R_2893_, v_a_2894_, v_b_2895_, v_c_2896_);
lean_dec_ref(v_snd_2891_);
lean_dec_ref(v_snd_2890_);
lean_dec_ref(v_diff_2889_);
lean_dec(v_upperBound_2888_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(lean_object* v___x_2898_, lean_object* v_original_2899_, lean_object* v_a_2900_, lean_object* v_inst_2901_, lean_object* v_a_2902_){
_start:
{
lean_object* v___x_2903_; 
v___x_2903_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___redArg(v___x_2898_, v_original_2899_, v_a_2900_, v_a_2902_);
return v___x_2903_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1___boxed(lean_object* v___x_2904_, lean_object* v_original_2905_, lean_object* v_a_2906_, lean_object* v_inst_2907_, lean_object* v_a_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__1(v___x_2904_, v_original_2905_, v_a_2906_, v_inst_2907_, v_a_2908_);
lean_dec_ref(v_a_2906_);
lean_dec_ref(v_original_2905_);
lean_dec(v___x_2904_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(lean_object* v___x_2910_, lean_object* v_edited_2911_, lean_object* v_a_2912_, lean_object* v_inst_2913_, lean_object* v_a_2914_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___redArg(v___x_2910_, v_edited_2911_, v_a_2912_, v_a_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2___boxed(lean_object* v___x_2916_, lean_object* v_edited_2917_, lean_object* v_a_2918_, lean_object* v_inst_2919_, lean_object* v_a_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__2(v___x_2916_, v_edited_2917_, v_a_2918_, v_inst_2919_, v_a_2920_);
lean_dec_ref(v_a_2918_);
lean_dec_ref(v_edited_2917_);
lean_dec(v___x_2916_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(lean_object* v___x_2922_, lean_object* v_original_2923_, lean_object* v_inst_2924_, lean_object* v_a_2925_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___redArg(v___x_2922_, v_original_2923_, v_a_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5___boxed(lean_object* v___x_2927_, lean_object* v_original_2928_, lean_object* v_inst_2929_, lean_object* v_a_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__5(v___x_2927_, v_original_2928_, v_inst_2929_, v_a_2930_);
lean_dec_ref(v_original_2928_);
lean_dec(v___x_2927_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(lean_object* v___x_2932_, lean_object* v_edited_2933_, lean_object* v_inst_2934_, lean_object* v_a_2935_){
_start:
{
lean_object* v___x_2936_; 
v___x_2936_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___redArg(v___x_2932_, v_edited_2933_, v_a_2935_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6___boxed(lean_object* v___x_2937_, lean_object* v_edited_2938_, lean_object* v_inst_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__6(v___x_2937_, v_edited_2938_, v_inst_2939_, v_a_2940_);
lean_dec_ref(v_edited_2938_);
lean_dec(v___x_2937_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6(lean_object* v_as_2942_, lean_object* v_as_x27_2943_, lean_object* v_b_2944_, lean_object* v_a_2945_){
_start:
{
lean_object* v___x_2946_; 
v___x_2946_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___redArg(v_as_x27_2943_, v_b_2944_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6___boxed(lean_object* v_as_2947_, lean_object* v_as_x27_2948_, lean_object* v_b_2949_, lean_object* v_a_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_List_forIn_x27_loop___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__6(v_as_2947_, v_as_x27_2948_, v_b_2949_, v_a_2950_);
lean_dec(v_as_x27_2948_);
lean_dec(v_as_2947_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9(lean_object* v_lsize_2952_, lean_object* v_rsize_2953_, lean_object* v_histogram_2954_, lean_object* v_index_2955_, lean_object* v_val_2956_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___redArg(v_histogram_2954_, v_index_2955_, v_val_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9___boxed(lean_object* v_lsize_2958_, lean_object* v_rsize_2959_, lean_object* v_histogram_2960_, lean_object* v_index_2961_, lean_object* v_val_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9(v_lsize_2958_, v_rsize_2959_, v_histogram_2960_, v_index_2961_, v_val_2962_);
lean_dec(v_rsize_2959_);
lean_dec(v_lsize_2958_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10(lean_object* v_upperBound_2964_, lean_object* v___x_2965_, lean_object* v_fst_2966_, lean_object* v___x_2967_, lean_object* v_inst_2968_, lean_object* v_R_2969_, lean_object* v_a_2970_, lean_object* v_b_2971_, lean_object* v_c_2972_){
_start:
{
lean_object* v___x_2973_; 
v___x_2973_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___redArg(v_upperBound_2964_, v___x_2965_, v_fst_2966_, v___x_2967_, v_a_2970_, v_b_2971_);
return v___x_2973_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10___boxed(lean_object* v_upperBound_2974_, lean_object* v___x_2975_, lean_object* v_fst_2976_, lean_object* v___x_2977_, lean_object* v_inst_2978_, lean_object* v_R_2979_, lean_object* v_a_2980_, lean_object* v_b_2981_, lean_object* v_c_2982_){
_start:
{
lean_object* v_res_2983_; 
v_res_2983_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__10(v_upperBound_2974_, v___x_2975_, v_fst_2976_, v___x_2977_, v_inst_2978_, v_R_2979_, v_a_2980_, v_b_2981_, v_c_2982_);
lean_dec(v___x_2977_);
lean_dec_ref(v_fst_2976_);
lean_dec(v___x_2975_);
lean_dec(v_upperBound_2974_);
return v_res_2983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11(lean_object* v_lsize_2984_, lean_object* v_rsize_2985_, lean_object* v_histogram_2986_, lean_object* v_index_2987_, lean_object* v_val_2988_){
_start:
{
lean_object* v___x_2989_; 
v___x_2989_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___redArg(v_histogram_2986_, v_index_2987_, v_val_2988_);
return v___x_2989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11___boxed(lean_object* v_lsize_2990_, lean_object* v_rsize_2991_, lean_object* v_histogram_2992_, lean_object* v_index_2993_, lean_object* v_val_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Lean_Diff_Histogram_addLeft___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__11(v_lsize_2990_, v_rsize_2991_, v_histogram_2992_, v_index_2993_, v_val_2994_);
lean_dec(v_rsize_2991_);
lean_dec(v_lsize_2990_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12(lean_object* v_upperBound_2996_, lean_object* v_fst_2997_, lean_object* v___x_2998_, lean_object* v_fst_2999_, lean_object* v_inst_3000_, lean_object* v_R_3001_, lean_object* v_a_3002_, lean_object* v_b_3003_, lean_object* v_c_3004_){
_start:
{
lean_object* v___x_3005_; 
v___x_3005_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___redArg(v_upperBound_2996_, v_fst_2997_, v___x_2998_, v_fst_2999_, v_a_3002_, v_b_3003_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12___boxed(lean_object* v_upperBound_3006_, lean_object* v_fst_3007_, lean_object* v___x_3008_, lean_object* v_fst_3009_, lean_object* v_inst_3010_, lean_object* v_R_3011_, lean_object* v_a_3012_, lean_object* v_b_3013_, lean_object* v_c_3014_){
_start:
{
lean_object* v_res_3015_; 
v_res_3015_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__12(v_upperBound_3006_, v_fst_3007_, v___x_3008_, v_fst_3009_, v_inst_3010_, v_R_3011_, v_a_3012_, v_b_3013_, v_c_3014_);
lean_dec_ref(v_fst_3009_);
lean_dec(v___x_3008_);
lean_dec_ref(v_fst_3007_);
lean_dec(v_upperBound_3006_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13(lean_object* v_00_u03b2_3016_, lean_object* v_m_3017_, lean_object* v_a_3018_){
_start:
{
lean_object* v___x_3019_; 
v___x_3019_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___redArg(v_m_3017_, v_a_3018_);
return v___x_3019_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13___boxed(lean_object* v_00_u03b2_3020_, lean_object* v_m_3021_, lean_object* v_a_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13(v_00_u03b2_3020_, v_m_3021_, v_a_3022_);
lean_dec_ref(v_a_3022_);
lean_dec_ref(v_m_3021_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14(lean_object* v_00_u03b2_3024_, lean_object* v_m_3025_, lean_object* v_a_3026_, lean_object* v_b_3027_){
_start:
{
lean_object* v___x_3028_; 
v___x_3028_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14___redArg(v_m_3025_, v_a_3026_, v_b_3027_);
return v___x_3028_;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14(lean_object* v_inst_3029_, lean_object* v_R_3030_, lean_object* v_a_3031_, lean_object* v_b_3032_){
_start:
{
lean_object* v___x_3033_; 
v___x_3033_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Util_Diff_0__Lean_Diff_matchSuffix_go___at___00Lean_Diff_matchSuffix___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__5_spec__8_spec__14___redArg(v_a_3031_, v_b_3032_);
return v___x_3033_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20(lean_object* v_00_u03b2_3034_, lean_object* v_a_3035_, lean_object* v_x_3036_){
_start:
{
lean_object* v___x_3037_; 
v___x_3037_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___redArg(v_a_3035_, v_x_3036_);
return v___x_3037_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20___boxed(lean_object* v_00_u03b2_3038_, lean_object* v_a_3039_, lean_object* v_x_3040_){
_start:
{
lean_object* v_res_3041_; 
v_res_3041_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__13_spec__20(v_00_u03b2_3038_, v_a_3039_, v_x_3040_);
lean_dec(v_x_3040_);
lean_dec_ref(v_a_3039_);
return v_res_3041_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22(lean_object* v_00_u03b2_3042_, lean_object* v_a_3043_, lean_object* v_x_3044_){
_start:
{
uint8_t v___x_3045_; 
v___x_3045_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___redArg(v_a_3043_, v_x_3044_);
return v___x_3045_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_3043_ = stack[1].m_obj;
lean_object* v_x_3044_ = stack[2].m_obj;
uint8_t v_res_3046_;
v_res_3046_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22(lean_box(0), v_a_3043_, v_x_3044_);
stack->m_num = v_res_3046_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22___boxed(lean_object* v_00_u03b2_3047_, lean_object* v_a_3048_, lean_object* v_x_3049_){
_start:
{
uint8_t v_res_3050_; lean_object* v_r_3051_; 
v_res_3050_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__22(v_00_u03b2_3047_, v_a_3048_, v_x_3049_);
lean_dec(v_x_3049_);
lean_dec_ref(v_a_3048_);
v_r_3051_ = lean_box(v_res_3050_);
return v_r_3051_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23(lean_object* v_00_u03b2_3052_, lean_object* v_data_3053_){
_start:
{
lean_object* v___x_3054_; 
v___x_3054_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23___redArg(v_data_3053_);
return v___x_3054_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24(lean_object* v_00_u03b2_3055_, lean_object* v_a_3056_, lean_object* v_b_3057_, lean_object* v_x_3058_){
_start:
{
lean_object* v___x_3059_; 
v___x_3059_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__24___redArg(v_a_3056_, v_b_3057_, v_x_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28(lean_object* v_00_u03b2_3060_, lean_object* v_i_3061_, lean_object* v_source_3062_, lean_object* v_target_3063_){
_start:
{
lean_object* v___x_3064_; 
v___x_3064_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28___redArg(v_i_3061_, v_source_3062_, v_target_3063_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29(lean_object* v_00_u03b2_3065_, lean_object* v_x_3066_, lean_object* v_x_3067_){
_start:
{
lean_object* v___x_3068_; 
v___x_3068_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Diff_Histogram_addRight___at___00Lean_Diff_lcs___at___00Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff_spec__1_spec__3_spec__9_spec__14_spec__23_spec__28_spec__29___redArg(v_x_3066_, v_x_3067_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(lean_object* v_s_3069_){
_start:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3070_ = l_String_toListImpl(v_s_3069_);
v___x_3071_ = lean_array_mk(v___x_3070_);
return v___x_3071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(lean_object* v_s_3072_, lean_object* v_s_x27_3073_){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3074_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3072_);
v___x_3075_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3073_);
v___x_3076_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3074_, v___x_3075_);
v___x_3077_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff(v___x_3076_);
lean_dec_ref(v___x_3076_);
return v___x_3077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(lean_object* v_s_3078_, lean_object* v_s_x27_3079_){
_start:
{
uint8_t v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; uint8_t v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3080_ = 1;
v___x_3081_ = lean_box(v___x_3080_);
v___x_3082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
lean_ctor_set(v___x_3082_, 1, v_s_3078_);
v___x_3083_ = 0;
v___x_3084_ = lean_box(v___x_3083_);
v___x_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
lean_ctor_set(v___x_3085_, 1, v_s_x27_3079_);
v___x_3086_ = lean_unsigned_to_nat(2u);
v___x_3087_ = lean_mk_empty_array_with_capacity(v___x_3086_);
v___x_3088_ = lean_array_push(v___x_3087_, v___x_3082_);
v___x_3089_ = lean_array_push(v___x_3088_, v___x_3085_);
return v___x_3089_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(lean_object* v_as_3090_, size_t v_i_3091_, size_t v_stop_3092_, lean_object* v_b_3093_){
_start:
{
lean_object* v___y_3095_; uint8_t v___x_3099_; 
v___x_3099_ = lean_usize_dec_eq(v_i_3091_, v_stop_3092_);
if (v___x_3099_ == 0)
{
lean_object* v___x_3100_; lean_object* v_fst_3101_; uint8_t v___x_3102_; uint8_t v___x_3103_; uint8_t v___x_3104_; 
v___x_3100_ = lean_array_uget_borrowed(v_as_3090_, v_i_3091_);
v_fst_3101_ = lean_ctor_get(v___x_3100_, 0);
v___x_3102_ = 2;
v___x_3103_ = lean_unbox(v_fst_3101_);
v___x_3104_ = l_Lean_Diff_instBEqAction_beq(v___x_3103_, v___x_3102_);
if (v___x_3104_ == 0)
{
lean_object* v___x_3105_; 
lean_inc(v___x_3100_);
v___x_3105_ = lean_array_push(v_b_3093_, v___x_3100_);
v___y_3095_ = v___x_3105_;
goto v___jp_3094_;
}
else
{
v___y_3095_ = v_b_3093_;
goto v___jp_3094_;
}
}
else
{
return v_b_3093_;
}
v___jp_3094_:
{
size_t v___x_3096_; size_t v___x_3097_; 
v___x_3096_ = ((size_t)1ULL);
v___x_3097_ = lean_usize_add(v_i_3091_, v___x_3096_);
v_i_3091_ = v___x_3097_;
v_b_3093_ = v___y_3095_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3090_ = stack[0].m_obj;
size_t v_i_3091_ = stack[1].m_num;
size_t v_stop_3092_ = stack[2].m_num;
lean_object* v_b_3093_ = stack[3].m_obj;
lean_object* v_res_3106_;
v_res_3106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_as_3090_, v_i_3091_, v_stop_3092_, v_b_3093_);
stack->m_obj
 = v_res_3106_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0___boxed(lean_object* v_as_3107_, lean_object* v_i_3108_, lean_object* v_stop_3109_, lean_object* v_b_3110_){
_start:
{
size_t v_i_boxed_3111_; size_t v_stop_boxed_3112_; lean_object* v_res_3113_; 
v_i_boxed_3111_ = lean_unbox_usize(v_i_3108_);
lean_dec(v_i_3108_);
v_stop_boxed_3112_ = lean_unbox_usize(v_stop_3109_);
lean_dec(v_stop_3109_);
v_res_3113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_as_3107_, v_i_boxed_3111_, v_stop_boxed_3112_, v_b_3110_);
lean_dec_ref(v_as_3107_);
return v_res_3113_;
}
}
lean_object* l_Lean_Meta_Hint_readableDiff(lean_object* v_s_3114_, lean_object* v_s_x27_3115_, uint8_t v_granularity_3116_){
_start:
{
lean_object* v___y_3118_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; 
switch(v_granularity_3116_)
{
case 0:
{
lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___y_3160_; uint8_t v___x_3166_; 
v___x_3157_ = lean_string_length(v_s_3114_);
v___x_3158_ = lean_string_length(v_s_x27_3115_);
v___x_3166_ = lean_nat_dec_le(v___x_3157_, v___x_3158_);
if (v___x_3166_ == 0)
{
v___y_3160_ = v___x_3158_;
goto v___jp_3159_;
}
else
{
v___y_3160_ = v___x_3157_;
goto v___jp_3159_;
}
v___jp_3159_:
{
lean_object* v___x_3161_; lean_object* v_maxCharDiffDistance_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; uint8_t v___x_3165_; 
v___x_3161_ = lean_unsigned_to_nat(5u);
v_maxCharDiffDistance_3162_ = lean_nat_div(v___y_3160_, v___x_3161_);
v___x_3163_ = lean_unsigned_to_nat(1u);
v___x_3164_ = lean_nat_shiftr(v___y_3160_, v___x_3163_);
lean_dec(v___y_3160_);
v___x_3165_ = lean_nat_dec_le(v___x_3157_, v___x_3158_);
if (v___x_3165_ == 0)
{
v___y_3137_ = v___x_3164_;
v___y_3138_ = v___x_3163_;
v___y_3139_ = v_maxCharDiffDistance_3162_;
v___y_3140_ = v___x_3157_;
goto v___jp_3136_;
}
else
{
v___y_3137_ = v___x_3164_;
v___y_3138_ = v___x_3163_;
v___y_3139_ = v_maxCharDiffDistance_3162_;
v___y_3140_ = v___x_3158_;
goto v___jp_3136_;
}
}
}
case 1:
{
lean_object* v___x_3167_; 
v___x_3167_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_charDiff(v_s_3114_, v_s_x27_3115_);
return v___x_3167_;
}
case 2:
{
lean_object* v___x_3168_; 
v___x_3168_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3114_, v_s_x27_3115_);
lean_dec_ref(v_s_x27_3115_);
lean_dec_ref(v_s_3114_);
return v___x_3168_;
}
case 3:
{
lean_object* v___x_3169_; 
v___x_3169_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3114_, v_s_x27_3115_);
return v___x_3169_;
}
default: 
{
uint8_t v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
lean_dec_ref(v_s_3114_);
v___x_3170_ = 0;
v___x_3171_ = lean_box(v___x_3170_);
v___x_3172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3172_, 0, v___x_3171_);
lean_ctor_set(v___x_3172_, 1, v_s_x27_3115_);
v___x_3173_ = lean_unsigned_to_nat(1u);
v___x_3174_ = lean_mk_empty_array_with_capacity(v___x_3173_);
v___x_3175_ = lean_array_push(v___x_3174_, v___x_3172_);
return v___x_3175_;
}
}
v___jp_3117_:
{
size_t v_sz_3119_; size_t v___x_3120_; lean_object* v___x_3121_; 
v_sz_3119_ = lean_array_size(v___y_3118_);
v___x_3120_ = ((size_t)0ULL);
v___x_3121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinCharDiff_spec__0(v_sz_3119_, v___x_3120_, v___y_3118_);
return v___x_3121_;
}
v___jp_3122_:
{
lean_object* v_charArrDiff_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; uint8_t v___x_3130_; 
v_charArrDiff_3127_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_joinEdits___redArg(v___y_3123_);
lean_dec_ref(v___y_3123_);
v___x_3128_ = lean_array_get_size(v_charArrDiff_3127_);
v___x_3129_ = lean_unsigned_to_nat(3u);
v___x_3130_ = lean_nat_dec_le(v___x_3128_, v___x_3129_);
if (v___x_3130_ == 0)
{
lean_object* v_approxEditDistance_3131_; uint8_t v___x_3132_; 
v_approxEditDistance_3131_ = lean_array_get_size(v___y_3126_);
lean_dec_ref(v___y_3126_);
v___x_3132_ = lean_nat_dec_le(v_approxEditDistance_3131_, v___y_3125_);
lean_dec(v___y_3125_);
if (v___x_3132_ == 0)
{
uint8_t v___x_3133_; 
lean_dec_ref(v_charArrDiff_3127_);
v___x_3133_ = lean_nat_dec_le(v_approxEditDistance_3131_, v___y_3124_);
lean_dec(v___y_3124_);
if (v___x_3133_ == 0)
{
lean_object* v___x_3134_; 
v___x_3134_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_maxDiff(v_s_3114_, v_s_x27_3115_);
return v___x_3134_;
}
else
{
lean_object* v___x_3135_; 
v___x_3135_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_wordDiff(v_s_3114_, v_s_x27_3115_);
lean_dec_ref(v_s_x27_3115_);
lean_dec_ref(v_s_3114_);
return v___x_3135_;
}
}
else
{
lean_dec(v___y_3124_);
lean_dec_ref(v_s_x27_3115_);
lean_dec_ref(v_s_3114_);
v___y_3118_ = v_charArrDiff_3127_;
goto v___jp_3117_;
}
}
else
{
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v_s_x27_3115_);
lean_dec_ref(v_s_3114_);
v___y_3118_ = v_charArrDiff_3127_;
goto v___jp_3117_;
}
}
v___jp_3136_:
{
lean_object* v___x_3141_; lean_object* v_maxWordDiffDistance_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v_charDiffRaw_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; uint8_t v___x_3149_; 
v___x_3141_ = lean_nat_shiftr(v___y_3140_, v___y_3138_);
lean_dec(v___y_3140_);
v_maxWordDiffDistance_3142_ = lean_nat_add(v___y_3137_, v___x_3141_);
lean_dec(v___x_3141_);
lean_dec(v___y_3137_);
lean_inc_ref(v_s_3114_);
v___x_3143_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_3114_);
lean_inc_ref(v_s_x27_3115_);
v___x_3144_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_splitChars(v_s_x27_3115_);
v_charDiffRaw_3145_ = l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1(v___x_3143_, v___x_3144_);
v___x_3146_ = lean_unsigned_to_nat(0u);
v___x_3147_ = lean_array_get_size(v_charDiffRaw_3145_);
v___x_3148_ = ((lean_object*)(l_Lean_Diff_diff___at___00__private_Lean_Meta_Hint_0__Lean_Meta_Hint_readableDiff_mkWhitespaceDiff_spec__1___closed__0));
v___x_3149_ = lean_nat_dec_lt(v___x_3146_, v___x_3147_);
if (v___x_3149_ == 0)
{
v___y_3123_ = v_charDiffRaw_3145_;
v___y_3124_ = v_maxWordDiffDistance_3142_;
v___y_3125_ = v___y_3139_;
v___y_3126_ = v___x_3148_;
goto v___jp_3122_;
}
else
{
uint8_t v___x_3150_; 
v___x_3150_ = lean_nat_dec_le(v___x_3147_, v___x_3147_);
if (v___x_3150_ == 0)
{
if (v___x_3149_ == 0)
{
v___y_3123_ = v_charDiffRaw_3145_;
v___y_3124_ = v_maxWordDiffDistance_3142_;
v___y_3125_ = v___y_3139_;
v___y_3126_ = v___x_3148_;
goto v___jp_3122_;
}
else
{
size_t v___x_3151_; size_t v___x_3152_; lean_object* v___x_3153_; 
v___x_3151_ = ((size_t)0ULL);
v___x_3152_ = lean_usize_of_nat(v___x_3147_);
v___x_3153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3145_, v___x_3151_, v___x_3152_, v___x_3148_);
v___y_3123_ = v_charDiffRaw_3145_;
v___y_3124_ = v_maxWordDiffDistance_3142_;
v___y_3125_ = v___y_3139_;
v___y_3126_ = v___x_3153_;
goto v___jp_3122_;
}
}
else
{
size_t v___x_3154_; size_t v___x_3155_; lean_object* v___x_3156_; 
v___x_3154_ = ((size_t)0ULL);
v___x_3155_ = lean_usize_of_nat(v___x_3147_);
v___x_3156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_readableDiff_spec__0(v_charDiffRaw_3145_, v___x_3154_, v___x_3155_, v___x_3148_);
v___y_3123_ = v_charDiffRaw_3145_;
v___y_3124_ = v_maxWordDiffDistance_3142_;
v___y_3125_ = v___y_3139_;
v___y_3126_ = v___x_3156_;
goto v___jp_3122_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Hint_readableDiff_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_3114_ = stack[0].m_obj;
lean_object* v_s_x27_3115_ = stack[1].m_obj;
uint8_t v_granularity_3116_ = stack[2].m_num;
lean_object* v_res_3176_;
v_res_3176_ = l_Lean_Meta_Hint_readableDiff(v_s_3114_, v_s_x27_3115_, v_granularity_3116_);
stack->m_obj
 = v_res_3176_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_readableDiff___boxed(lean_object* v_s_3177_, lean_object* v_s_x27_3178_, lean_object* v_granularity_3179_){
_start:
{
uint8_t v_granularity_boxed_3180_; lean_object* v_res_3181_; 
v_granularity_boxed_3180_ = lean_unbox(v_granularity_3179_);
v_res_3181_ = l_Lean_Meta_Hint_readableDiff(v_s_3177_, v_s_x27_3178_, v_granularity_boxed_3180_);
return v_res_3181_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(lean_object* v_as_3182_, size_t v_i_3183_, size_t v_stop_3184_, lean_object* v_b_3185_){
_start:
{
uint8_t v___x_3186_; 
v___x_3186_ = lean_usize_dec_eq(v_i_3183_, v_stop_3184_);
if (v___x_3186_ == 0)
{
lean_object* v___x_3187_; lean_object* v_snd_3188_; lean_object* v___x_3189_; size_t v___x_3190_; size_t v___x_3191_; 
v___x_3187_ = lean_array_uget_borrowed(v_as_3182_, v_i_3183_);
v_snd_3188_ = lean_ctor_get(v___x_3187_, 1);
v___x_3189_ = lean_string_append(v_b_3185_, v_snd_3188_);
v___x_3190_ = ((size_t)1ULL);
v___x_3191_ = lean_usize_add(v_i_3183_, v___x_3190_);
v_i_3183_ = v___x_3191_;
v_b_3185_ = v___x_3189_;
goto _start;
}
else
{
return v_b_3185_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3182_ = stack[0].m_obj;
size_t v_i_3183_ = stack[1].m_num;
size_t v_stop_3184_ = stack[2].m_num;
lean_object* v_b_3185_ = stack[3].m_obj;
lean_object* v_res_3193_;
v_res_3193_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v_as_3182_, v_i_3183_, v_stop_3184_, v_b_3185_);
stack->m_obj
 = v_res_3193_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0___boxed(lean_object* v_as_3194_, lean_object* v_i_3195_, lean_object* v_stop_3196_, lean_object* v_b_3197_){
_start:
{
size_t v_i_boxed_3198_; size_t v_stop_boxed_3199_; lean_object* v_res_3200_; 
v_i_boxed_3198_ = lean_unbox_usize(v_i_3195_);
lean_dec(v_i_3195_);
v_stop_boxed_3199_ = lean_unbox_usize(v_stop_3196_);
lean_dec(v_stop_3196_);
v_res_3200_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v_as_3194_, v_i_boxed_3198_, v_stop_boxed_3199_, v_b_3197_);
lean_dec_ref(v_as_3194_);
return v_res_3200_;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(lean_object* v_t_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v___x_3204_; lean_object* v_infoState_3205_; uint8_t v_enabled_3206_; 
v___x_3204_ = lean_st_ref_get(v___y_3202_);
v_infoState_3205_ = lean_ctor_get(v___x_3204_, 8);
lean_inc_ref(v_infoState_3205_);
lean_dec(v___x_3204_);
v_enabled_3206_ = lean_ctor_get_uint8(v_infoState_3205_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3205_);
if (v_enabled_3206_ == 0)
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
lean_dec_ref(v_t_3201_);
v___x_3207_ = lean_box(0);
v___x_3208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3207_);
return v___x_3208_;
}
else
{
lean_object* v___x_3209_; lean_object* v_infoState_3210_; lean_object* v_env_3211_; lean_object* v_nextMacroScope_3212_; lean_object* v_ngen_3213_; lean_object* v_auxDeclNGen_3214_; lean_object* v_traceState_3215_; lean_object* v_cache_3216_; lean_object* v_recordedDeps_3217_; lean_object* v_messages_3218_; lean_object* v_snapshotTasks_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3241_; 
v___x_3209_ = lean_st_ref_take(v___y_3202_);
v_infoState_3210_ = lean_ctor_get(v___x_3209_, 8);
v_env_3211_ = lean_ctor_get(v___x_3209_, 0);
v_nextMacroScope_3212_ = lean_ctor_get(v___x_3209_, 1);
v_ngen_3213_ = lean_ctor_get(v___x_3209_, 2);
v_auxDeclNGen_3214_ = lean_ctor_get(v___x_3209_, 3);
v_traceState_3215_ = lean_ctor_get(v___x_3209_, 4);
v_cache_3216_ = lean_ctor_get(v___x_3209_, 5);
v_recordedDeps_3217_ = lean_ctor_get(v___x_3209_, 6);
v_messages_3218_ = lean_ctor_get(v___x_3209_, 7);
v_snapshotTasks_3219_ = lean_ctor_get(v___x_3209_, 9);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3221_ = v___x_3209_;
v_isShared_3222_ = v_isSharedCheck_3241_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_snapshotTasks_3219_);
lean_inc(v_infoState_3210_);
lean_inc(v_messages_3218_);
lean_inc(v_recordedDeps_3217_);
lean_inc(v_cache_3216_);
lean_inc(v_traceState_3215_);
lean_inc(v_auxDeclNGen_3214_);
lean_inc(v_ngen_3213_);
lean_inc(v_nextMacroScope_3212_);
lean_inc(v_env_3211_);
lean_dec(v___x_3209_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3241_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
uint8_t v_enabled_3223_; lean_object* v_assignment_3224_; lean_object* v_lazyAssignment_3225_; lean_object* v_trees_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3240_; 
v_enabled_3223_ = lean_ctor_get_uint8(v_infoState_3210_, sizeof(void*)*3);
v_assignment_3224_ = lean_ctor_get(v_infoState_3210_, 0);
v_lazyAssignment_3225_ = lean_ctor_get(v_infoState_3210_, 1);
v_trees_3226_ = lean_ctor_get(v_infoState_3210_, 2);
v_isSharedCheck_3240_ = !lean_is_exclusive(v_infoState_3210_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3228_ = v_infoState_3210_;
v_isShared_3229_ = v_isSharedCheck_3240_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_trees_3226_);
lean_inc(v_lazyAssignment_3225_);
lean_inc(v_assignment_3224_);
lean_dec(v_infoState_3210_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3240_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3233_; 
v___x_3230_ = lean_box(0);
v___x_3231_ = l_Lean_PersistentArray_push___redArg(v_trees_3226_, v_t_3201_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 2, v___x_3231_);
v___x_3233_ = v___x_3228_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_assignment_3224_);
lean_ctor_set(v_reuseFailAlloc_3239_, 1, v_lazyAssignment_3225_);
lean_ctor_set(v_reuseFailAlloc_3239_, 2, v___x_3231_);
lean_ctor_set_uint8(v_reuseFailAlloc_3239_, sizeof(void*)*3, v_enabled_3223_);
v___x_3233_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
lean_object* v___x_3235_; 
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 8, v___x_3233_);
v___x_3235_ = v___x_3221_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_env_3211_);
lean_ctor_set(v_reuseFailAlloc_3238_, 1, v_nextMacroScope_3212_);
lean_ctor_set(v_reuseFailAlloc_3238_, 2, v_ngen_3213_);
lean_ctor_set(v_reuseFailAlloc_3238_, 3, v_auxDeclNGen_3214_);
lean_ctor_set(v_reuseFailAlloc_3238_, 4, v_traceState_3215_);
lean_ctor_set(v_reuseFailAlloc_3238_, 5, v_cache_3216_);
lean_ctor_set(v_reuseFailAlloc_3238_, 6, v_recordedDeps_3217_);
lean_ctor_set(v_reuseFailAlloc_3238_, 7, v_messages_3218_);
lean_ctor_set(v_reuseFailAlloc_3238_, 8, v___x_3233_);
lean_ctor_set(v_reuseFailAlloc_3238_, 9, v_snapshotTasks_3219_);
v___x_3235_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3236_ = lean_st_ref_put(v___y_3202_, v___x_3235_);
v___x_3237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3230_);
return v___x_3237_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_3201_ = stack[0].m_obj;
lean_object* v___y_3202_ = stack[1].m_obj;
lean_object* v_res_3242_;
v_res_3242_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3201_, v___y_3202_);
stack->m_obj
 = v_res_3242_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg___boxed(lean_object* v_t_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3243_, v___y_3244_);
lean_dec(v___y_3244_);
return v_res_3246_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3247_ = lean_unsigned_to_nat(32u);
v___x_3248_ = lean_mk_empty_array_with_capacity(v___x_3247_);
v___x_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3248_);
return v___x_3249_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1(void){
_start:
{
size_t v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3250_ = ((size_t)5ULL);
v___x_3251_ = lean_unsigned_to_nat(0u);
v___x_3252_ = lean_unsigned_to_nat(32u);
v___x_3253_ = lean_mk_empty_array_with_capacity(v___x_3252_);
v___x_3254_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__0);
v___x_3255_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3255_, 0, v___x_3254_);
lean_ctor_set(v___x_3255_, 1, v___x_3253_);
lean_ctor_set(v___x_3255_, 2, v___x_3251_);
lean_ctor_set(v___x_3255_, 3, v___x_3251_);
lean_ctor_set_usize(v___x_3255_, 4, v___x_3250_);
return v___x_3255_;
}
}
lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(lean_object* v_t_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
lean_object* v___x_3260_; lean_object* v_infoState_3261_; uint8_t v_enabled_3262_; 
v___x_3260_ = lean_st_ref_get(v___y_3258_);
v_infoState_3261_ = lean_ctor_get(v___x_3260_, 8);
lean_inc_ref(v_infoState_3261_);
lean_dec(v___x_3260_);
v_enabled_3262_ = lean_ctor_get_uint8(v_infoState_3261_, sizeof(void*)*3);
lean_dec_ref(v_infoState_3261_);
if (v_enabled_3262_ == 0)
{
lean_object* v___x_3263_; lean_object* v___x_3264_; 
lean_dec_ref(v_t_3256_);
v___x_3263_ = lean_box(0);
v___x_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3263_);
return v___x_3264_;
}
else
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3265_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___closed__1);
v___x_3266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3266_, 0, v_t_3256_);
lean_ctor_set(v___x_3266_, 1, v___x_3265_);
v___x_3267_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v___x_3266_, v___y_3258_);
return v___x_3267_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_3256_ = stack[0].m_obj;
lean_object* v___y_3257_ = stack[1].m_obj;
lean_object* v___y_3258_ = stack[2].m_obj;
lean_object* v_res_3268_;
v_res_3268_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v_t_3256_, v___y_3257_, v___y_3258_);
stack->m_obj
 = v_res_3268_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1___boxed(lean_object* v_t_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
lean_object* v_res_3273_; 
v_res_3273_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v_t_3269_, v___y_3270_, v___y_3271_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
return v_res_3273_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0(lean_object* v___x_3274_, lean_object* v___y_3275_){
_start:
{
lean_object* v___x_3276_; 
v___x_3276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3274_);
lean_ctor_set(v___x_3276_, 1, v___y_3275_);
return v___x_3276_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1(void){
_start:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3278_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__0));
v___x_3279_ = l_Lean_stringToMessageData(v___x_3278_);
return v___x_3279_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3(void){
_start:
{
lean_object* v___x_3281_; lean_object* v___x_3282_; 
v___x_3281_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__2));
v___x_3282_ = l_Lean_stringToMessageData(v___x_3281_);
return v___x_3282_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29(void){
_start:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3331_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__28));
v___x_3332_ = l_Lean_Json_mkObj(v___x_3331_);
return v___x_3332_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30(void){
_start:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v___x_3333_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__29);
v___x_3334_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__19));
v___x_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3334_);
lean_ctor_set(v___x_3335_, 1, v___x_3333_);
return v___x_3335_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31(void){
_start:
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3336_ = lean_box(0);
v___x_3337_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__30);
v___x_3338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3337_);
lean_ctor_set(v___x_3338_, 1, v___x_3336_);
return v___x_3338_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33(void){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3341_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__32));
v___x_3342_ = l_Lean_MessageData_ofFormat(v___x_3341_);
return v___x_3342_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35(void){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3344_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__34));
v___x_3345_ = l_Lean_stringToMessageData(v___x_3344_);
return v___x_3345_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(lean_object* v_suggestions_3347_, uint8_t v_forceList_3348_, lean_object* v_codeActionPrefix_x3f_3349_, lean_object* v_ref_3350_, lean_object* v_as_3351_, size_t v_sz_3352_, size_t v_i_3353_, lean_object* v_b_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_){
_start:
{
lean_object* v_a_3359_; lean_object* v___y_3364_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3375_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; uint8_t v___x_3403_; 
v___x_3403_ = lean_usize_dec_lt(v_i_3353_, v_sz_3352_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; 
lean_dec(v_ref_3350_);
lean_dec(v_codeActionPrefix_x3f_3349_);
v___x_3404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3404_, 0, v_b_3354_);
return v___x_3404_;
}
else
{
lean_object* v_a_3405_; lean_object* v_span_x3f_3406_; lean_object* v___x_3407_; lean_object* v___y_3409_; lean_object* v___y_3410_; uint8_t v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; uint8_t v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; uint8_t v___y_3495_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; uint8_t v___y_3501_; uint8_t v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v_postInfo_x3f_3510_; lean_object* v___y_3511_; uint8_t v___y_3512_; uint8_t v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3521_; uint8_t v___y_3522_; uint8_t v___y_3523_; lean_object* v___y_3524_; lean_object* v_edits_3525_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v_stop_3533_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; uint8_t v___y_3537_; uint8_t v___y_3538_; lean_object* v___y_3539_; lean_object* v_edits_3540_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; uint8_t v___y_3556_; lean_object* v___y_3557_; uint8_t v___y_3558_; lean_object* v___y_3559_; lean_object* v_edits_3560_; lean_object* v___y_3561_; lean_object* v___x_3587_; lean_object* v___y_3589_; lean_object* v___y_3590_; lean_object* v___y_3591_; uint8_t v___y_3592_; uint8_t v___y_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3596_; lean_object* v___y_3597_; lean_object* v___y_3598_; lean_object* v___y_3635_; lean_object* v___y_3636_; lean_object* v___y_3637_; uint8_t v___y_3638_; lean_object* v___y_3639_; uint8_t v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3653_; 
v_a_3405_ = lean_array_uget_borrowed(v_as_3351_, v_i_3353_);
v_span_x3f_3406_ = lean_ctor_get(v_a_3405_, 1);
v___x_3407_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v___x_3587_ = l_Lean_Meta_Tactic_TryThis_instImpl_00___x40_Lean_Meta_TryThis_3141183573____hygCtx___hyg_12_;
if (lean_obj_tag(v_span_x3f_3406_) == 0)
{
lean_inc(v_ref_3350_);
v___y_3653_ = v_ref_3350_;
goto v___jp_3652_;
}
else
{
lean_object* v_val_3674_; 
v_val_3674_ = lean_ctor_get(v_span_x3f_3406_, 0);
lean_inc(v_val_3674_);
v___y_3653_ = v_val_3674_;
goto v___jp_3652_;
}
v___jp_3408_:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___f_3429_; 
lean_inc_ref(v___y_3413_);
v___x_3415_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffJson(v___y_3413_);
v___x_3416_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__9));
v___x_3417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3417_, 0, v___x_3416_);
lean_ctor_set(v___x_3417_, 1, v___x_3415_);
v___x_3418_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3419_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3419_, 0, v___y_3410_);
v___x_3420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3418_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
v___x_3421_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3422_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3409_);
v___x_3423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3423_, 0, v___x_3421_);
lean_ctor_set(v___x_3423_, 1, v___x_3422_);
v___x_3424_ = lean_box(0);
v___x_3425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3423_);
lean_ctor_set(v___x_3425_, 1, v___x_3424_);
v___x_3426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3420_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3427_, 0, v___x_3417_);
lean_ctor_set(v___x_3427_, 1, v___x_3426_);
v___x_3428_ = l_Lean_Json_mkObj(v___x_3427_);
lean_dec_ref_known(v___x_3427_, 2);
v___f_3429_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3429_, 0, v___x_3428_);
if (v___y_3411_ == 0)
{
lean_object* v___x_3430_; 
v___x_3430_ = l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString(v___y_3413_);
v___y_3383_ = v___y_3414_;
v___y_3384_ = v___y_3412_;
v___y_3385_ = v___f_3429_;
v___y_3386_ = v___x_3430_;
goto v___jp_3382_;
}
else
{
lean_object* v___x_3431_; lean_object* v___x_3432_; uint8_t v___x_3433_; 
v___x_3431_ = lean_unsigned_to_nat(0u);
v___x_3432_ = lean_array_get_size(v___y_3413_);
v___x_3433_ = lean_nat_dec_lt(v___x_3431_, v___x_3432_);
if (v___x_3433_ == 0)
{
lean_dec_ref(v___y_3413_);
v___y_3383_ = v___y_3414_;
v___y_3384_ = v___y_3412_;
v___y_3385_ = v___f_3429_;
v___y_3386_ = v___x_3407_;
goto v___jp_3382_;
}
else
{
uint8_t v___x_3434_; 
v___x_3434_ = lean_nat_dec_le(v___x_3432_, v___x_3432_);
if (v___x_3434_ == 0)
{
if (v___x_3433_ == 0)
{
lean_dec_ref(v___y_3413_);
v___y_3383_ = v___y_3414_;
v___y_3384_ = v___y_3412_;
v___y_3385_ = v___f_3429_;
v___y_3386_ = v___x_3407_;
goto v___jp_3382_;
}
else
{
size_t v___x_3435_; size_t v___x_3436_; lean_object* v___x_3437_; 
v___x_3435_ = ((size_t)0ULL);
v___x_3436_ = lean_usize_of_nat(v___x_3432_);
v___x_3437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3413_, v___x_3435_, v___x_3436_, v___x_3407_);
lean_dec_ref(v___y_3413_);
v___y_3383_ = v___y_3414_;
v___y_3384_ = v___y_3412_;
v___y_3385_ = v___f_3429_;
v___y_3386_ = v___x_3437_;
goto v___jp_3382_;
}
}
else
{
size_t v___x_3438_; size_t v___x_3439_; lean_object* v___x_3440_; 
v___x_3438_ = ((size_t)0ULL);
v___x_3439_ = lean_usize_of_nat(v___x_3432_);
v___x_3440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__0(v___y_3413_, v___x_3438_, v___x_3439_, v___x_3407_);
lean_dec_ref(v___y_3413_);
v___y_3383_ = v___y_3414_;
v___y_3384_ = v___y_3412_;
v___y_3385_ = v___f_3429_;
v___y_3386_ = v___x_3440_;
goto v___jp_3382_;
}
}
}
}
v___jp_3441_:
{
if (lean_obj_tag(v___y_3449_) == 0)
{
lean_object* v___x_3450_; uint64_t v_javascriptHash_3451_; lean_object* v_suggestion_3452_; lean_object* v_messageData_x3f_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___f_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
lean_dec_ref(v___y_3445_);
v___x_3450_ = ((lean_object*)(l_Lean_Meta_Hint_textInsertionWidget));
v_javascriptHash_3451_ = lean_ctor_get_uint64(v___x_3450_, sizeof(void*)*1);
v_suggestion_3452_ = lean_ctor_get(v___y_3443_, 0);
lean_inc_ref(v_suggestion_3452_);
v_messageData_x3f_3453_ = lean_ctor_get(v___y_3443_, 4);
lean_inc(v_messageData_x3f_3453_);
lean_dec_ref(v___y_3443_);
v___x_3454_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__18));
v___x_3455_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__11));
v___x_3456_ = l_Lean_Lsp_instToJsonRange_toJson(v___y_3442_);
v___x_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3455_);
lean_ctor_set(v___x_3457_, 1, v___x_3456_);
v___x_3458_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__10));
v___x_3459_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3459_, 0, v___y_3444_);
v___x_3460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3460_, 0, v___x_3458_);
lean_ctor_set(v___x_3460_, 1, v___x_3459_);
v___x_3461_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__31);
v___x_3462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3460_);
lean_ctor_set(v___x_3462_, 1, v___x_3461_);
v___x_3463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3457_);
lean_ctor_set(v___x_3463_, 1, v___x_3462_);
v___x_3464_ = l_Lean_Json_mkObj(v___x_3463_);
lean_dec_ref_known(v___x_3463_, 2);
v___f_3465_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___lam__0), 2, 1);
lean_closure_set(v___f_3465_, 0, v___x_3464_);
v___x_3466_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3466_, 0, v___x_3454_);
lean_ctor_set(v___x_3466_, 1, v___f_3465_);
lean_ctor_set_uint64(v___x_3466_, sizeof(void*)*2, v_javascriptHash_3451_);
v___x_3467_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__33);
v___x_3468_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3466_);
lean_ctor_set(v___x_3468_, 1, v___x_3467_);
v___x_3469_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3470_, 0, v___x_3469_);
lean_ctor_set(v___x_3470_, 1, v___x_3468_);
v___x_3471_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__35);
v___x_3472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3470_);
lean_ctor_set(v___x_3472_, 1, v___x_3471_);
v___x_3473_ = l_Lean_stringToMessageData(v___y_3447_);
v___x_3474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3472_);
lean_ctor_set(v___x_3474_, 1, v___x_3473_);
if (lean_obj_tag(v_messageData_x3f_3453_) == 0)
{
if (lean_obj_tag(v_suggestion_3452_) == 0)
{
lean_object* v_a_3475_; lean_object* v___x_3476_; 
v_a_3475_ = lean_ctor_get(v_suggestion_3452_, 1);
lean_inc(v_a_3475_);
lean_dec_ref_known(v_suggestion_3452_, 2);
v___x_3476_ = l_Lean_MessageData_ofSyntax(v_a_3475_);
v___y_3368_ = v___x_3474_;
v___y_3369_ = v___y_3448_;
v___y_3370_ = v___x_3476_;
goto v___jp_3367_;
}
else
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3485_; 
v_a_3477_ = lean_ctor_get(v_suggestion_3452_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v_suggestion_3452_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3479_ = v_suggestion_3452_;
v_isShared_3480_ = v_isSharedCheck_3485_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v_suggestion_3452_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3485_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
lean_ctor_set_tag(v___x_3479_, 3);
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3477_);
v___x_3482_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
lean_object* v___x_3483_; 
v___x_3483_ = l_Lean_MessageData_ofFormat(v___x_3482_);
v___y_3368_ = v___x_3474_;
v___y_3369_ = v___y_3448_;
v___y_3370_ = v___x_3483_;
goto v___jp_3367_;
}
}
}
}
else
{
lean_object* v_val_3486_; 
lean_dec_ref(v_suggestion_3452_);
v_val_3486_ = lean_ctor_get(v_messageData_x3f_3453_, 0);
lean_inc(v_val_3486_);
lean_dec_ref_known(v_messageData_x3f_3453_, 1);
v___y_3368_ = v___x_3474_;
v___y_3369_ = v___y_3448_;
v___y_3370_ = v_val_3486_;
goto v___jp_3367_;
}
}
else
{
lean_dec_ref_known(v___y_3449_, 1);
lean_dec_ref(v___y_3443_);
v___y_3409_ = v___y_3442_;
v___y_3410_ = v___y_3444_;
v___y_3411_ = v___y_3446_;
v___y_3412_ = v___y_3447_;
v___y_3413_ = v___y_3445_;
v___y_3414_ = v___y_3448_;
goto v___jp_3408_;
}
}
v___jp_3487_:
{
if (v___y_3495_ == 0)
{
lean_object* v_messageData_x3f_3496_; 
v_messageData_x3f_3496_ = lean_ctor_get(v___y_3489_, 4);
if (lean_obj_tag(v_messageData_x3f_3496_) == 0)
{
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3489_);
v___y_3409_ = v___y_3488_;
v___y_3410_ = v___y_3490_;
v___y_3411_ = v___y_3495_;
v___y_3412_ = v___y_3492_;
v___y_3413_ = v___y_3491_;
v___y_3414_ = v___y_3494_;
goto v___jp_3408_;
}
else
{
v___y_3442_ = v___y_3488_;
v___y_3443_ = v___y_3489_;
v___y_3444_ = v___y_3490_;
v___y_3445_ = v___y_3491_;
v___y_3446_ = v___y_3495_;
v___y_3447_ = v___y_3492_;
v___y_3448_ = v___y_3494_;
v___y_3449_ = v___y_3493_;
goto v___jp_3441_;
}
}
else
{
v___y_3442_ = v___y_3488_;
v___y_3443_ = v___y_3489_;
v___y_3444_ = v___y_3490_;
v___y_3445_ = v___y_3491_;
v___y_3446_ = v___y_3495_;
v___y_3447_ = v___y_3492_;
v___y_3448_ = v___y_3494_;
v___y_3449_ = v___y_3493_;
goto v___jp_3441_;
}
}
v___jp_3497_:
{
if (v___y_3501_ == 4)
{
v___y_3488_ = v___y_3498_;
v___y_3489_ = v___y_3499_;
v___y_3490_ = v___y_3500_;
v___y_3491_ = v___y_3504_;
v___y_3492_ = v___y_3503_;
v___y_3493_ = v___y_3505_;
v___y_3494_ = v___y_3506_;
v___y_3495_ = v___x_3403_;
goto v___jp_3487_;
}
else
{
v___y_3488_ = v___y_3498_;
v___y_3489_ = v___y_3499_;
v___y_3490_ = v___y_3500_;
v___y_3491_ = v___y_3504_;
v___y_3492_ = v___y_3503_;
v___y_3493_ = v___y_3505_;
v___y_3494_ = v___y_3506_;
v___y_3495_ = v___y_3502_;
goto v___jp_3487_;
}
}
v___jp_3507_:
{
if (lean_obj_tag(v_postInfo_x3f_3510_) == 0)
{
v___y_3498_ = v___y_3508_;
v___y_3499_ = v___y_3509_;
v___y_3500_ = v___y_3511_;
v___y_3501_ = v___y_3512_;
v___y_3502_ = v___y_3513_;
v___y_3503_ = v___y_3516_;
v___y_3504_ = v___y_3514_;
v___y_3505_ = v___y_3515_;
v___y_3506_ = v___x_3407_;
goto v___jp_3497_;
}
else
{
lean_object* v_val_3517_; 
v_val_3517_ = lean_ctor_get(v_postInfo_x3f_3510_, 0);
lean_inc(v_val_3517_);
lean_dec_ref_known(v_postInfo_x3f_3510_, 1);
v___y_3498_ = v___y_3508_;
v___y_3499_ = v___y_3509_;
v___y_3500_ = v___y_3511_;
v___y_3501_ = v___y_3512_;
v___y_3502_ = v___y_3513_;
v___y_3503_ = v___y_3516_;
v___y_3504_ = v___y_3514_;
v___y_3505_ = v___y_3515_;
v___y_3506_ = v_val_3517_;
goto v___jp_3497_;
}
}
v___jp_3518_:
{
lean_object* v_preInfo_x3f_3526_; 
v_preInfo_x3f_3526_ = lean_ctor_get(v___y_3520_, 1);
if (lean_obj_tag(v_preInfo_x3f_3526_) == 0)
{
lean_object* v_postInfo_x3f_3527_; 
v_postInfo_x3f_3527_ = lean_ctor_get(v___y_3520_, 2);
lean_inc(v_postInfo_x3f_3527_);
v___y_3508_ = v___y_3519_;
v___y_3509_ = v___y_3520_;
v_postInfo_x3f_3510_ = v_postInfo_x3f_3527_;
v___y_3511_ = v___y_3521_;
v___y_3512_ = v___y_3522_;
v___y_3513_ = v___y_3523_;
v___y_3514_ = v_edits_3525_;
v___y_3515_ = v___y_3524_;
v___y_3516_ = v___x_3407_;
goto v___jp_3507_;
}
else
{
lean_object* v_postInfo_x3f_3528_; lean_object* v_val_3529_; 
v_postInfo_x3f_3528_ = lean_ctor_get(v___y_3520_, 2);
lean_inc(v_postInfo_x3f_3528_);
v_val_3529_ = lean_ctor_get(v_preInfo_x3f_3526_, 0);
lean_inc(v_val_3529_);
v___y_3508_ = v___y_3519_;
v___y_3509_ = v___y_3520_;
v_postInfo_x3f_3510_ = v_postInfo_x3f_3528_;
v___y_3511_ = v___y_3521_;
v___y_3512_ = v___y_3522_;
v___y_3513_ = v___y_3523_;
v___y_3514_ = v_edits_3525_;
v___y_3515_ = v___y_3524_;
v___y_3516_ = v_val_3529_;
goto v___jp_3507_;
}
}
v___jp_3530_:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; uint8_t v___x_3543_; 
v___x_3541_ = lean_unsigned_to_nat(1u);
v___x_3542_ = lean_nat_add(v___y_3532_, v___x_3541_);
v___x_3543_ = lean_nat_dec_le(v___x_3542_, v_stop_3533_);
lean_dec(v___x_3542_);
if (v___x_3543_ == 0)
{
lean_dec(v_stop_3533_);
lean_dec(v___y_3532_);
v___y_3519_ = v___y_3531_;
v___y_3520_ = v___y_3535_;
v___y_3521_ = v___y_3536_;
v___y_3522_ = v___y_3537_;
v___y_3523_ = v___y_3538_;
v___y_3524_ = v___y_3539_;
v_edits_3525_ = v_edits_3540_;
goto v___jp_3518_;
}
else
{
lean_object* v_source_3544_; uint8_t v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
v_source_3544_ = lean_ctor_get(v___y_3534_, 0);
v___x_3545_ = 2;
v___x_3546_ = lean_string_utf8_extract(v_source_3544_, v___y_3532_, v_stop_3533_);
lean_dec(v_stop_3533_);
lean_dec(v___y_3532_);
v___x_3547_ = lean_box(v___x_3545_);
v___x_3548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3547_);
lean_ctor_set(v___x_3548_, 1, v___x_3546_);
v___x_3549_ = lean_array_push(v_edits_3540_, v___x_3548_);
v___y_3519_ = v___y_3531_;
v___y_3520_ = v___y_3535_;
v___y_3521_ = v___y_3536_;
v___y_3522_ = v___y_3537_;
v___y_3523_ = v___y_3538_;
v___y_3524_ = v___y_3539_;
v_edits_3525_ = v___x_3549_;
goto v___jp_3518_;
}
}
v___jp_3550_:
{
if (lean_obj_tag(v___y_3559_) == 0)
{
lean_dec_ref(v___y_3557_);
lean_dec(v___y_3553_);
lean_dec(v___y_3552_);
v___y_3519_ = v___y_3551_;
v___y_3520_ = v___y_3554_;
v___y_3521_ = v___y_3555_;
v___y_3522_ = v___y_3556_;
v___y_3523_ = v___y_3558_;
v___y_3524_ = v___y_3559_;
v_edits_3525_ = v_edits_3560_;
goto v___jp_3518_;
}
else
{
lean_object* v_val_3562_; lean_object* v___x_3563_; 
v_val_3562_ = lean_ctor_get(v___y_3559_, 0);
v___x_3563_ = l_Lean_Syntax_getRange_x3f(v_val_3562_, v___y_3558_);
if (lean_obj_tag(v___x_3563_) == 1)
{
lean_object* v_val_3564_; uint8_t v___x_3565_; 
v_val_3564_ = lean_ctor_get(v___x_3563_, 0);
lean_inc(v_val_3564_);
lean_dec_ref_known(v___x_3563_, 1);
v___x_3565_ = l_Lean_Syntax_Range_includes(v_val_3564_, v___y_3557_, v___y_3558_, v___y_3558_);
lean_dec_ref(v___y_3557_);
if (v___x_3565_ == 0)
{
lean_dec(v_val_3564_);
lean_dec(v___y_3553_);
lean_dec(v___y_3552_);
v___y_3519_ = v___y_3551_;
v___y_3520_ = v___y_3554_;
v___y_3521_ = v___y_3555_;
v___y_3522_ = v___y_3556_;
v___y_3523_ = v___y_3558_;
v___y_3524_ = v___y_3559_;
v_edits_3525_ = v_edits_3560_;
goto v___jp_3518_;
}
else
{
lean_object* v_toCold_3566_; lean_object* v_fileMap_3567_; lean_object* v_start_3568_; lean_object* v_stop_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3586_; 
v_toCold_3566_ = lean_ctor_get(v___y_3561_, 0);
v_fileMap_3567_ = lean_ctor_get(v_toCold_3566_, 1);
v_start_3568_ = lean_ctor_get(v_val_3564_, 0);
v_stop_3569_ = lean_ctor_get(v_val_3564_, 1);
v_isSharedCheck_3586_ = !lean_is_exclusive(v_val_3564_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3571_ = v_val_3564_;
v_isShared_3572_ = v_isSharedCheck_3586_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_stop_3569_);
lean_inc(v_start_3568_);
lean_dec(v_val_3564_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3586_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; uint8_t v___x_3575_; 
v___x_3573_ = lean_unsigned_to_nat(1u);
v___x_3574_ = lean_nat_add(v_start_3568_, v___x_3573_);
v___x_3575_ = lean_nat_dec_le(v___x_3574_, v___y_3553_);
lean_dec(v___x_3574_);
if (v___x_3575_ == 0)
{
lean_del_object(v___x_3571_);
lean_dec(v_start_3568_);
lean_dec(v___y_3553_);
v___y_3531_ = v___y_3551_;
v___y_3532_ = v___y_3552_;
v_stop_3533_ = v_stop_3569_;
v___y_3534_ = v_fileMap_3567_;
v___y_3535_ = v___y_3554_;
v___y_3536_ = v___y_3555_;
v___y_3537_ = v___y_3556_;
v___y_3538_ = v___y_3558_;
v___y_3539_ = v___y_3559_;
v_edits_3540_ = v_edits_3560_;
goto v___jp_3530_;
}
else
{
lean_object* v_source_3576_; uint8_t v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3581_; 
v_source_3576_ = lean_ctor_get(v_fileMap_3567_, 0);
v___x_3577_ = 2;
v___x_3578_ = lean_string_utf8_extract(v_source_3576_, v_start_3568_, v___y_3553_);
lean_dec(v___y_3553_);
lean_dec(v_start_3568_);
v___x_3579_ = lean_box(v___x_3577_);
if (v_isShared_3572_ == 0)
{
lean_ctor_set(v___x_3571_, 1, v___x_3578_);
lean_ctor_set(v___x_3571_, 0, v___x_3579_);
v___x_3581_ = v___x_3571_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v___x_3579_);
lean_ctor_set(v_reuseFailAlloc_3585_, 1, v___x_3578_);
v___x_3581_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
v___x_3582_ = lean_mk_empty_array_with_capacity(v___x_3573_);
v___x_3583_ = lean_array_push(v___x_3582_, v___x_3581_);
v___x_3584_ = l_Array_append___redArg(v___x_3583_, v_edits_3560_);
lean_dec_ref(v_edits_3560_);
v___y_3531_ = v___y_3551_;
v___y_3532_ = v___y_3552_;
v_stop_3533_ = v_stop_3569_;
v___y_3534_ = v_fileMap_3567_;
v___y_3535_ = v___y_3554_;
v___y_3536_ = v___y_3555_;
v___y_3537_ = v___y_3556_;
v___y_3538_ = v___y_3558_;
v___y_3539_ = v___y_3559_;
v_edits_3540_ = v___x_3584_;
goto v___jp_3530_;
}
}
}
}
}
else
{
lean_dec(v___x_3563_);
lean_dec_ref(v___y_3557_);
lean_dec(v___y_3553_);
lean_dec(v___y_3552_);
v___y_3519_ = v___y_3551_;
v___y_3520_ = v___y_3554_;
v___y_3521_ = v___y_3555_;
v___y_3522_ = v___y_3556_;
v___y_3523_ = v___y_3558_;
v___y_3524_ = v___y_3559_;
v_edits_3525_ = v_edits_3560_;
goto v___jp_3518_;
}
}
}
v___jp_3588_:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
lean_inc_ref(v___y_3590_);
v___x_3599_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3599_, 0, v___y_3597_);
lean_ctor_set(v___x_3599_, 1, v___y_3598_);
lean_ctor_set(v___x_3599_, 2, v___y_3590_);
v___x_3600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3587_);
lean_ctor_set(v___x_3600_, 1, v___x_3599_);
v___x_3601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___y_3595_);
lean_ctor_set(v___x_3601_, 1, v___x_3600_);
v___x_3602_ = lean_alloc_ctor(10, 1, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3601_);
v___x_3603_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1(v___x_3602_, v___y_3355_, v___y_3356_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_object* v_messageData_x3f_3604_; 
lean_dec_ref_known(v___x_3603_, 1);
v_messageData_x3f_3604_ = lean_ctor_get(v___y_3590_, 4);
if (lean_obj_tag(v_messageData_x3f_3604_) == 1)
{
lean_object* v_start_3605_; lean_object* v_stop_3606_; lean_object* v_val_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; uint8_t v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; 
v_start_3605_ = lean_ctor_get(v___y_3594_, 0);
lean_inc(v_start_3605_);
v_stop_3606_ = lean_ctor_get(v___y_3594_, 1);
lean_inc(v_stop_3606_);
v_val_3607_ = lean_ctor_get(v_messageData_x3f_3604_, 0);
v___x_3608_ = lean_box(0);
lean_inc(v_val_3607_);
v___x_3609_ = l_Lean_MessageData_format(v_val_3607_, v___x_3608_);
v___x_3610_ = 0;
v___x_3611_ = l_Std_Format_defWidth;
v___x_3612_ = lean_unsigned_to_nat(0u);
v___x_3613_ = l_Std_Format_pretty(v___x_3609_, v___x_3611_, v___x_3612_, v___x_3612_);
v___x_3614_ = lean_box(v___x_3610_);
v___x_3615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3614_);
lean_ctor_set(v___x_3615_, 1, v___x_3613_);
v___x_3616_ = lean_unsigned_to_nat(1u);
v___x_3617_ = lean_mk_empty_array_with_capacity(v___x_3616_);
v___x_3618_ = lean_array_push(v___x_3617_, v___x_3615_);
v___y_3551_ = v___y_3589_;
v___y_3552_ = v_stop_3606_;
v___y_3553_ = v_start_3605_;
v___y_3554_ = v___y_3590_;
v___y_3555_ = v___y_3591_;
v___y_3556_ = v___y_3592_;
v___y_3557_ = v___y_3594_;
v___y_3558_ = v___y_3593_;
v___y_3559_ = v___y_3596_;
v_edits_3560_ = v___x_3618_;
v___y_3561_ = v___y_3355_;
goto v___jp_3550_;
}
else
{
lean_object* v_toCold_3619_; lean_object* v_fileMap_3620_; lean_object* v_start_3621_; lean_object* v_stop_3622_; lean_object* v_source_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
v_toCold_3619_ = lean_ctor_get(v___y_3355_, 0);
v_fileMap_3620_ = lean_ctor_get(v_toCold_3619_, 1);
v_start_3621_ = lean_ctor_get(v___y_3594_, 0);
lean_inc(v_start_3621_);
v_stop_3622_ = lean_ctor_get(v___y_3594_, 1);
lean_inc(v_stop_3622_);
v_source_3623_ = lean_ctor_get(v_fileMap_3620_, 0);
v___x_3624_ = lean_string_utf8_extract(v_source_3623_, v_start_3621_, v_stop_3622_);
lean_inc_ref(v___y_3591_);
v___x_3625_ = l_Lean_Meta_Hint_readableDiff(v___x_3624_, v___y_3591_, v___y_3592_);
v___y_3551_ = v___y_3589_;
v___y_3552_ = v_stop_3622_;
v___y_3553_ = v_start_3621_;
v___y_3554_ = v___y_3590_;
v___y_3555_ = v___y_3591_;
v___y_3556_ = v___y_3592_;
v___y_3557_ = v___y_3594_;
v___y_3558_ = v___y_3593_;
v___y_3559_ = v___y_3596_;
v_edits_3560_ = v___x_3625_;
v___y_3561_ = v___y_3355_;
goto v___jp_3550_;
}
}
else
{
lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3633_; 
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3594_);
lean_dec_ref(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec_ref(v_b_3354_);
lean_dec(v_ref_3350_);
lean_dec(v_codeActionPrefix_x3f_3349_);
v_a_3626_ = lean_ctor_get(v___x_3603_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3628_ = v___x_3603_;
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3603_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3631_; 
if (v_isShared_3629_ == 0)
{
v___x_3631_ = v___x_3628_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_a_3626_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
}
v___jp_3634_:
{
lean_object* v_toCodeActionTitle_x3f_3644_; lean_object* v___x_3645_; 
v_toCodeActionTitle_x3f_3644_ = lean_ctor_get(v___y_3636_, 5);
v___x_3645_ = l_Lean_Syntax_ofRange(v___y_3643_, v___x_3403_);
if (lean_obj_tag(v_toCodeActionTitle_x3f_3644_) == 0)
{
if (lean_obj_tag(v_codeActionPrefix_x3f_3349_) == 0)
{
lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3646_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__36));
v___x_3647_ = lean_string_append(v___x_3646_, v___y_3637_);
v___y_3589_ = v___y_3635_;
v___y_3590_ = v___y_3636_;
v___y_3591_ = v___y_3637_;
v___y_3592_ = v___y_3638_;
v___y_3593_ = v___y_3640_;
v___y_3594_ = v___y_3639_;
v___y_3595_ = v___x_3645_;
v___y_3596_ = v___y_3642_;
v___y_3597_ = v___y_3641_;
v___y_3598_ = v___x_3647_;
goto v___jp_3588_;
}
else
{
lean_object* v_val_3648_; lean_object* v___x_3649_; 
v_val_3648_ = lean_ctor_get(v_codeActionPrefix_x3f_3349_, 0);
lean_inc(v_val_3648_);
v___x_3649_ = lean_string_append(v_val_3648_, v___y_3637_);
v___y_3589_ = v___y_3635_;
v___y_3590_ = v___y_3636_;
v___y_3591_ = v___y_3637_;
v___y_3592_ = v___y_3638_;
v___y_3593_ = v___y_3640_;
v___y_3594_ = v___y_3639_;
v___y_3595_ = v___x_3645_;
v___y_3596_ = v___y_3642_;
v___y_3597_ = v___y_3641_;
v___y_3598_ = v___x_3649_;
goto v___jp_3588_;
}
}
else
{
lean_object* v_val_3650_; lean_object* v___x_3651_; 
v_val_3650_ = lean_ctor_get(v_toCodeActionTitle_x3f_3644_, 0);
lean_inc(v_val_3650_);
lean_inc_ref(v___y_3637_);
v___x_3651_ = lean_apply_1(v_val_3650_, v___y_3637_);
v___y_3589_ = v___y_3635_;
v___y_3590_ = v___y_3636_;
v___y_3591_ = v___y_3637_;
v___y_3592_ = v___y_3638_;
v___y_3593_ = v___y_3640_;
v___y_3594_ = v___y_3639_;
v___y_3595_ = v___x_3645_;
v___y_3596_ = v___y_3642_;
v___y_3597_ = v___y_3641_;
v___y_3598_ = v___x_3651_;
goto v___jp_3588_;
}
}
v___jp_3652_:
{
uint8_t v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = 0;
v___x_3655_ = l_Lean_Syntax_getRange_x3f(v___y_3653_, v___x_3654_);
lean_dec(v___y_3653_);
if (lean_obj_tag(v___x_3655_) == 1)
{
lean_object* v_val_3656_; lean_object* v_toTryThisSuggestion_3657_; lean_object* v_previewSpan_x3f_3658_; uint8_t v_diffGranularity_3659_; lean_object* v___x_3660_; 
v_val_3656_ = lean_ctor_get(v___x_3655_, 0);
lean_inc_n(v_val_3656_, 2);
lean_dec_ref_known(v___x_3655_, 1);
v_toTryThisSuggestion_3657_ = lean_ctor_get(v_a_3405_, 0);
v_previewSpan_x3f_3658_ = lean_ctor_get(v_a_3405_, 2);
v_diffGranularity_3659_ = lean_ctor_get_uint8(v_a_3405_, sizeof(void*)*3);
lean_inc_ref(v_toTryThisSuggestion_3657_);
v___x_3660_ = l_Lean_Meta_Tactic_TryThis_Suggestion_processEdit(v_toTryThisSuggestion_3657_, v_val_3656_, v___y_3355_, v___y_3356_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3661_; lean_object* v_range_3662_; lean_object* v_newText_3663_; lean_object* v___x_3664_; 
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
lean_inc(v_a_3661_);
lean_dec_ref_known(v___x_3660_, 1);
v_range_3662_ = lean_ctor_get(v_a_3661_, 0);
lean_inc_ref(v_range_3662_);
v_newText_3663_ = lean_ctor_get(v_a_3661_, 1);
lean_inc_ref(v_newText_3663_);
v___x_3664_ = l_Lean_Syntax_getRange_x3f(v_ref_3350_, v___x_3654_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_inc(v_previewSpan_x3f_3658_);
lean_inc(v_val_3656_);
lean_inc_ref(v_toTryThisSuggestion_3657_);
v___y_3635_ = v_range_3662_;
v___y_3636_ = v_toTryThisSuggestion_3657_;
v___y_3637_ = v_newText_3663_;
v___y_3638_ = v_diffGranularity_3659_;
v___y_3639_ = v_val_3656_;
v___y_3640_ = v___x_3654_;
v___y_3641_ = v_a_3661_;
v___y_3642_ = v_previewSpan_x3f_3658_;
v___y_3643_ = v_val_3656_;
goto v___jp_3634_;
}
else
{
lean_object* v_val_3665_; 
v_val_3665_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_val_3665_);
lean_dec_ref_known(v___x_3664_, 1);
lean_inc(v_previewSpan_x3f_3658_);
lean_inc_ref(v_toTryThisSuggestion_3657_);
v___y_3635_ = v_range_3662_;
v___y_3636_ = v_toTryThisSuggestion_3657_;
v___y_3637_ = v_newText_3663_;
v___y_3638_ = v_diffGranularity_3659_;
v___y_3639_ = v_val_3656_;
v___y_3640_ = v___x_3654_;
v___y_3641_ = v_a_3661_;
v___y_3642_ = v_previewSpan_x3f_3658_;
v___y_3643_ = v_val_3665_;
goto v___jp_3634_;
}
}
else
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3673_; 
lean_dec(v_val_3656_);
lean_dec_ref(v_b_3354_);
lean_dec(v_ref_3350_);
lean_dec(v_codeActionPrefix_x3f_3349_);
v_a_3666_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3673_ == 0)
{
v___x_3668_ = v___x_3660_;
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3660_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3671_; 
if (v_isShared_3669_ == 0)
{
v___x_3671_ = v___x_3668_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v_a_3666_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
}
else
{
lean_dec(v___x_3655_);
v_a_3359_ = v_b_3354_;
goto v___jp_3358_;
}
}
}
v___jp_3358_:
{
size_t v___x_3360_; size_t v___x_3361_; 
v___x_3360_ = ((size_t)1ULL);
v___x_3361_ = lean_usize_add(v_i_3353_, v___x_3360_);
v_i_3353_ = v___x_3361_;
v_b_3354_ = v_a_3359_;
goto _start;
}
v___jp_3363_:
{
lean_object* v___x_3365_; lean_object* v___x_3366_; 
v___x_3365_ = l_Lean_MessageData_nestD(v___y_3364_);
v___x_3366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3366_, 0, v_b_3354_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
v_a_3359_ = v___x_3366_;
goto v___jp_3358_;
}
v___jp_3367_:
{
lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v___x_3371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___y_3368_);
lean_ctor_set(v___x_3371_, 1, v___y_3370_);
v___x_3372_ = l_Lean_stringToMessageData(v___y_3369_);
v___x_3373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3371_);
lean_ctor_set(v___x_3373_, 1, v___x_3372_);
v___y_3364_ = v___x_3373_;
goto v___jp_3363_;
}
v___jp_3374_:
{
lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3376_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3377_ = lean_unsigned_to_nat(2u);
v___x_3378_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__3);
v___x_3379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3379_, 0, v___x_3378_);
lean_ctor_set(v___x_3379_, 1, v___y_3375_);
v___x_3380_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3377_);
lean_ctor_set(v___x_3380_, 1, v___x_3379_);
v___x_3381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3376_);
lean_ctor_set(v___x_3381_, 1, v___x_3380_);
v___y_3364_ = v___x_3381_;
goto v___jp_3363_;
}
v___jp_3382_:
{
lean_object* v___x_3387_; uint64_t v_javascriptHash_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; uint8_t v___x_3400_; 
v___x_3387_ = ((lean_object*)(l_Lean_Meta_Hint_tryThisDiffWidget));
v_javascriptHash_3388_ = lean_ctor_get_uint64(v___x_3387_, sizeof(void*)*1);
v___x_3389_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__8));
v___x_3390_ = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(v___x_3390_, 0, v___x_3389_);
lean_ctor_set(v___x_3390_, 1, v___y_3385_);
lean_ctor_set_uint64(v___x_3390_, sizeof(void*)*2, v_javascriptHash_3388_);
v___x_3391_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3391_, 0, v___y_3386_);
v___x_3392_ = l_Lean_MessageData_ofFormat(v___x_3391_);
v___x_3393_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3390_);
lean_ctor_set(v___x_3393_, 1, v___x_3392_);
v___x_3394_ = l_Lean_stringToMessageData(v___y_3384_);
v___x_3395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3394_);
lean_ctor_set(v___x_3395_, 1, v___x_3393_);
v___x_3396_ = l_Lean_stringToMessageData(v___y_3383_);
v___x_3397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3397_, 0, v___x_3395_);
lean_ctor_set(v___x_3397_, 1, v___x_3396_);
v___x_3398_ = lean_array_get_size(v_suggestions_3347_);
v___x_3399_ = lean_unsigned_to_nat(1u);
v___x_3400_ = lean_nat_dec_eq(v___x_3398_, v___x_3399_);
if (v___x_3400_ == 0)
{
v___y_3375_ = v___x_3397_;
goto v___jp_3374_;
}
else
{
if (v_forceList_3348_ == 0)
{
lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3401_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___closed__1);
v___x_3402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3402_, 0, v___x_3401_);
lean_ctor_set(v___x_3402_, 1, v___x_3397_);
v___y_3364_ = v___x_3402_;
goto v___jp_3363_;
}
else
{
v___y_3375_ = v___x_3397_;
goto v___jp_3374_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_suggestions_3347_ = stack[0].m_obj;
uint8_t v_forceList_3348_ = stack[1].m_num;
lean_object* v_codeActionPrefix_x3f_3349_ = stack[2].m_obj;
lean_object* v_ref_3350_ = stack[3].m_obj;
lean_object* v_as_3351_ = stack[4].m_obj;
size_t v_sz_3352_ = stack[5].m_num;
size_t v_i_3353_ = stack[6].m_num;
lean_object* v_b_3354_ = stack[7].m_obj;
lean_object* v___y_3355_ = stack[8].m_obj;
lean_object* v___y_3356_ = stack[9].m_obj;
lean_object* v_res_3675_;
v_res_3675_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3347_, v_forceList_3348_, v_codeActionPrefix_x3f_3349_, v_ref_3350_, v_as_3351_, v_sz_3352_, v_i_3353_, v_b_3354_, v___y_3355_, v___y_3356_);
stack->m_obj
 = v_res_3675_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2___boxed(lean_object* v_suggestions_3676_, lean_object* v_forceList_3677_, lean_object* v_codeActionPrefix_x3f_3678_, lean_object* v_ref_3679_, lean_object* v_as_3680_, lean_object* v_sz_3681_, lean_object* v_i_3682_, lean_object* v_b_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_){
_start:
{
uint8_t v_forceList_boxed_3687_; size_t v_sz_boxed_3688_; size_t v_i_boxed_3689_; lean_object* v_res_3690_; 
v_forceList_boxed_3687_ = lean_unbox(v_forceList_3677_);
v_sz_boxed_3688_ = lean_unbox_usize(v_sz_3681_);
lean_dec(v_sz_3681_);
v_i_boxed_3689_ = lean_unbox_usize(v_i_3682_);
lean_dec(v_i_3682_);
v_res_3690_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3676_, v_forceList_boxed_3687_, v_codeActionPrefix_x3f_3678_, v_ref_3679_, v_as_3680_, v_sz_boxed_3688_, v_i_boxed_3689_, v_b_3683_, v___y_3684_, v___y_3685_);
lean_dec(v___y_3685_);
lean_dec_ref(v___y_3684_);
lean_dec_ref(v_as_3680_);
lean_dec_ref(v_suggestions_3676_);
return v_res_3690_;
}
}
static lean_object* _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0(void){
_start:
{
lean_object* v___x_3691_; lean_object* v_msg_3692_; 
v___x_3691_ = ((lean_object*)(l___private_Lean_Meta_Hint_0__Lean_Meta_Hint_mkDiffString___closed__0));
v_msg_3692_ = l_Lean_stringToMessageData(v___x_3691_);
return v_msg_3692_;
}
}
lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage(lean_object* v_suggestions_3693_, lean_object* v_ref_3694_, lean_object* v_codeActionPrefix_x3f_3695_, uint8_t v_forceList_3696_, lean_object* v_a_3697_, lean_object* v_a_3698_){
_start:
{
lean_object* v_msg_3700_; size_t v_sz_3701_; size_t v___x_3702_; lean_object* v___x_3703_; 
v_msg_3700_ = lean_obj_once(&l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0, &l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0_once, _init_l_Lean_Meta_Hint_mkSuggestionsMessage___closed__0);
v_sz_3701_ = lean_array_size(v_suggestions_3693_);
v___x_3702_ = ((size_t)0ULL);
v___x_3703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__2(v_suggestions_3693_, v_forceList_3696_, v_codeActionPrefix_x3f_3695_, v_ref_3694_, v_suggestions_3693_, v_sz_3701_, v___x_3702_, v_msg_3700_, v_a_3697_, v_a_3698_);
return v___x_3703_;
}
}
LEAN_EXPORT void l_Lean_Meta_Hint_mkSuggestionsMessage_0interp(lean_interpreter_value* stack)
{
lean_object* v_suggestions_3693_ = stack[0].m_obj;
lean_object* v_ref_3694_ = stack[1].m_obj;
lean_object* v_codeActionPrefix_x3f_3695_ = stack[2].m_obj;
uint8_t v_forceList_3696_ = stack[3].m_num;
lean_object* v_a_3697_ = stack[4].m_obj;
lean_object* v_a_3698_ = stack[5].m_obj;
lean_object* v_res_3704_;
v_res_3704_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3693_, v_ref_3694_, v_codeActionPrefix_x3f_3695_, v_forceList_3696_, v_a_3697_, v_a_3698_);
stack->m_obj
 = v_res_3704_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Hint_mkSuggestionsMessage___boxed(lean_object* v_suggestions_3705_, lean_object* v_ref_3706_, lean_object* v_codeActionPrefix_x3f_3707_, lean_object* v_forceList_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_){
_start:
{
uint8_t v_forceList_boxed_3712_; lean_object* v_res_3713_; 
v_forceList_boxed_3712_ = lean_unbox(v_forceList_3708_);
v_res_3713_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3705_, v_ref_3706_, v_codeActionPrefix_x3f_3707_, v_forceList_boxed_3712_, v_a_3709_, v_a_3710_);
lean_dec(v_a_3710_);
lean_dec_ref(v_a_3709_);
lean_dec_ref(v_suggestions_3705_);
return v_res_3713_;
}
}
lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(lean_object* v_t_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
lean_object* v___x_3718_; 
v___x_3718_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___redArg(v_t_3714_, v___y_3716_);
return v___x_3718_;
}
}
LEAN_EXPORT void l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_3714_ = stack[0].m_obj;
lean_object* v___y_3715_ = stack[1].m_obj;
lean_object* v___y_3716_ = stack[2].m_obj;
lean_object* v_res_3719_;
v_res_3719_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(v_t_3714_, v___y_3715_, v___y_3716_);
stack->m_obj
 = v_res_3719_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1___boxed(lean_object* v_t_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
lean_object* v_res_3724_; 
v_res_3724_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Meta_Hint_mkSuggestionsMessage_spec__1_spec__1(v_t_3720_, v___y_3721_, v___y_3722_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
return v_res_3724_;
}
}
static lean_object* _init_l_Lean_MessageData_hint___closed__3(void){
_start:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3729_ = ((lean_object*)(l_Lean_MessageData_hint___closed__2));
v___x_3730_ = l_Lean_stringToMessageData(v___x_3729_);
return v___x_3730_;
}
}
lean_object* l_Lean_MessageData_hint(lean_object* v_hint_3731_, lean_object* v_suggestions_3732_, lean_object* v_ref_x3f_3733_, lean_object* v_codeActionPrefix_x3f_3734_, uint8_t v_forceList_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_){
_start:
{
lean_object* v___y_3740_; 
if (lean_obj_tag(v_ref_x3f_3733_) == 0)
{
lean_object* v_ref_3755_; 
v_ref_3755_ = lean_ctor_get(v_a_3736_, 2);
lean_inc(v_ref_3755_);
v___y_3740_ = v_ref_3755_;
goto v___jp_3739_;
}
else
{
lean_object* v_val_3756_; 
v_val_3756_ = lean_ctor_get(v_ref_x3f_3733_, 0);
lean_inc(v_val_3756_);
lean_dec_ref_known(v_ref_x3f_3733_, 1);
v___y_3740_ = v_val_3756_;
goto v___jp_3739_;
}
v___jp_3739_:
{
lean_object* v___x_3741_; 
v___x_3741_ = l_Lean_Meta_Hint_mkSuggestionsMessage(v_suggestions_3732_, v___y_3740_, v_codeActionPrefix_x3f_3734_, v_forceList_3735_, v_a_3736_, v_a_3737_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3754_; 
v_a_3742_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3744_ = v___x_3741_;
v_isShared_3745_ = v_isSharedCheck_3754_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3741_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3754_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3752_; 
v___x_3746_ = ((lean_object*)(l_Lean_MessageData_hint___closed__1));
v___x_3747_ = lean_obj_once(&l_Lean_MessageData_hint___closed__3, &l_Lean_MessageData_hint___closed__3_once, _init_l_Lean_MessageData_hint___closed__3);
v___x_3748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3748_, 0, v___x_3747_);
lean_ctor_set(v___x_3748_, 1, v_hint_3731_);
v___x_3749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
lean_ctor_set(v___x_3749_, 1, v_a_3742_);
v___x_3750_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3746_);
lean_ctor_set(v___x_3750_, 1, v___x_3749_);
if (v_isShared_3745_ == 0)
{
lean_ctor_set(v___x_3744_, 0, v___x_3750_);
v___x_3752_ = v___x_3744_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3750_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
else
{
lean_dec_ref(v_hint_3731_);
return v___x_3741_;
}
}
}
}
LEAN_EXPORT void l_Lean_MessageData_hint_0interp(lean_interpreter_value* stack)
{
lean_object* v_hint_3731_ = stack[0].m_obj;
lean_object* v_suggestions_3732_ = stack[1].m_obj;
lean_object* v_ref_x3f_3733_ = stack[2].m_obj;
lean_object* v_codeActionPrefix_x3f_3734_ = stack[3].m_obj;
uint8_t v_forceList_3735_ = stack[4].m_num;
lean_object* v_a_3736_ = stack[5].m_obj;
lean_object* v_a_3737_ = stack[6].m_obj;
lean_object* v_res_3757_;
v_res_3757_ = l_Lean_MessageData_hint(v_hint_3731_, v_suggestions_3732_, v_ref_x3f_3733_, v_codeActionPrefix_x3f_3734_, v_forceList_3735_, v_a_3736_, v_a_3737_);
stack->m_obj
 = v_res_3757_;
}
LEAN_EXPORT lean_object* l_Lean_MessageData_hint___boxed(lean_object* v_hint_3758_, lean_object* v_suggestions_3759_, lean_object* v_ref_x3f_3760_, lean_object* v_codeActionPrefix_x3f_3761_, lean_object* v_forceList_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_){
_start:
{
uint8_t v_forceList_boxed_3766_; lean_object* v_res_3767_; 
v_forceList_boxed_3766_ = lean_unbox(v_forceList_3762_);
v_res_3767_ = l_Lean_MessageData_hint(v_hint_3758_, v_suggestions_3759_, v_ref_x3f_3760_, v_codeActionPrefix_x3f_3761_, v_forceList_boxed_3766_, v_a_3763_, v_a_3764_);
lean_dec(v_a_3764_);
lean_dec_ref(v_a_3763_);
lean_dec_ref(v_suggestions_3759_);
return v_res_3767_;
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
